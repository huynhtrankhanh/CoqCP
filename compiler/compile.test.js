import { CoqCPASTTransformer, ParseError } from './compile'

describe('CoqCPASTTransformer', () => {
  it('should parse valid code correctly', () => {
    const code = `environment({
        fibSeq: array([int32], 100),  
        anotherArray: array([int8, int64], 3)
    });
  
    procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
        set("n", readInt8());  
        set("a", 0);
        set("b", 1);

        store("fibSeq", 0, [get("a")]);
        store("fibSeq", 1, [get("b")]);
  
        range(get("n") - 2, x => {  
            set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);
            store("fibSeq", x + 2, [get("i")]);  
        })

        if (get("n") == 100) {
          writeInt8(32);
        } else {writeInt8(64);}
  
        if (less(get("n"), 200)) {
          writeInt8(100);
        }
    });`

    const transformer = new CoqCPASTTransformer(code)
    expect(() => transformer.transform()).not.toThrowError()
  })

  it('should throw an error for invalid code', () => {
    const invalidCode = `environment({
        fibSeq: array([int32], 100),
        anotherArray: array([int8, int64], 3)
    });

    procedure(100, { n: int32, a: int32, b: int32, i: int32 }, () => {
        set("n", readInt8());  
        set("a", 0);
        set("b", 1);

        store("fibSeq", 0, [get("a")]);
        store("fibSeq", 1, [get("b")]);
  
        range(get("n") - 2, x => {  
            set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  
            store("fibSeq", x + 2, [get("i")]);  
        })

        if (get("n") == 100) {
          writeInt8(32);
        } else {writeInt8(64);}

        if (less(get("n"), 200)) {
          writeInt8(100);
        }
    });`

    const transformer = new CoqCPASTTransformer(invalidCode)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(
        /^first argument of procedure\(\) must be a string literal\./
      )
    }
  })

  it('should parse valid code and produce correct structure', () => {
    const code = `environment({
        fibSeq: array([int32], 100)
    });

    procedure("fibonacci", { n: int32 }, () => {
        set("n", readInt8());
    });`

    const transformer = new CoqCPASTTransformer(code)
    const result = transformer.transform()

    expect(result.environment).toBeDefined()
    expect(result.environment?.arrays).toHaveProperty('fibSeq')
    expect(result.environment?.arrays['fibSeq']).toEqual({
      itemTypes: ['int32'],
      length: 100,
      lengthNodeLocation: expect.any(Object),
    })

    expect(result.procedures).toHaveLength(1)
    expect(result.procedures[0].name).toEqual('fibonacci')
    expect(result.procedures[0].variables).toHaveProperty('n')
    expect(result.procedures[0].body).toHaveLength(1)
    expect(result.procedures[0].body[0].type).toEqual('set')
    expect(result.procedures[0].body[0].name).toEqual('n')
    expect(result.procedures[0].body[0].value).toEqual({
      type: 'readInt8',
      location: expect.any(Object),
    })
  })

  it('throws ParseError when there are duplicate environment blocks', () => {
    const code = `environment({
        fibSeq: array([int32], 100)
    });

    environment({
        anotherArray: array([int8, int64], 3)
    });
    
    procedure("fibonacci", { n: int32 }, () => {
        set("n", readInt8());
    });`

    const transformer = new CoqCPASTTransformer(code)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(/^duplicate environment block/)
    }
  })

  it('throws ParseError when environment block has incorrect syntax', () => {
    const code = `environment(10);
    
    procedure("fibonacci", { n: int32 }, () => {
        set("n", readInt8());
    });`

    const transformer = new CoqCPASTTransformer(code)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(/^the argument must be an object/)
    }
  })

  it('should parse sDivide instruction correctly', () => {
    const program = `
    procedure("exampleProcedure", { a: int32, b: int32 }, () => {      
        sDivide(get("a"), get("b"));
    });`

    const transformer = new CoqCPASTTransformer(program)
    const result = transformer.transform()

    expect(result.procedures[0].body[0]).toMatchObject({
      type: 'sDivide',
      left: { type: 'get', name: 'a' },
      right: { type: 'get', name: 'b' },
    })
  })

  it('should parse readInt8 instruction correctly', () => {
    const program = `
    procedure("exampleProcedure", { }, () => {      
        readInt8();
    });`

    const transformer = new CoqCPASTTransformer(program)
    const result = transformer.transform()

    expect(result.procedures[0].body[0]).toMatchObject({
      type: 'readInt8',
    })
  })

  it('should handle simple if condition correctly', () => {
    const program = `
    procedure("exampleProcedure", { a: int32 }, () => {
      if(get("a") == 10) {
        get("a");
      }
    });`

    const transformer = new CoqCPASTTransformer(program)
    const result = transformer.transform()

    expect(result.procedures[0].body[0]).toMatchObject({
      type: 'condition',
      condition: {
        type: 'binaryOp',
        operator: 'equal',
        left: { type: 'get', name: 'a' },
        right: { type: 'literal', value: 10 },
      },
      body: [{ type: 'get', name: 'a' }],
      alternate: [],
    })
  })

  describe('range() instruction', () => {
    it('should create a range instruction with proper attributes', () => {
      const code = `environment({
            loopExample: array([int32], 10)
        });

        procedure("loopExampleProcedure", { i: int32 }, () => {
            range(10, x => {  
                store("loopExample", x, [x]);  
            })
        });`

      const transformer = new CoqCPASTTransformer(code)
      const result = transformer.transform()

      const expectedInstruction = {
        type: 'range',
        name: 'x',
        end: { type: 'literal', value: 10, location: expect.any(Object) },
        loopVariable: 'x',
        loopBody: [
          {
            type: 'store',
            name: 'loopExample',
            index: {
              type: 'local binder',
              name: 'x',
              location: expect.any(Object),
            },
            tuples: [
              { type: 'local binder', name: 'x', location: expect.any(Object) },
            ],
            location: expect.any(Object),
          },
        ],
        location: expect.any(Object),
      }

      const procBody = result.procedures[0].body

      expect(procBody[0]).toEqual(expectedInstruction)
    })

    it('should throw an error if "range" function does not have two arguments', () => {
      const codeWithFaultyRange = `
            environment({ myArray: array([int32], 10) });
            procedure("myProcedure", { i: int32 }, () => {
                range(10);})`

      const transformer = new CoqCPASTTransformer(codeWithFaultyRange)

      expect.assertions(3)

      try {
        transformer.transform()
      } catch (error) {
        expect(error).toBeInstanceOf(ParseError)
        expect(error).toHaveProperty('message')
        expect(error.message).toMatch(
          /^range\(\) function accepts exactly 2 arguments,/
        )
      }
    })
  })

  test('Error: If expression without {}', async () => {
    const code = `
      environment({
        testArray: array([int32], 100)
      });
  
      procedure("test", { x: int32 }, () => {
        if (less(get("x"), 10))
          writeInt8(32);
        else
          writeInt8(64);
      });
    `

    const transformer = new CoqCPASTTransformer(code)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(/^must be a block statement/)
    }
  })

  describe('If instruction parsing', () => {
    test('Happy path', async () => {
      const code = `
        environment({
          testArray: array([int32], 100)
        });
  
        procedure("test", { x: int32 }, () => {
          if (less(get("x"), 10)) {
            writeInt8(32);
          } else {
            writeInt8(64);
          }
        });
      `

      const transformer = new CoqCPASTTransformer(code)
      const transformedAST = transformer.transform()

      expect(transformedAST.procedures.length).toBe(1)

      const procedure = transformedAST.procedures[0]

      expect(procedure.body[0].type).toBe('condition')
      expect(procedure.body[0].condition.type).toBe('less')
      expect(procedure.body[0].condition.left.type).toBe('get')
      expect(procedure.body[0].condition.left.name).toBe('x')
      expect(procedure.body[0].condition.right.value).toBe(10)
      expect(procedure.body[0].body.length).toBe(1)
      expect(procedure.body[0].alternate.length).toBe(1)
    })

    test('Error: Condition not supplied', async () => {
      const code = `
        environment({
          testArray: array([int32], 100)
        });
  
        procedure("test", { x: int32 }, () => {
          if () {
            writeInt8(32);
          }
        });
      `

      expect.assertions(3)

      try {
        const transformer = new CoqCPASTTransformer(code)
        transformer.transform()
      } catch (error) {
        expect(error).toBeInstanceOf(SyntaxError)
        expect(error).toHaveProperty('message')
        expect(error.message).toMatch(/^Unexpected token/)
      }
    })

    test('Error: Invalid condition type', async () => {
      const code = `
        environment({
          testArray: array([int32], 100)
        });
  
        procedure("test", { x: int32 }, () => {
          if(fetchData()) {
            writeInt8(32);
          }
        });
      `

      const transformer = new CoqCPASTTransformer(code)

      expect.assertions(3)

      try {
        transformer.transform()
      } catch (error) {
        expect(error).toBeInstanceOf(ParseError)
        expect(error).toHaveProperty('message')
        expect(error.message).toMatch(/^unknown instruction/)
      }
    })
  })

  test('Reject duplicate identifiers in the environment block', () => {
    const sourceCode = `
      environment({
        a: array([int8], 4),
        a: array([int16], 5),
      })
  
      procedure("example", {}, () => [])
    `

    const transformer = new CoqCPASTTransformer(sourceCode)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(
        /^duplicate identifier in environment block\./
      )
    }
  })

  test('illegal procedure block', () => {
    const sourceCode = `
      environment({
        a: array([int8], 4),
      })
  
      procedure("example", {x: int16, x: int8}, () => [])
    `

    const transformer = new CoqCPASTTransformer(sourceCode)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(
        /^third argument of procedure\(\) must be an arrow function expression\./
      )
    }
  })

  test('Reject duplicate identifiers in procedure variables', () => {
    const sourceCode = `
      environment({
        a: array([int8], 4),
      })
  
      procedure("example", {x: int16, x: int8}, () => {})
    `

    const transformer = new CoqCPASTTransformer(sourceCode)

    expect.assertions(3)

    try {
      transformer.transform()
    } catch (error) {
      expect(error).toBeInstanceOf(ParseError)
      expect(error).toHaveProperty('message')
      expect(error.message).toMatch(
        /^duplicate identifier in procedure variables\./
      )
    }
  })
})
