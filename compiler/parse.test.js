import { CoqCPASTTransformer, ParseError } from './parse'

describe('CoqCPASTTransformer', () => {
  it('should parse valid code correctly', () => {
    const code = `environment({
        fibSeq: array([int32], 100),  
        anotherArray: array([int8, int64], 3)
    });
  
    procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
        set("n", readChar());  
        set("a", 0);
        set("b", 1);

        store("fibSeq", 0, [get("a")]);
        store("fibSeq", 1, [get("b")]);
  
        range(get("n") - 2, x => {  
            set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);
            store("fibSeq", x + 2, [get("i")]);  
        })

        if (get("n") == 100) {
          writeChar(32);
        } else {writeChar(64);}
  
        if (less(get("n"), 200)) {
          writeChar(100);
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
        set("n", readChar());  
        set("a", 0);
        set("b", 1);

        store("fibSeq", 0, [get("a")]);
        store("fibSeq", 1, [get("b")]);
  
        range(get("n") - 2, x => {  
            set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  
            store("fibSeq", x + 2, [get("i")]);  
        })

        if (get("n") == 100) {
          writeChar(32);
        } else {writeChar(64);}

        if (less(get("n"), 200)) {
          writeChar(100);
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
        set("n", readChar());
    });`

    const transformer = new CoqCPASTTransformer(code)
    const result = transformer.transform()

    expect(result.environment).toBeDefined()
    expect(result.environment?.arrays.has('fibSeq')).toEqual(true)
    expect(result.environment?.arrays.get('fibSeq')).toEqual({
      itemTypes: ['int32'],
      length: {
        type: 'literal',
        valueType: 'number',
        raw: '100',
        location: expect.any(Object),
      },
    })

    expect(result.procedures).toHaveLength(1)
    expect(result.procedures[0].name).toEqual('fibonacci')
    expect(result.procedures[0].variables.has('n')).toEqual(true)
    expect(result.procedures[0].body).toHaveLength(1)
    expect(result.procedures[0].body[0].type).toEqual('set')
    expect(result.procedures[0].body[0].name).toEqual('n')
    expect(result.procedures[0].body[0].value).toEqual({
      type: 'readChar',
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
        set("n", readChar());
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
        set("n", readChar());
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

  it('should parse readChar instruction correctly', () => {
    const program = `
    procedure("exampleProcedure", { }, () => {      
        readChar();
    });`

    const transformer = new CoqCPASTTransformer(program)
    const result = transformer.transform()

    expect(result.procedures[0].body[0]).toMatchObject({
      type: 'readChar',
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
        right: { type: 'literal', raw: '10', valueType: 'number' },
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
        end: {
          type: 'literal',
          raw: '10',
          valueType: 'number',
          location: expect.any(Object),
        },
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
            tuple: [
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
          writeChar(32);
        else
          writeChar(64);
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
            writeChar(32);
          } else {
            writeChar(64);
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
      expect(procedure.body[0].condition.right.raw).toBe('10')
      expect(procedure.body[0].condition.right.valueType).toBe('number')
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
            writeChar(32);
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
            writeChar(32);
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
  
      procedure("example", {x: int16}, () => [])
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

  it('parses the "call" instruction correctly', () => {
    const code = `
      environment({
          myArray: array([int8], 3)
      });

      procedure("myProcedure1", { x: int8 }, () => {
          call("myProcedure2", { x: 10 });
      });

      procedure("myProcedure2", { x: int8 }, () => {
          set("x", 8);
      });
    `

    const transformer = new CoqCPASTTransformer(code)
    const result = transformer.transform()

    const procedure1 = result.procedures[0]
    const procedure2 = result.procedures[1]

    expect(procedure1.body[0]).toMatchObject({
      type: 'call',
      procedure: 'myProcedure2',
    })
    expect(
      [...procedure1.body[0].presetVariables].reduce(
        (acc, [key, value]) => ((acc[key] = value), acc),
        {}
      )
    ).toEqual({
      x: {
        type: 'literal',
        valueType: 'number',
        raw: '10',
        location: expect.any(Object),
      },
    })

    expect(procedure2).toMatchObject({
      name: 'myProcedure2',
      body: [
        {
          type: 'set',
          name: 'x',
          value: {
            type: 'literal',
            valueType: 'number',
            raw: '8',
            location: expect.any(Object),
          },
          location: expect.any(Object),
        },
      ],
    })
    expect(
      [...procedure2.variables].reduce(
        (acc, [key, value]) => ((acc[key] = value), acc),
        {}
      )
    ).toEqual({ x: { type: 'int8' } })
  })

  describe('Call instruction parsing', () => {
    test('Happy path', async () => {
      const code = `
        environment({
          testArray: array([int32], 100)
        });
  
        procedure("exampleOne", { x: int32 }, () => {
          set("x", 1);
        });
  
        procedure("exampleTwo", { }, () => {
          call("exampleOne", { x: 100 });
        });
      `

      const transformer = new CoqCPASTTransformer(code)
      const transformedAST = transformer.transform()

      expect(transformedAST.procedures.length).toBe(2)

      const exampleTwoProcedure = transformedAST.procedures.find(
        (proc) => proc.name === 'exampleTwo'
      )
      expect(exampleTwoProcedure).toBeDefined()

      const callInstruction = exampleTwoProcedure?.body[0]

      expect(callInstruction).toMatchObject({
        type: 'call',
        procedure: 'exampleOne',
        location: expect.any(Object),
      })

      expect(
        [...callInstruction.presetVariables].reduce(
          (acc, [key, value]) => ((acc[key] = value), acc),
          {}
        )
      ).toEqual({
        x: {
          type: 'literal',
          raw: '100',
          valueType: 'number',
          location: expect.any(Object),
        },
      })
    })

    test('Reject duplicate identifiers in preset variables', () => {
      const sourceCode = `
        environment({
          a: array([int8], 4),
        })
    
        procedure("exampleOne", {x: int16}, () => { set("x", 1); })
  
        procedure("exampleTwo", { }, () => { 
          call("exampleOne", {x: 100, x: 200}); 
        })
      `

      const transformer = new CoqCPASTTransformer(sourceCode)

      expect.assertions(3)

      try {
        transformer.transform()
      } catch (error) {
        expect(error).toBeInstanceOf(ParseError)
        expect(error).toHaveProperty('message')
        expect(error.message).toMatch(
          /^duplicate identifier in preset variables\./
        )
      }
    })
  })

  describe('Parsing break, continue and flush statements', () => {
    const code = `
    environment({
      myArray: array([int32], 10)
    });

    procedure("testProcedure", { i: int32 }, () => {
      range(10, x => {
        if (x == 5) {
          "break";
        }
        if (x == 3) {
          "continue";
        }
        "flush";
      })
    });`

    it('parses the "break" statement correctly', () => {
      const transformer = new CoqCPASTTransformer(code)
      const result = transformer.transform()

      const instr = result.procedures[0].body[0].loopBody[0].body

      expect(instr[0]).toMatchObject({
        type: 'break',
        location: expect.any(Object),
      })
    })

    it('parses the "continue" statement correctly', () => {
      const transformer = new CoqCPASTTransformer(code)
      const result = transformer.transform()

      const instr = result.procedures[0].body[0].loopBody[1].body

      expect(instr[0]).toMatchObject({
        type: 'continue',
        location: expect.any(Object),
      })
    })

    it('parses the "flush" statement correctly', () => {
      const transformer = new CoqCPASTTransformer(code)
      const result = transformer.transform()

      const instr = result.procedures[0].body[0].loopBody[2]

      expect(instr).toMatchObject({
        type: 'flush',
        location: expect.any(Object),
      })
    })
  })
})
