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
    expect(() => transformer.transform()).toThrow(ParseError)
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

    expect(() => transformer.transform()).toThrow(
      expect.objectContaining({ name: 'ParseError' })
    )
  })

  it('throws ParseError when environment block has incorrect syntax', () => {
    const code = `environment(10);
    
    procedure("fibonacci", { n: int32 }, () => {
        set("n", readInt8());
    });`

    const transformer = new CoqCPASTTransformer(code)

    expect(() => transformer.transform()).toThrow(
      expect.objectContaining({ name: 'ParseError' })
    )
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

      expect(() => {
        const transformer = new CoqCPASTTransformer(codeWithFaultyRange)
        transformer.transform()
      }).toThrow(/^range\(\) function accepts exactly 2 arguments,/)
    })
  })
})
