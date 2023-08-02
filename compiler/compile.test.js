import { CoqCPASTTransformer, ParseError } from "./compile"

describe("CoqCPASTTransformer", () => {
  it("should parse valid code correctly", () => {
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

  it("should throw an error for invalid code", () => {
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

  it("should parse valid code and produce correct structure", () => {
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
      lengthNodeLocation: expect.any(Object)
    })

    expect(result.procedures).toHaveLength(1)
    expect(result.procedures[0].name).toEqual('fibonacci')
    expect(result.procedures[0].variables).toHaveProperty('n')
    expect(result.procedures[0].body).toHaveLength(1)
    expect(result.procedures[0].body[0].type).toEqual('set')
    expect(result.procedures[0].body[0].name).toEqual('n')
    expect(result.procedures[0].body[0].value).toEqual({
      type: 'readInt8',
      location: expect.any(Object)
    })
  })

  it("throws ParseError when there are duplicate environment blocks", () => {
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
  
  it("throws ParseError when environment block has incorrect syntax", () => {
    const code = `environment(10);
    
    procedure("fibonacci", { n: int32 }, () => {
        set("n", readInt8());
    });`

    const transformer = new CoqCPASTTransformer(code)

    expect(() => transformer.transform()).toThrow(
      expect.objectContaining({ name: 'ParseError' })
    )
  })
})