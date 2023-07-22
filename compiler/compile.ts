import acorn from "acorn";
import * as ESTree from "estree";

type PrimitiveType = "int8" | "int16" | "int32" | "int64";

interface ArrayDeclaration {
  itemTypes: PrimitiveType[];
  length: number;
}

interface Environment {
  arrays: Record<string, ArrayDeclaration>;
}

interface Variable {
  type: string;
}

type Instruction =
  | { type: "get"; name: string }
  | { type: "set"; name: string; value: string | number }
  | { type: "store"; name: string; index: number; tuples: (string | number)[] }
  | { type: "retrieve"; name: string; index: number }
  | {
      type: "range";
      name: string;
      loopVariable: string;
      loopBody: Instruction[];
    }
  | { type: "operation"; operator: string; operands: (string | Instruction)[] };

class ParseError extends Error {
  constructor(...args: string[] | undefined[]) {
    super(...args);
    this.name = "ParseError";
  }
}

interface Procedure {
  name: string;
  variables: Record<string, Variable>;
  body: Instruction[];
}

class CoqCPAST {
  environment: Environment | null = null;
  procedures: Procedure[] = [];
}

class CoqCPASTTransformer {
  ast: acorn.ExtendNode<ESTree.Program>;
  result: CoqCPAST;

  constructor(code: string) {
    this.ast = acorn.parse(code, { sourceType: "module", ecmaVersion: 2023 });
    this.result = new CoqCPAST();
  }

  transform() {
    let seenEnvironmentBlock = false;
    for (const node of this.ast.body) {
      if (
        node.type !== "ExpressionStatement" ||
        node.expression.type !== "CallExpression" ||
        node.expression.callee.type !== "Identifier" ||
        (node.expression.callee.name !== "environment" &&
          node.expression.callee.name !== "procedure")
      ) {
        throw new ParseError(
          'only "environment" and "procedure" expressions allowed. range: ' +
            node.start +
            " to " +
            node.end
        );
      }

      if (node.expression.callee.name === "environment") {
        if (seenEnvironmentBlock) {
          throw new ParseError(
            "duplicate environment block. range: " +
              node.start +
              " to " +
              node.end
          );
        }
        seenEnvironmentBlock = true;

        if (node.expression.arguments.length !== 1) {
          throw new ParseError(
            "environment block accepts exactly 1 argument. range: " +
              node.start +
              " to " +
              node.end
          );
        }

        const argumentNode = node.expression.arguments[0];
        if (argumentNode.type !== "ObjectExpression") {
          throw new ParseError(
            "the argument must be an object. range: " +
              argumentNode.start +
              " to " +
              argumentNode.end
          );
        }

        for (const property of argumentNode.properties) {
          if (property.type === "SpreadElement") {
            throw new ParseError(
              "spread syntax isn't recognized. range: " +
                property.start +
                " to " +
                property.end
            );
          }

          if (property.key.type !== "Identifier") {
            throw new ParseError(
              "unrecognized key type. range: " +
                property.key.start +
                " to " +
                property.key.end
            );
          }

          const arrayDescription = property.value;
          if (
            arrayDescription.type !== "CallExpression" ||
            arrayDescription.callee.type !== "Identifier" ||
            arrayDescription.callee.name !== "array"
          ) {
            throw new ParseError(
              "expecting an array expression. range: " +
                arrayDescription.start +
                " to " +
                arrayDescription.end
            );
          }

          if (arrayDescription.arguments.length !== 2) {
            throw new ParseError(
              "array() accepts exactly two arguments. range: " +
                arrayDescription.start +
                " to " +
                arrayDescription.end
            );
          }
          
          const typesArrayNode = arrayDescription.arguments[0];
          const lengthNode = arrayDescription.arguments[1];
          
          if (typesArrayNode.type !== "ArrayExpression") {
            throw new ParseError(
              "First argument of array() must be an array. range: " +
                typesArrayNode.start +
                " to " +
                typesArrayNode.end
            );
          }
          
          if (lengthNode.type !== "Literal" || typeof lengthNode.value !== 'number') {
            throw new ParseError(
              "Second argument of array() must be a numeric literal. range: " +
                lengthNode.start +
                " to " +
                lengthNode.end
            );
          }
          
          let itemTypes: PrimitiveType[] = [];
          for (const itemType of typesArrayNode.elements) {
            if (
              itemType === null ||
              itemType.type !== "Identifier" ||
              (itemType.name !== "int8" &&
                itemType.name !== "int16" &&
                itemType.name !== "int32" &&
                itemType.name !== "int64")
            ) {
              throw new ParseError(
                "Invalid array item type. range: " +
                  typesArrayNode.start +
                  " to " +
                  typesArrayNode.end
              );
            }
            
            itemTypes.push(itemType.name);
          }
          
          if (!this.result.environment) {
            this.result.environment = { arrays: {} };
          }
          this.result.environment.arrays[property.key.name] = { itemTypes, length: lengthNode.value };
        }
      }

      if (node.expression.callee.name === "procedure") {
        // that's tomorrow's task
      }
    }
    return this.result;
  }
}

const code = `environment({
    fibSeq: array([int32], 100),  // Memory to hold Fibonacci sequence up to the 100th term
    anotherArray: array([int8, int64], 3) // Example of an array where each element can hold multiple values
});

procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
    set("n", readInt32());  // Reading the term 'n' to which Fibonacci sequence is to be calculated
    set("a", 0);
    set("b", 1);
    
    // Initialize first two numbers in fibonacci series
    store("fibSeq", 0, [get("a")]);
    store("fibSeq", 1, [get("b")]);

    range(get("n") - 2, x => {  
        let index = x + 2;  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", index, [get("i")]);  // Storing the newly calculated fibonacci term
    })
});`;
const transformer = new CoqCPASTTransformer(code);
console.log(JSON.stringify(transformer.transform(), null, 4));
