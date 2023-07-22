import acorn, { ExtendNode } from "acorn";
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

type BinaryOp =
  | "add"
  | "subtract"
  | "multiply"
  | "divide"
  | "modulus"
  | "equal"
  | "noteq"
  | "less"
  | "greater"
  | "lesseq"
  | "greatereq";

interface BinaryOperationInstruction {
  type: "binaryOp";
  operator: BinaryOp;
  left: string | number | Instruction;
  right: string | number | Instruction;
}

type Instruction =
  | { type: "get"; name: string }
  | { type: "set"; name: string; value: string | number | Instruction }
  | {
      type: "store";
      name: string;
      index: number;
      tuples: (string | number | Instruction)[];
    }
  | { type: "retrieve"; name: string; index: number }
  | {
      type: "range";
      name: string;
      loopVariable: string;
      loopBody: Instruction[];
    }
  | { type: "operation"; operator: string; operands: (string | Instruction)[] }
  | { type: "readInt32" }
  | BinaryOperationInstruction
  | { type: "subscript"; value: Instruction; index: number };

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

          if (
            lengthNode.type !== "Literal" ||
            typeof lengthNode.value !== "number"
          ) {
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
          this.result.environment.arrays[property.key.name] = {
            itemTypes,
            length: lengthNode.value,
          };
        }
      }

      if (node.expression.callee.name === "procedure") {
        if (node.expression.callee.name === "procedure") {
          // Parsing the procedure block
          if (node.expression.arguments.length !== 3) {
            throw new ParseError(
              "procedure block accepts exactly 3 arguments. range: " +
                node.start +
                " to " +
                node.end
            );
          }

          const procedureNameNode = node.expression.arguments[0];
          const variableListNode = node.expression.arguments[1];
          const bodyNode = node.expression.arguments[2];

          if (
            procedureNameNode.type !== "Literal" ||
            typeof procedureNameNode.value !== "string"
          ) {
            throw new ParseError(
              "First argument of procedure() must be a string literal. range: " +
                procedureNameNode.start +
                " to " +
                procedureNameNode.end
            );
          }

          if (variableListNode.type !== "ObjectExpression") {
            throw new ParseError(
              "Second argument of procedure() must be an object. range: " +
                variableListNode.start +
                " to " +
                variableListNode.end
            );
          }

          // building the variables object
          let variables: Record<string, Variable> = {};
          for (const property of variableListNode.properties) {
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

            if (property.value.type !== "Identifier") {
              throw new ParseError(
                "unrecognized value type. range: " +
                  property.value.start +
                  " to " +
                  property.value.end
              );
            }

            variables[property.key.name] = { type: property.value.name };
          }

          // transforming bodyNode into Instruction[]
          if (
            bodyNode.type !== "ArrowFunctionExpression" ||
            bodyNode.body.type !== "BlockStatement"
          ) {
            throw new ParseError(
              "Third argument of procedure() must be an arrow function expression. range: " +
                bodyNode.start +
                " to " +
                bodyNode.end
            );
          }
          const body: Instruction[] = this.transformBodyNode(bodyNode.body);

          // adding the procedure to the result
          this.result.procedures.push({
            name: procedureNameNode.value,
            variables,
            body,
          });
        }
      }
    }
    return this.result;
  }

  private processNode(
    node: ExtendNode<ESTree.Node>
  ): Instruction | string | number {
    if (node.type === "CallExpression" && node.callee.type === "Identifier") {
      const name = node.callee.name;
      switch (name) {
        case "get":
        case "set":
        case "store":
        case "retrieve":
        case "range":
        case "readInt32":
          return this.processInstruction(
            name,
            node.arguments.map((x) => {
              if (x.type === "SpreadElement") {
                throw new Error("spread syntax not supported");
              }

              return x;
            })
          );
        default:
          throw new ParseError("Unknown function call: " + name);
      }
    } else if (node.type === "Identifier") {
      return node.name;
    } else if (node.type === "Literal" && typeof node.value === "number") {
      return node.value;
    } else if (node.type === "BinaryExpression") {
      return this.processBinaryExpression(node);
    } else if (node.type === "MemberExpression") {
      const instruction = this.processNode(node.object);
      if (node.property.type !== "Literal") {
        throw new ParseError("only literal indices allowed");
      }
      const index = node.property.raw;
    } else {
      throw new ParseError("Unrecognized node type: " + node.type);
    }
  }

  private processBinaryExpression(
    node: ExtendNode<ESTree.BinaryExpression>
  ): BinaryOperationInstruction {
    const operator = this.getBinaryOperator(node.operator);
    const left = this.processNode(node.left);
    const right = this.processNode(node.right);
    return { type: "binaryOp", operator, left, right };
  }

  private getBinaryOperator(operator: string): BinaryOp {
    switch (operator) {
      case "+":
        return "add";
      case "-":
        return "subtract";
      case "*":
        return "multiply";
      case "/":
        return "divide";
      case "%":
        return "modulus";
      case "==":
        return "equal";
      case "!=":
        return "noteq";
      case "<":
        return "less";
      case ">":
        return "greater";
      case "<=":
        return "lesseq";
      case ">=":
        return "greatereq";
      default:
        throw new ParseError("Invalid binary operator: " + operator);
    }
  }

  private processInstruction(
    name: string,
    args: ExtendNode<ESTree.Expression>[]
  ): Instruction {
    let instruction: Instruction;

    switch (name) {
      case "get": {
        if (
          args.length !== 1 ||
          args[0].type !== "Literal" ||
          typeof args[0].value !== "string"
        ) {
          throw new ParseError(
            "get() function accepts exactly 1 string argument"
          );
        }
        const varName = args[0].value;
        instruction = { type: "get", name: varName };
        break;
      }

      case "set": {
        if (
          args.length !== 2 ||
          args[0].type !== "Literal" ||
          typeof args[0].value !== "string"
        ) {
          throw new ParseError(
            "set() function accepts exactly 2 arguments, first one being a string"
          );
        }
        const varName = args[0].value;
        const value = this.processNode(args[1]);
        instruction = { type: "set", name: varName, value };
        break;
      }

      case "store": {
        if (
          args.length !== 3 ||
          args[0].type !== "Literal" ||
          typeof args[0].value !== "string" ||
          args[2].type !== "ArrayExpression"
        ) {
          throw new ParseError(
            "store() function accepts exactly 3 arguments, first one being a string and last one being an array"
          );
        }
        const arrayName = args[0].value;
        const index = this.processNode(args[1]) as number;
        const tuples = args[2].elements.map((node) => {
          if (node === null) {
            throw new Error("node can't be null");
          }
          if (node.type === "SpreadElement") {
            throw new Error("spread syntax not supported");
          }
          return this.processNode(node as ExtendNode<ESTree.Expression>);
        });
        instruction = { type: "store", name: arrayName, index, tuples };
        break;
      }

      case "retrieve": {
        if (
          args.length !== 2 ||
          args[0].type !== "Literal" ||
          typeof args[0].value !== "string"
        ) {
          throw new ParseError(
            "retrieve() function accepts exactly 2 arguments, first one being a string"
          );
        }
        const arrayName = args[0].value;
        const index = this.processNode(args[1]) as number;
        instruction = { type: "retrieve", name: arrayName, index };
        break;
      }

      case "range": {
        if (
          args.length !== 2 ||
          args[1].type !== "ArrowFunctionExpression" ||
          args[1].body.type !== "BlockStatement"
        ) {
          throw new ParseError(
            "range() function accepts exactly 2 arguments, second one being an arrow function"
          );
        }
        const end = this.processNode(args[0]) as number;
        const funcNode = args[1];

        if (funcNode.params.length !== 1) {
          throw new ParseError("arrow function must take exactly 1 argument");
        }

        const parameter = funcNode.params[0];

        if (parameter.type !== "Identifier") {
          throw new ParseError("this parameter isn't recognized");
        }

        const loopVariable = parameter.name;

        if (funcNode.body.type !== "BlockStatement") {
          throw new ParseError("block statement expected");
        }

        const loopBody = this.transformBodyNode(funcNode.body);
        instruction = {
          type: "range",
          name: loopVariable,
          loopVariable,
          loopBody,
        };
        break;
      }

      case "readInt32": {
        if (args.length !== 0) {
          throw new ParseError(
            "readInt32() function accepts exactly 0 argument"
          );
        }
        instruction = { type: "readInt32" };
        break;
      }

      default:
        throw new ParseError("Unknown instruction: " + name);
    }

    return instruction;
  }

  private transformBodyNode(
    bodyNode: ExtendNode<ESTree.BlockStatement>
  ): Instruction[] {
    let instructions: Instruction[] = [];

    for (const statement of bodyNode.body) {
      if (
        statement.type !== "ExpressionStatement" ||
        statement.expression.type !== "CallExpression"
      ) {
        throw new ParseError(
          "Invalid statement type. range: " +
            statement.start +
            " to " +
            statement.end
        );
      }
      instructions.push(this.processNode(statement.expression) as Instruction);
    }

    return instructions;
  }
}

const code = `environment({
    fibSeq: array([int32], 100),  // Memory to hold Fibonacci sequence up to the 100th term
    anotherArray: array([int8, int64], 3) // Example of an array where each element can hold multiple values
});

procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, _ => {
    set("n", readInt32());  // Reading the term 'n' to which Fibonacci sequence is to be calculated
    set("a", 0);
    set("b", 1);
    
    // Initialize first two numbers in fibonacci series
    store("fibSeq", 0, [get("a")]);
    store("fibSeq", 1, [get("b")]);

    range(get("n") - 2, x => {  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", x + 2, [get("i")]);  // Storing the newly calculated fibonacci term
    })
});`;
const transformer = new CoqCPASTTransformer(code);
console.log(JSON.stringify(transformer.transform(), null, 4));
