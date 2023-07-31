import acorn, { ExtendNode } from "acorn";
import * as ESTree from "estree";

type PrimitiveType = "bool" | "int8" | "int16" | "int32" | "int64";

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

type LocalBinder = { type: "local binder"; name: string };
type ValueType = LocalBinder | number | Instruction | boolean;

interface BinaryOperationInstruction {
  type: "binaryOp";
  operator: BinaryOp;
  left: ValueType;
  right: ValueType;
}

type Instruction =
  | { type: "get"; name: string }
  | {
      type: "set";
      name: string;
      value: ValueType;
    }
  | {
      type: "store";
      name: string;
      index: number;
      tuples: ValueType[];
    }
  | { type: "retrieve"; name: string; index: number }
  | {
      type: "range";
      name: string;
      end: ValueType;
      loopVariable: string;
      loopBody: Instruction[];
    }
  | { type: "readInt8" }
  | { type: "writeInt8"; value: ValueType }
  | BinaryOperationInstruction
  | { type: "subscript"; value: Instruction | LocalBinder; index: number }
  | {
      type: "condition";
      condition: ValueType;
      body: Instruction[];
      alternate: Instruction[];
    };

class ParseError extends Error {
  constructor(...args: string[] | undefined[]) {
    super(...args);
    this.name = "ParseError";
  }
}

type Location = {
  start: { line: number; column: number };
  end: { line: number; column: number };
};

const formatLocation = ({ start, end }: Location): string =>
  `${start.line}:${start.column}-${end.line}:${end.column}`;

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
    this.ast = acorn.parse(code, {
      sourceType: "module",
      ecmaVersion: 2023,
      locations: true,
    });
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
          'only "environment" and "procedure" expressions allowed. ' +
            formatLocation(node.loc),
        );
      }

      if (node.expression.callee.name === "environment") {
        if (seenEnvironmentBlock) {
          throw new ParseError(
            "duplicate environment block. " + formatLocation(node.loc),
          );
        }
        seenEnvironmentBlock = true;

        if (node.expression.arguments.length !== 1) {
          throw new ParseError(
            "environment block accepts exactly 1 argument. " +
              formatLocation(node.loc),
          );
        }

        const argumentNode = node.expression.arguments[0];
        if (argumentNode.type !== "ObjectExpression") {
          throw new ParseError(
            "the argument must be an object. " +
              formatLocation(argumentNode.loc),
          );
        }

        for (const property of argumentNode.properties) {
          if (property.type === "SpreadElement") {
            throw new ParseError(
              "spread syntax isn't recognized. " + formatLocation(property.loc),
            );
          }

          if (property.key.type !== "Identifier") {
            throw new ParseError(
              "unrecognized key type. " + formatLocation(property.key.loc),
            );
          }

          const arrayDescription = property.value;
          if (
            arrayDescription.type !== "CallExpression" ||
            arrayDescription.callee.type !== "Identifier" ||
            arrayDescription.callee.name !== "array"
          ) {
            throw new ParseError(
              "expecting an array expression. " +
                formatLocation(arrayDescription.loc),
            );
          }

          if (arrayDescription.arguments.length !== 2) {
            throw new ParseError(
              "array() accepts exactly two arguments. " +
                formatLocation(arrayDescription.loc),
            );
          }

          const typesArrayNode = arrayDescription.arguments[0];
          const lengthNode = arrayDescription.arguments[1];

          if (typesArrayNode.type !== "ArrayExpression") {
            throw new ParseError(
              "first argument of array() must be an array." +
                formatLocation(typesArrayNode.loc),
            );
          }

          if (
            lengthNode.type !== "Literal" ||
            typeof lengthNode.value !== "number"
          ) {
            throw new ParseError(
              "second argument of array() must be a numeric literal." +
                formatLocation(lengthNode.loc),
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
                "invalid array item type. range: " +
                  formatLocation(typesArrayNode.loc),
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
        // Parsing the procedure block
        if (node.expression.arguments.length !== 3) {
          throw new ParseError(
            "procedure block accepts exactly 3 arguments. " +
              formatLocation(node.loc),
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
            "first argument of procedure() must be a string literal. " +
              formatLocation(procedureNameNode.loc),
          );
        }

        if (variableListNode.type !== "ObjectExpression") {
          throw new ParseError(
            "second argument of procedure() must be an object. " +
              formatLocation(variableListNode.loc),
          );
        }

        // building the variables object
        let variables: Record<string, Variable> = {};
        for (const property of variableListNode.properties) {
          if (property.type === "SpreadElement") {
            throw new ParseError(
              "spread syntax isn't recognized. " + formatLocation(property.loc),
            );
          }

          if (property.key.type !== "Identifier") {
            throw new ParseError(
              "unrecognized key type. " + formatLocation(property.key.loc),
            );
          }

          if (property.value.type !== "Identifier") {
            throw new ParseError(
              "unrecognized value type. " + formatLocation(property.value.loc),
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
            "third argument of procedure() must be an arrow function expression. " +
              formatLocation(bodyNode.loc),
          );
        }

        if (bodyNode.params.length !== 0) {
          throw new ParseError("inner function can't take arguments");
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
    return this.result;
  }

  private processNode(node: ExtendNode<ESTree.Node>): ValueType {
    if (node.type === "CallExpression" && node.callee.type === "Identifier") {
      return this.processInstruction(
        node.callee.name,
        node.arguments.map((x) => {
          if (x.type === "SpreadElement") {
            throw new Error("spread syntax not supported");
          }

          return x;
        }),
        node.loc,
      );
    } else if (node.type === "Identifier") {
      return { type: "local binder", name: node.name };
    } else if (
      node.type === "Literal" &&
      (typeof node.value === "number" || typeof node.value === "boolean")
    ) {
      return node.value;
    } else if (node.type === "BinaryExpression") {
      return this.processBinaryExpression(node);
    } else if (node.type === "MemberExpression") {
      const instruction = this.processNode(node.object);
      if (node.property.type !== "Literal") {
        throw new ParseError(
          "only literal indices allowed. " + formatLocation(node.loc),
        );
      }
      const index = node.property.raw;
      if (index === undefined) {
        throw new ParseError(
          "index must be defined. " + formatLocation(node.loc),
        );
      }
      if (typeof instruction === "number" || typeof instruction === "boolean") {
        throw new ParseError(
          "left hand side can't be a literal. " + formatLocation(node.loc),
        );
      }
      return { type: "subscript", value: instruction, index: Number(index) };
    } else {
      throw new ParseError("unrecognized node type: " + node.type + ". " + formatLocation(node.loc));
    }
  }

  private processBinaryExpression(
    node: ExtendNode<ESTree.BinaryExpression>,
  ): BinaryOperationInstruction {
    const operator = this.getBinaryOperator(node.operator, node.loc);
    const left = this.processNode(node.left);
    const right = this.processNode(node.right);
    return { type: "binaryOp", operator, left, right };
  }

  private getBinaryOperator(
    operator: string,
    location: {
      start: {
        line: number;
        column: number;
      };
      end: {
        line: number;
        column: number;
      };
    },
  ): BinaryOp {
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
        throw new ParseError(
          "invalid binary operator: " +
            operator +
            ". " +
            formatLocation(location),
        );
    }
  }

  private processInstruction(
    name: string,
    args: ExtendNode<ESTree.Expression>[],
    location: {
      start: {
        line: number;
        column: number;
      };
      end: {
        line: number;
        column: number;
      };
    },
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
            "get() function accepts exactly 1 string argument. " +
              formatLocation(location),
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
            "set() function accepts exactly 2 arguments, first one being a string. " +
              formatLocation(location),
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
            "store() function accepts exactly 3 arguments, first one being a string and last one being an array. " +
              formatLocation(location),
          );
        }
        const arrayName = args[0].value;
        const index = this.processNode(args[1]) as number;
        const tuples = args[2].elements.map((node) => {
          if (node === null) {
            throw new Error("node can't be null. " + formatLocation(location));
          }
          if (node.type === "SpreadElement") {
            throw new Error(
              "spread syntax not supported, " + formatLocation(location),
            );
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
            "retrieve() function accepts exactly 2 arguments, first one being a string. " +
              formatLocation(location),
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
            "range() function accepts exactly 2 arguments, second one being an arrow function. " +
              formatLocation(location),
          );
        }
        const end = this.processNode(args[0]);
        const funcNode = args[1];

        if (funcNode.params.length !== 1) {
          throw new ParseError(
            "arrow function must take exactly 1 argument. " +
              formatLocation(funcNode.loc),
          );
        }

        const parameter = funcNode.params[0];

        if (parameter.type !== "Identifier") {
          throw new ParseError(
            "this parameter isn't recognized. " + formatLocation(parameter.loc),
          );
        }

        const loopVariable = parameter.name;

        if (funcNode.body.type !== "BlockStatement") {
          throw new ParseError(
            "block statement expected. " + formatLocation(funcNode.loc),
          );
        }

        const loopBody = this.transformBodyNode(funcNode.body);
        instruction = {
          type: "range",
          name: loopVariable,
          loopVariable,
          loopBody,
          end,
        };
        break;
      }

      case "readInt8": {
        if (args.length !== 0) {
          throw new ParseError(
            "readInt8() function accepts exactly 0 argument. " +
              formatLocation(location),
          );
        }
        instruction = { type: "readInt8" };
        break;
      }

      case "writeInt8": {
        if (args.length !== 1) {
          throw new ParseError(
            "writeInt8() function accepts exactly 1 argument. " +
              formatLocation(location),
          );
        }
        const value = this.processNode(args[0]);
        instruction = { type: "writeInt8", value };
        break;
      }

      default:
        throw new ParseError(
          "unknown instruction: " + name + ". " + formatLocation(location),
        );
    }

    return instruction;
  }

  private transformBodyNode(
    bodyNode: ExtendNode<ESTree.BlockStatement>,
  ): Instruction[] {
    let instructions: Instruction[] = [];

    for (const statement of bodyNode.body) {
      if (statement.type === "IfStatement") {
        const test = this.processNode(statement.test);
        if (statement.consequent.type !== "BlockStatement") {
          throw new Error(
            "must be a block statement. " +
              formatLocation(statement.consequent.loc),
          );
        }
        const consequent = this.transformBodyNode(statement.consequent);
        const alternate = statement.alternate;
        if (alternate === null || alternate === undefined) {
          instructions.push({
            type: "condition",
            condition: test,
            body: consequent,
            alternate: [],
          });
          continue;
        }
        if (alternate.type !== "BlockStatement") {
          if (alternate.loc === undefined || alternate.loc === null) {
            throw new Error("must be a block statement. " + statement.loc);
          }
          throw new Error(
            "must be a block statement. " + formatLocation(alternate.loc),
          );
        }
        instructions.push({
          type: "condition",
          condition: test,
          body: consequent,
          alternate: this.transformBodyNode(
            alternate as ExtendNode<ESTree.BlockStatement>,
          ),
        });
        continue;
      }
      if (
        statement.type !== "ExpressionStatement" ||
        statement.expression.type !== "CallExpression"
      ) {
        throw new ParseError(
          "invalid statement type. " + formatLocation(statement.loc),
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

procedure("fibonacci", { n: int32, a: int32, b: int32, i: int32 }, () => {
    set("n", readInt8());  // Reading the term 'n' to which Fibonacci sequence is to be calculated
    set("a", 0);
    set("b", 1);
    
    // Initialize first two numbers in fibonacci series
    store("fibSeq", 0, [get("a")]);
    store("fibSeq", 1, [get("b")]);

    range(get("n") - 2, x => {  
        set("i", retrieve("fibSeq", x)[0] + retrieve("fibSeq", x + 1)[0]);  // Getting sum of last two fibonacci numbers
        store("fibSeq", x + 2, [get("i")]);  // Storing the newly calculated fibonacci term
    })

    if (get("n") > 100) {
      writeInt8(32);
    } else {writeInt8(64);}
});`;
const transformer = new CoqCPASTTransformer(code);
console.log(JSON.stringify(transformer.transform(), null, 4));
