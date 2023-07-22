import * as acorn from "acorn";
import { simple as walkSimple } from "acorn-walk";

interface Variable {
  type: string;
}

interface Instruction {
  type: 'set' | 'get' | 'store' | 'retrieve' | 'range' | 'operation';
  name?: string;
  value?: string | number;
  operator?: string;
  operands?: (string | Instruction)[];
  index?: number;
  tuples?: (string | number)[];
  loopVariable?: string;
  loopBody?: Instruction[];
}

interface Procedure {
  name: string;
  variables: Record<string, Variable>;
  body: Instruction[];
}

interface ArrayDeclaration {
  itemTypes: string[];
  length: number;
}

interface Environment {
  arrays: Record<string, ArrayDeclaration>;
}

class CoqCPAST {
  environment: Environment | null = null;
  procedures: Procedure[] = [];
}

class CoqCPASTTransformer {
  private parser = acorn.Parser;
  ast: any;
  result: CoqCPAST;

  constructor(code: string) {
    this.ast = this.parser.parse(code, {sourceType: "module"});
    this.result = new CoqCPAST();
  }

  transform() {
    walkSimple(this.ast, {
      CallExpression: (node) => {
        const nodeName = node.callee.name;

        if (nodeName === 'environment') {
          if (this.result.environment) {
            throw new Error('Duplicate declaration for "environment"');
          }
          this.result.environment = this.transformEnvironmentDeclaration(node.arguments[0]);
        }

        else if (nodeName === 'procedure') {
          this.result.procedures.push(this.transformProcedure(node.arguments));
        }
      }
    });
  }

  transformEnvironmentDeclaration(node): Environment {
    let arrays: Record<string, ArrayDeclaration> = {};
    node.properties.forEach((prop) => {
      const name = prop.key.name;

      const arraySpec = prop.value.callee.object.callee.name === "array"
                      ? prop.value.callee.object.arguments
                      : prop.value.arguments;

      const itemTypes: string[] = arraySpec[0].elements.map((t: any) => t.name);
      const length: number = arraySpec[1].value;
      arrays[name] = { itemTypes, length };
    });

    return { arrays };
  }

  transformProcedure(nodes): Procedure {
    const name = nodes[0].value;
    let variables: Record<string, Variable> = {};
    nodes[1].properties.forEach((prop: any) => {
      const variableName = prop.key.name;
      const variable: Variable = { 
        type: prop.value.name
      };
      variables[variableName] = variable;
    });
    const body = this.transformInstructions(nodes[2].body);
    return { name, variables, body };
  }

  transformInstructions(node): Instruction[] {
    let instructions: Instruction[] = [];
    walkSimple(node.body, {
      CallExpression: (n) => {
        instructions.push(this.transformInstruction(n));
      },
      BinaryExpression: (n) => {
        instructions.push({
          type: 'operation',
          operator: n.operator,
          operands: [n.left.raw, n.right.raw],
        });
      },
    });
    return instructions;
  }

  transformInstruction(node): Instruction {
    let type = node.callee.name;
    let instruction: Instruction = { type: type };
    switch (type) {
      case 'set':
        instruction.name = node.arguments[0].value;
        instruction.value = node.arguments[1].value;
        break;
      case 'get':
        instruction.name = node.arguments[0].value;
        break;
      case 'store':
        instruction.name = node.arguments[0].value;
        instruction.index = node.arguments[1].value;
        instruction.tuples = node.arguments[2].elements.map((el: any) => el.value);
        break;
      case 'retrieve':
        instruction.name = node.arguments[0].value;
        instruction.index = node.arguments[1].value;
        break;
      case 'range':
        instruction.name = node.arguments[0].value;
        instruction.loopVariable = node.arguments[1].params[0].name;
        instruction.loopBody = this.transformInstructions(node.arguments[1].body);
        break;
    }
    return instruction;
  }
}

const code = `<Your JavaScript/CoqCP code here>`;
const transformer = new CoqCPASTTransformer(code);
transformer.transform();
