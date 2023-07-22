import * as acorn from "acorn";
import { simple as walkSimple } from "acorn-walk";

interface ArrayDeclaration {
  itemTypes: string[];
  length: number;
}

interface Environment {
  arrays: Record<string, ArrayDeclaration>;
}

interface Variable {
  type: string;
}

type Instruction =
  | { type: 'get', name: string }
  | { type: 'set', name: string, value: string | number }
  | { type: 'store', name: string, index: number, tuples: (string | number)[] }
  | { type: 'retrieve', name: string, index: number }
  | { type: 'range', name: string, loopVariable: string, loopBody: Instruction[] }
  | { type: 'operation', operator: string, operands: (string | Instruction)[] };

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
  private parser = acorn.Parser;
  ast: any;
  result: CoqCPAST;

  constructor(code: string) {
    this.ast = this.parser.parse(code, { sourceType: "module" });
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
    const arrays: Record<string, ArrayDeclaration> = {};
    node.properties.forEach((prop) => {
      const name = prop.key.name;
      const itemTypes = prop.value.elements[0].elements.map((el) => el.name);
      const length = prop.value.elements[1].value;

      arrays[name] = { itemTypes, length };
    });

    return { arrays };
  }

  transformProcedure(nodes): Procedure {
    const name = nodes[0].value;
    const variables: Record<string, Variable> = {};
    nodes[1].properties.forEach((prop: any) => {
      const variableName = prop.key.name;

      variables[variableName] = {
        type: prop.value.name,
      };
    });

    const body = this.transformInstructions(nodes[2]);
    return { name, variables, body };
  }

  transformInstructions(node): Instruction[] {
    const instructions: Instruction[] = [];
    walkSimple(node, {
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
    const type = node.callee.name;

    switch (type) {
      case 'set':
        return {
          type: 'set',
          name: node.arguments[0].value,
          value: node.arguments[1].value
        };
      case 'get':
        return {
          type: 'get',
          name: node.arguments[0].value,
        };
      case 'store':
        return {
          type: 'store',
          name: node.arguments[0].value,
          index: node.arguments[1].value,
          tuples: node.arguments[2].elements.map((el: any) => el.value),
        };
      case 'retrieve':
        return {
          type: 'retrieve',
          name: node.arguments[0].value,
          index: node.arguments[1].value,
        };
      case 'range':
        return {
          type: 'range',
          name: node.arguments[0].value,
          loopVariable: node.arguments[1].params[0].name,
          loopBody: this.transformInstructions(node.arguments[1].body),
        };
      default:
        throw new Error(`Invalid instruction type: ${type}`);
    }
  }
}

const code = `<Your JavaScript/CoqCP code here>`;
const transformer = new CoqCPASTTransformer(code);
transformer.transform();
