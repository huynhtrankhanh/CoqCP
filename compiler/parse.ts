import acorn, { ExtendNode } from 'acorn'
import * as ESTree from 'estree'

export type PrimitiveType =
  | 'bool'
  | 'int8'
  | 'int16'
  | 'int32'
  | 'int64'
  | 'int256'
  | 'address'

export interface ArrayDeclaration {
  itemTypes: PrimitiveType[]
  length: {
    type: 'literal'
    valueType: 'number'
    raw: string
    location: Location
  }
}

export interface Environment {
  arrays: Map<string, ArrayDeclaration>
}

export interface Variable {
  type: PrimitiveType
}

export type BinaryOp =
  | 'add'
  | 'subtract'
  | 'multiply'
  | 'mod'
  | 'bitwise or'
  | 'bitwise xor'
  | 'bitwise and'
  | 'boolean and'
  | 'boolean or'
  | 'shift right'
  | 'shift left'
  | 'equal'
  | 'noteq'

export type LocalBinder = {
  type: 'local binder'
  name: string
  location: Location
}
export type ValueType =
  | LocalBinder
  | {
      type: 'literal'
      valueType: 'number' | 'boolean' | 'string'
      raw: string
      location: Location
    }
  | Instruction

const castToInstruction = (x: ValueType): Instruction | undefined =>
  x.type === 'local binder' || x.type === 'literal' ? undefined : x

export interface BinaryOperationInstruction {
  type: 'binaryOp'
  operator: BinaryOp
  left: ValueType
  right: ValueType
}

export type UnaryOp = 'minus' | 'plus' | 'bitwise not' | 'boolean not'

export interface UnaryOperationInstruction {
  type: 'unaryOp'
  operator: UnaryOp
  value: ValueType
}

export const COMMUNICATION = Symbol('communication')

export type Instruction = (
  | { type: 'get'; name: string }
  | {
      type: 'set'
      name: string
      value: ValueType
    }
  | {
      type: 'store'
      name: string
      index: ValueType
      tuple: ValueType[]
    }
  | {
      type: 'store'
      name: typeof COMMUNICATION
      index: ValueType
      value: ValueType
    }
  | { type: 'retrieve'; name: string | typeof COMMUNICATION; index: ValueType }
  | { type: 'communication area size' }
  | {
      type: 'invoke'
      address: ValueType
      money: ValueType
      array: string
      communicationSize: ValueType
    }
  | { type: 'donate'; address: ValueType; money: ValueType }
  | { type: 'get sender' }
  | { type: 'get money' }
  | {
      type: 'range'
      end: ValueType
      loopVariable: string
      loopBody: Instruction[]
    }
  | { type: 'readChar' }
  | { type: 'writeChar'; value: ValueType }
  | BinaryOperationInstruction
  | UnaryOperationInstruction
  | {
      type: 'subscript'
      value: ValueType
      index: ValueType
    }
  | {
      type: 'condition'
      condition: ValueType
      body: Instruction[]
      alternate: Instruction[]
    }
  | {
      type: 'sDivide'
      left: ValueType
      right: ValueType
    }
  | {
      type: 'divide'
      left: ValueType
      right: ValueType
    }
  | {
      type: 'coerceInt8'
      value: ValueType
    }
  | {
      type: 'coerceInt16'
      value: ValueType
    }
  | {
      type: 'coerceInt32'
      value: ValueType
    }
  | {
      type: 'coerceInt64'
      value: ValueType
    }
  | {
      type: 'coerceInt256'
      value: ValueType
    }
  | { type: 'less'; left: ValueType; right: ValueType }
  | { type: 'sLess'; left: ValueType; right: ValueType }
  | {
      type: 'call'
      procedure: string
      presetVariables: Map<string, ValueType>
    }
  | {
      type: 'cross module call'
      procedure: string
      module: string
      presetVariables: Map<string, ValueType>
      // key is name of the array of the called procedure's module
      arrayMapping: Map<string, string>
    }
  | {
      type: 'break' | 'continue' | 'flush'
    }
  | { type: 'construct address'; bytes: ValueType[] }
) & { location: Location }

export class ParseError extends Error {
  constructor(...args: string[] | undefined[]) {
    super(...args)
    this.name = 'ParseError'
  }
}

export type Location = {
  start: { line: number; column: number }
  end: { line: number; column: number }
}

const formatLocation = ({ start, end }: Location): string =>
  `${start.line}:${start.column}-${end.line}:${end.column}`

export interface Procedure {
  name: string
  variables: Map<string, Variable>
  body: Instruction[]
  nameLocation: Location
}

export class CoqCPAST {
  environment: Environment | null = null
  procedures: Procedure[] = []
  moduleName: string = ''
  moduleNameLocation: Location | null = null
}

export class CoqCPASTTransformer {
  ast: acorn.ExtendNode<ESTree.Program>
  result: CoqCPAST

  constructor(code: string) {
    this.ast = acorn.parse(code, {
      sourceType: 'module',
      ecmaVersion: 2023,
      locations: true,
    })
    this.result = new CoqCPAST()
  }

  transform() {
    let seenEnvironmentBlock = false
    for (const node of this.ast.body) {
      if (
        node.type !== 'ExpressionStatement' ||
        node.expression.type !== 'CallExpression' ||
        node.expression.callee.type !== 'Identifier' ||
        (node.expression.callee.name !== 'environment' &&
          node.expression.callee.name !== 'procedure' &&
          node.expression.callee.name !== 'module')
      ) {
        throw new ParseError(
          'only "environment", "procedure" and "module" expressions allowed. ' +
            formatLocation(node.loc)
        )
      }

      if (node.expression.callee.name === 'environment') {
        if (seenEnvironmentBlock) {
          throw new ParseError(
            'duplicate environment block. ' + formatLocation(node.loc)
          )
        }
        seenEnvironmentBlock = true

        if (node.expression.arguments.length !== 1) {
          throw new ParseError(
            'environment block accepts exactly 1 argument. ' +
              formatLocation(node.loc)
          )
        }

        const argumentNode = node.expression.arguments[0]
        if (argumentNode.type !== 'ObjectExpression') {
          throw new ParseError(
            'the argument must be an object. ' +
              formatLocation(argumentNode.loc)
          )
        }

        for (const property of argumentNode.properties) {
          if (property.type === 'SpreadElement') {
            throw new ParseError(
              "spread syntax isn't recognized. " + formatLocation(property.loc)
            )
          }

          let keyName: string

          if (property.key.type === 'Identifier') keyName = property.key.name
          else if (property.key.type === 'Literal') {
            if (typeof property.key.value !== 'string')
              throw new ParseError(
                'unrecognized key type. ' + formatLocation(property.key.loc)
              )
            keyName = property.key.value
          } else
            throw new ParseError(
              'unrecognized key type. ' + formatLocation(property.key.loc)
            )

          const arrayDescription = property.value
          if (
            arrayDescription.type !== 'CallExpression' ||
            arrayDescription.callee.type !== 'Identifier' ||
            arrayDescription.callee.name !== 'array'
          ) {
            throw new ParseError(
              'expecting an array expression. ' +
                formatLocation(arrayDescription.loc)
            )
          }

          if (arrayDescription.arguments.length !== 2) {
            throw new ParseError(
              'array() accepts exactly two arguments. ' +
                formatLocation(arrayDescription.loc)
            )
          }

          const typesArrayNode = arrayDescription.arguments[0]
          const lengthNode = arrayDescription.arguments[1]

          if (typesArrayNode.type !== 'ArrayExpression') {
            throw new ParseError(
              'first argument of array() must be an array.' +
                formatLocation(typesArrayNode.loc)
            )
          }

          let itemTypes: PrimitiveType[] = []
          for (const itemType of typesArrayNode.elements) {
            if (
              itemType === null ||
              itemType.type !== 'Identifier' ||
              (itemType.name !== 'int8' &&
                itemType.name !== 'int16' &&
                itemType.name !== 'int32' &&
                itemType.name !== 'int64' &&
                itemType.name !== 'int256' &&
                itemType.name !== 'address' &&
                itemType.name !== 'bool')
            ) {
              throw new ParseError(
                'invalid array item type. range: ' +
                  formatLocation(typesArrayNode.loc)
              )
            }

            itemTypes.push(itemType.name)
          }

          if (!this.result.environment) {
            this.result.environment = { arrays: new Map() }
          }

          if (this.result.environment.arrays.get(keyName) !== undefined) {
            throw new ParseError(
              'duplicate identifier in environment block. ' +
                formatLocation(property.key.loc)
            )
          }

          const lengthLiteral = this.processNode(lengthNode)
          if (
            lengthLiteral.type === 'literal' &&
            lengthLiteral.valueType === 'number'
          ) {
            this.result.environment.arrays.set(keyName, {
              itemTypes,
              length: {
                type: 'literal',
                valueType: 'number',
                location: lengthLiteral.location,
                raw: lengthLiteral.raw,
              },
            })
          } else {
            throw new ParseError(
              'second argument of array() must be a numeric literal.' +
                formatLocation(lengthNode.loc)
            )
          }
        }
      }

      if (node.expression.callee.name === 'procedure') {
        // Parsing the procedure block
        if (node.expression.arguments.length !== 3) {
          throw new ParseError(
            'procedure block accepts exactly 3 arguments. ' +
              formatLocation(node.loc)
          )
        }

        const procedureNameNode = node.expression.arguments[0]
        const variableListNode = node.expression.arguments[1]
        const bodyNode = node.expression.arguments[2]

        if (
          procedureNameNode.type !== 'Literal' ||
          typeof procedureNameNode.value !== 'string'
        ) {
          throw new ParseError(
            'first argument of procedure() must be a string literal. ' +
              formatLocation(procedureNameNode.loc)
          )
        }

        if (variableListNode.type !== 'ObjectExpression') {
          throw new ParseError(
            'second argument of procedure() must be an object. ' +
              formatLocation(variableListNode.loc)
          )
        }

        // building the variables object
        let variables: Map<string, Variable> = new Map()
        for (const property of variableListNode.properties) {
          if (property.type === 'SpreadElement') {
            throw new ParseError(
              "spread syntax isn't recognized. " + formatLocation(property.loc)
            )
          }

          let keyName: string

          if (property.key.type === 'Identifier') keyName = property.key.name
          else if (property.key.type === 'Literal') {
            if (typeof property.key.value !== 'string')
              throw new ParseError(
                'unrecognized key type. ' + formatLocation(property.key.loc)
              )

            keyName = property.key.value
          } else
            throw new ParseError(
              'unrecognized key type. ' + formatLocation(property.key.loc)
            )

          if (property.value.type !== 'Identifier') {
            throw new ParseError(
              'unrecognized value type. ' + formatLocation(property.value.loc)
            )
          }

          if (variables.get(keyName) !== undefined) {
            throw new ParseError(
              'duplicate identifier in procedure variables. ' +
                formatLocation(property.key.loc)
            )
          }

          const declaredType = property.value.name
          if (
            declaredType !== 'int8' &&
            declaredType !== 'int16' &&
            declaredType !== 'int32' &&
            declaredType !== 'int64' &&
            declaredType !== 'int256' &&
            declaredType !== 'address' &&
            declaredType !== 'bool'
          )
            throw new ParseError(
              'invalid variable type. ' + formatLocation(property.value.loc)
            )

          variables.set(keyName, { type: declaredType })
        }

        // transforming bodyNode into Instruction[]
        if (
          bodyNode.type !== 'ArrowFunctionExpression' ||
          bodyNode.body.type !== 'BlockStatement'
        ) {
          throw new ParseError(
            'third argument of procedure() must be an arrow function expression. ' +
              formatLocation(bodyNode.loc)
          )
        }

        if (bodyNode.params.length !== 0) {
          throw new ParseError("inner function can't take arguments")
        }

        const body: Instruction[] = this.transformBodyNode(bodyNode.body)

        // adding the procedure to the result
        this.result.procedures.push({
          name: procedureNameNode.value,
          variables,
          body,
          nameLocation: procedureNameNode.loc,
        })
      }
      if (node.expression.callee.name === 'module') {
        if (this.result.moduleName !== '') {
          throw new ParseError(
            'duplicate module expression. ' + formatLocation(node.loc)
          )
        }

        if (node.expression.arguments.length !== 1) {
          throw new ParseError(
            'module expression accepts exactly 1 argument. ' +
              formatLocation(node.loc)
          )
        }

        const argument = node.expression.arguments[0]
        if (argument.type !== 'Identifier') {
          throw new ParseError(
            'module expression must take an identifier. ' +
              formatLocation(argument.loc)
          )
        }

        this.result.moduleName = argument.name
        this.result.moduleNameLocation = argument.loc
      }
    }
    return this.result
  }

  private processNode(node: ExtendNode<ESTree.Node>): ValueType {
    if (node.type === 'CallExpression' && node.callee.type === 'Identifier') {
      return this.processInstruction(
        node.callee.name,
        node.arguments.map((x) => {
          if (x.type === 'SpreadElement') {
            throw new ParseError("spread syntax isn't recognized")
          }

          return x
        }),
        node.loc
      )
    } else if (node.type === 'Identifier') {
      return { type: 'local binder', name: node.name, location: node.loc }
    } else if (
      node.type === 'Literal' &&
      (typeof node.value === 'number' ||
        typeof node.value === 'boolean' ||
        typeof node.value === 'string')
    ) {
      if (node.raw === undefined) {
        throw new ParseError(
          "raw value of literal can't be undefined. " + formatLocation(node.loc)
        )
      }
      return {
        type: 'literal',
        valueType:
          typeof node.value === 'number'
            ? 'number'
            : typeof node.value === 'boolean'
              ? 'boolean'
              : 'string',
        raw: typeof node.value === 'string' ? node.value : node.raw,
        location: node.loc,
      }
    } else if (node.type === 'BinaryExpression') {
      return this.processBinaryExpression(node)
    } else if (node.type === 'UnaryExpression') {
      const { operator, argument } = node
      const value = this.processNode(argument)
      switch (operator) {
        case '!':
          return {
            type: 'unaryOp',
            operator: 'boolean not',
            value,
            location: node.loc,
          }
        case '+':
          return {
            type: 'unaryOp',
            operator: 'plus',
            value,
            location: node.loc,
          }
        case '-':
          return {
            type: 'unaryOp',
            operator: 'minus',
            value,
            location: node.loc,
          }
        case '~':
          return {
            type: 'unaryOp',
            operator: 'bitwise not',
            value,
            location: node.loc,
          }
        default:
          throw new ParseError(
            'operator not recognized. ' + formatLocation(argument.loc)
          )
      }
    } else if (node.type === 'MemberExpression') {
      const instruction = this.processNode(node.object)
      const index = this.processNode(node.property)
      if (instruction.type === 'literal') {
        throw new ParseError(
          "left hand side can't be a literal. " + formatLocation(node.loc)
        )
      }
      return {
        type: 'subscript',
        value: instruction,
        index,
        location: node.loc,
      }
    } else if (node.type === 'LogicalExpression') {
      const left = this.processNode(node.left)
      const right = this.processNode(node.right)
      const operator = this.getBinaryOperator(node.operator, node.loc)
      return { type: 'binaryOp', operator, left, right, location: node.loc }
    } else {
      throw new ParseError(
        'unrecognized node type: ' + node.type + '. ' + formatLocation(node.loc)
      )
    }
  }

  private processBinaryExpression(
    node: ExtendNode<ESTree.BinaryExpression>
  ): BinaryOperationInstruction & { location: Location } {
    const operator = this.getBinaryOperator(node.operator, node.loc)
    const left = this.processNode(node.left)
    const right = this.processNode(node.right)
    return { type: 'binaryOp', operator, left, right, location: node.loc }
  }

  private getBinaryOperator(
    operator: string,
    location: {
      start: {
        line: number
        column: number
      }
      end: {
        line: number
        column: number
      }
    }
  ): BinaryOp {
    switch (operator) {
      case '+':
        return 'add'
      case '-':
        return 'subtract'
      case '*':
        return 'multiply'
      case '==':
        return 'equal'
      case '!=':
        return 'noteq'
      case '|':
        return 'bitwise or'
      case '^':
        return 'bitwise xor'
      case '&':
        return 'bitwise and'
      case '>>':
        return 'shift right'
      case '<<':
        return 'shift left'
      case '%':
        return 'mod'
      case '&&':
        return 'boolean and'
      case '||':
        return 'boolean or'
      default:
        throw new ParseError(
          'invalid binary operator: ' +
            operator +
            '. ' +
            formatLocation(location)
        )
    }
  }

  private processInstruction(
    name: string,
    args: ExtendNode<ESTree.Expression>[],
    location: {
      start: {
        line: number
        column: number
      }
      end: {
        line: number
        column: number
      }
    }
  ): Instruction {
    let instruction: Instruction

    switch (name) {
      case 'get': {
        if (
          args.length !== 1 ||
          args[0].type !== 'Literal' ||
          typeof args[0].value !== 'string'
        ) {
          throw new ParseError(
            'get() function accepts exactly 1 string argument. ' +
              formatLocation(location)
          )
        }
        const varName = args[0].value
        instruction = { type: 'get', name: varName, location }
        break
      }

      case 'set': {
        if (
          args.length !== 2 ||
          args[0].type !== 'Literal' ||
          typeof args[0].value !== 'string'
        ) {
          throw new ParseError(
            'set() function accepts exactly 2 arguments: variable name, value. ' +
              formatLocation(location)
          )
        }
        const varName = args[0].value
        const value = this.processNode(args[1])
        instruction = { type: 'set', name: varName, value, location }
        break
      }

      case 'store': {
        if (
          args.length === 3 &&
          args[0].type === 'Literal' &&
          typeof args[0].value === 'string' &&
          args[2].type === 'ArrayExpression'
        ) {
          const arrayName = args[0].value
          const index = this.processNode(args[1])
          const tuples = args[2].elements.map((node) => {
            if (node === null) {
              throw new ParseError(
                "node can't be null. " + formatLocation(location)
              )
            }
            if (node.type === 'SpreadElement') {
              throw new ParseError(
                "spread syntax isn't recognized. " + formatLocation(location)
              )
            }
            return this.processNode(node)
          })
          instruction = {
            type: 'store',
            name: arrayName,
            index,
            tuple: tuples,
            location,
          }
        } else if (args.length === 2) {
          const index = this.processNode(args[0])
          const value = this.processNode(args[1])
          instruction = {
            type: 'store',
            name: COMMUNICATION,
            index,
            value,
            location,
          }
        } else {
          throw new ParseError(
            'store() function accepts 3 arguments: array name, index, tuple or 2 arguments: index, tuple. ' +
              formatLocation(location)
          )
        }
        break
      }

      case 'retrieve': {
        if (
          args.length === 2 &&
          args[0].type === 'Literal' &&
          typeof args[0].value === 'string'
        ) {
          const arrayName = args[0].value
          const index = this.processNode(args[1])
          instruction = { type: 'retrieve', name: arrayName, index, location }
        } else if (args.length === 1) {
          const index = this.processNode(args[0])
          instruction = {
            type: 'retrieve',
            name: COMMUNICATION,
            index,
            location,
          }
        } else {
          throw new ParseError(
            'retrieve() function accepts 2 arguments, array name, index or 1 argument: index. ' +
              formatLocation(location)
          )
        }
        break
      }

      case 'communicationSize': {
        if (args.length !== 0) {
          throw new ParseError(
            'communicationSize() takes no arguments. ' +
              formatLocation(location)
          )
        }
        instruction = { type: 'communication area size', location }
        break
      }

      case 'getSender': {
        if (args.length !== 0) {
          throw new ParseError(
            'getSender() takes no arguments. ' + formatLocation(location)
          )
        }
        instruction = { type: 'get sender', location }
        break
      }

      case 'getMoney': {
        if (args.length !== 0) {
          throw new ParseError(
            'getMoney() takes no arguments. ' + formatLocation(location)
          )
        }
        instruction = { type: 'get money', location }
        break
      }

      case 'invoke': {
        if (
          args.length !== 4 ||
          args[2].type !== 'Literal' ||
          typeof args[2].value !== 'string'
        ) {
          throw new ParseError(
            'invoke() accepts 4 arguments: address, money, communication array, communication size. ' +
              formatLocation(location)
          )
        }
        const address = this.processNode(args[0])
        const money = this.processNode(args[1])
        const array = args[2].value
        const communicationSize = this.processNode(args[3])

        instruction = {
          type: 'invoke',
          address,
          money,
          array,
          communicationSize,
          location,
        }
        break
      }

      case 'donate': {
        if (args.length !== 2) {
          throw new ParseError(
            'donate() accepts 2 arguments: address, money. ' +
              formatLocation(location)
          )
        }
        const address = this.processNode(args[0])
        const money = this.processNode(args[1])
        instruction = { type: 'donate', address, money, location }
        break
      }

      case 'address': {
        if (args.length !== 20) {
          throw new ParseError(
            'address() function accepts exactly 20 arguments. ' +
              formatLocation(location)
          )
        }
        instruction = {
          type: 'construct address',
          bytes: args.map((x) => ({ ...this.processNode(x), location: x.loc })),
          location,
        }
        break
      }

      case 'range': {
        if (
          args.length !== 2 ||
          args[1].type !== 'ArrowFunctionExpression' ||
          args[1].body.type !== 'BlockStatement'
        ) {
          throw new ParseError(
            'range() function accepts exactly 2 arguments, second one being an arrow function. ' +
              formatLocation(location)
          )
        }
        const end = this.processNode(args[0])
        const funcNode = args[1]

        if (funcNode.params.length !== 1) {
          throw new ParseError(
            'arrow function must take exactly 1 argument. ' +
              formatLocation(funcNode.loc)
          )
        }

        const parameter = funcNode.params[0]

        if (parameter.type !== 'Identifier') {
          throw new ParseError(
            "this parameter isn't recognized. " + formatLocation(parameter.loc)
          )
        }

        const loopVariable = parameter.name

        if (funcNode.body.type !== 'BlockStatement') {
          throw new ParseError(
            'block statement expected. ' + formatLocation(funcNode.loc)
          )
        }

        const loopBody = this.transformBodyNode(funcNode.body)
        instruction = {
          type: 'range',
          loopVariable,
          loopBody,
          end,
          location,
        }
        break
      }

      case 'readChar': {
        if (args.length !== 0) {
          throw new ParseError(
            'readChar() function accepts exactly 0 argument. ' +
              formatLocation(location)
          )
        }
        instruction = { type: 'readChar', location }
        break
      }

      case 'writeChar': {
        if (args.length !== 1) {
          throw new ParseError(
            'writeChar() function accepts exactly 1 argument. ' +
              formatLocation(location)
          )
        }
        const value = this.processNode(args[0])
        instruction = { type: 'writeChar', value, location }
        break
      }

      case 'sDivide': {
        if (args.length !== 2) {
          throw new ParseError(
            'sDivide() function accepts exactly 2 arguments. ' +
              formatLocation(location)
          )
        }
        const left = this.processNode(args[0])
        const right = this.processNode(args[1])
        instruction = { type: 'sDivide', left, right, location }
        break
      }

      case 'divide': {
        if (args.length !== 2) {
          throw new ParseError(
            'divide() function accepts exactly 2 arguments. ' +
              formatLocation(location)
          )
        }
        const left = this.processNode(args[0])
        const right = this.processNode(args[1])
        instruction = { type: 'divide', left, right, location }
        break
      }

      case 'coerceInt8': {
        if (args.length !== 1) {
          throw new ParseError(
            'coerceInt8() function accepts exactly 1 argument. ' +
              formatLocation(location)
          )
        }
        const value = this.processNode(args[0])
        instruction = { type: 'coerceInt8', value, location }
        break
      }

      case 'coerceInt16': {
        if (args.length !== 1) {
          throw new ParseError(
            'coerceInt16() function accepts exactly 1 argument. ' +
              formatLocation(location)
          )
        }
        const value = this.processNode(args[0])
        instruction = { type: 'coerceInt16', value, location }
        break
      }

      case 'coerceInt32': {
        if (args.length !== 1) {
          throw new ParseError(
            'coerceInt32() function accepts exactly 1 argument. ' +
              formatLocation(location)
          )
        }
        const value = this.processNode(args[0])
        instruction = { type: 'coerceInt32', value, location }
        break
      }

      case 'coerceInt64': {
        if (args.length !== 1) {
          throw new ParseError(
            'coerceInt64() function accepts exactly 1 argument. ' +
              formatLocation(location)
          )
        }
        const value = this.processNode(args[0])
        instruction = { type: 'coerceInt64', value, location }
        break
      }

      case 'coerceInt256': {
        if (args.length !== 1) {
          throw new ParseError(
            'coerceInt256() function accepts exactly 1 argument. ' +
              formatLocation(location)
          )
        }
        const value = this.processNode(args[0])
        instruction = { type: 'coerceInt256', value, location }
        break
      }

      case 'less': {
        if (args.length !== 2) {
          throw new ParseError(
            'less() function accepts exactly 2 arguments. ' +
              formatLocation(location)
          )
        }
        const left = this.processNode(args[0])
        const right = this.processNode(args[1])
        instruction = { type: 'less', left, right, location }
        break
      }

      case 'sLess': {
        if (args.length !== 2) {
          throw new ParseError(
            'sLess() function accepts exactly 2 arguments. ' +
              formatLocation(location)
          )
        }
        const left = this.processNode(args[0])
        const right = this.processNode(args[1])
        instruction = { type: 'sLess', left, right, location }
        break
      }

      case 'call': {
        if (args.length === 2) {
          if (args[0].type !== 'Literal' || typeof args[0].value !== 'string') {
            throw new ParseError(
              'first argument to call() must be a procedure name. ' +
                formatLocation(args[0].loc)
            )
          }

          const procedureName = args[0].value
          if (args[1].type !== 'ObjectExpression') {
            throw new ParseError(
              'second argument to call() must be an object denoting preset variables. ' +
                formatLocation(args[1].loc)
            )
          }

          const presetVariables: Map<string, ValueType> = new Map()

          for (const property of args[1].properties) {
            if (property.type === 'SpreadElement') {
              throw new ParseError(
                'spread syntax not allowed. ' + formatLocation(property.loc)
              )
            }

            let name: string

            if (property.key.type === 'Identifier') name = property.key.name
            else if (property.key.type === 'Literal') {
              if (typeof property.key.value !== 'string')
                throw new ParseError(
                  'unrecognized key type. ' + formatLocation(property.key.loc)
                )
              name = property.key.value
            } else
              throw new ParseError(
                'unrecognized key type. ' + formatLocation(property.key.loc)
              )

            const value = this.processNode(property.value)

            if (presetVariables.get(name) !== undefined) {
              throw new ParseError(
                'duplicate identifier in preset variables. ' +
                  formatLocation(property.key.loc)
              )
            }

            presetVariables.set(name, value)
          }

          instruction = {
            type: 'call',
            procedure: procedureName,
            presetVariables,
            location,
          }
        } else if (args.length === 4) {
          const moduleNameNode = args[0]
          if (moduleNameNode.type !== 'Identifier')
            throw new ParseError(
              'first argument to cross module call() expression must be an identifier. ' +
                formatLocation(location)
            )

          const moduleName = moduleNameNode.name

          const arrayMappingNode = args[1]
          if (arrayMappingNode.type !== 'ObjectExpression')
            throw new ParseError(
              'second argument to cross module call() expression must be an object literal. ' +
                formatLocation(location)
            )

          const procedureNameNode = args[2]
          if (
            procedureNameNode.type !== 'Literal' ||
            typeof procedureNameNode.value !== 'string'
          )
            throw new ParseError(
              'third argument to cross module call() expression must be a string literal. ' +
                formatLocation(location)
            )

          const procedureName = procedureNameNode.value

          const presetVariablesNode = args[3]
          if (presetVariablesNode.type !== 'ObjectExpression')
            throw new ParseError(
              'fourth argument to cross module call() expression must be an object literal. ' +
                formatLocation(location)
            )

          const arrayMapping = new Map<string, string>()
          for (const property of arrayMappingNode.properties) {
            if (property.type === 'SpreadElement')
              throw new ParseError(
                'spread syntax not allowed. ' + formatLocation(property.loc)
              )

            let arrayName: string

            if (property.key.type === 'Identifier')
              arrayName = property.key.name
            else if (property.key.type === 'Literal') {
              if (typeof property.key.value !== 'string')
                throw new ParseError(
                  'unrecognized key type. ' + formatLocation(property.loc)
                )
              arrayName = property.key.value
            } else
              throw new ParseError(
                'unrecognized key type. ' + formatLocation(property.loc)
              )

            if (arrayMapping.get(arrayName) !== undefined)
              throw new ParseError(
                'duplicate identifier in array mapping. ' +
                  formatLocation(property.loc)
              )

            if (
              property.value.type !== 'Literal' ||
              typeof property.value.value !== 'string'
            )
              throw new ParseError(
                'value must be a string literal denoting array name. ' +
                  formatLocation(property.loc)
              )

            arrayMapping.set(arrayName, property.value.value)
          }

          const presetVariables = new Map<string, ValueType>()

          for (const property of presetVariablesNode.properties) {
            if (property.type === 'SpreadElement')
              throw new ParseError(
                "spread syntax isn't recognized. " +
                  formatLocation(property.loc)
              )
            let name: string
            if (property.key.type === 'Identifier') name = property.key.name
            else if (property.key.type === 'Literal') {
              if (typeof property.key.value !== 'string')
                throw new ParseError(
                  'unrecognized key type. ' + formatLocation(property.key.loc)
                )
              name = property.key.value
            } else
              throw new ParseError(
                'unrecognized key type. ' + formatLocation(property.key.loc)
              )

            if (presetVariables.get(name) !== undefined)
              throw new ParseError(
                'duplicate identifier in preset variables. ' +
                  formatLocation(property.key.loc)
              )

            presetVariables.set(name, this.processNode(property.value))
          }

          instruction = {
            type: 'cross module call',
            procedure: procedureName,
            presetVariables,
            arrayMapping,
            module: moduleName,
            location,
          }
        } else {
          throw new ParseError(
            'call() takes exactly 2 arguments for intra-module calls or 4 arguments for cross module calls. ' +
              formatLocation(location)
          )
        }
        break
      }

      default:
        throw new ParseError(
          'unknown instruction: ' + name + '. ' + formatLocation(location)
        )
    }

    return instruction
  }

  private transformBodyNode(
    bodyNode: ExtendNode<ESTree.BlockStatement>
  ): Instruction[] {
    let instructions: Instruction[] = []

    for (const statement of bodyNode.body) {
      if (statement.type === 'EmptyStatement') continue
      if (statement.type === 'IfStatement') {
        const test = this.processNode(statement.test)
        if (statement.consequent.type !== 'BlockStatement') {
          throw new ParseError(
            'must be a block statement. ' +
              formatLocation(statement.consequent.loc)
          )
        }
        const consequent = this.transformBodyNode(statement.consequent)
        const alternate = statement.alternate
        if (alternate === null || alternate === undefined) {
          instructions.push({
            type: 'condition',
            condition: test,
            body: consequent,
            alternate: [],
            location: statement.loc,
          })
          continue
        }
        if (alternate.type !== 'BlockStatement') {
          if (alternate.loc === undefined || alternate.loc === null) {
            throw new ParseError('must be a block statement. ' + statement.loc)
          }
          throw new ParseError(
            'must be a block statement. ' + formatLocation(alternate.loc)
          )
        }
        instructions.push({
          type: 'condition',
          condition: test,
          body: consequent,
          alternate: this.transformBodyNode(alternate),
          location: statement.loc,
        })
        continue
      }
      if (
        statement.type === 'ExpressionStatement' &&
        statement.expression.type === 'Literal'
      ) {
        if (
          statement.expression.value === 'break' ||
          statement.expression.value === 'continue' ||
          statement.expression.value === 'flush'
        ) {
          instructions.push({
            type: statement.expression.value as 'break' | 'continue' | 'flush',
            location: statement.loc,
          })
          continue
        }
        throw new ParseError(
          'invalid statement type. ' + formatLocation(statement.loc)
        )
      }
      if (
        statement.type !== 'ExpressionStatement' ||
        statement.expression.type !== 'CallExpression'
      ) {
        throw new ParseError(
          'invalid statement type. ' + formatLocation(statement.loc)
        )
      }
      const processed = castToInstruction(
        this.processNode(statement.expression)
      )
      if (processed === undefined) {
        throw new ParseError(
          'invalid statement type. ' + formatLocation(statement.loc)
        )
      }
      instructions.push(processed)
    }

    return instructions
  }
}
