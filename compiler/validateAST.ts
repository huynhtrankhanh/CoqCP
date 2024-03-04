import { consumeNever } from './consumeNever'
import { findCycle } from './findCycle'
import {
  ValueType,
  Procedure,
  PrimitiveType,
  CoqCPAST,
  Location,
} from './parse'

export type ValidationError = (
  | {
      type: 'binary expression expects numeric' | 'instruction expects numeric'
      actualType1: PrimitiveType | PrimitiveType[] | 'string'
      actualType2: PrimitiveType | PrimitiveType[] | 'string'
    }
  | {
      type: 'binary expression expects boolean'
      actualType1: PrimitiveType | PrimitiveType[] | 'string'
      actualType2: PrimitiveType | PrimitiveType[] | 'string'
    }
  | {
      type: 'binary expression type mismatch' | 'instruction type mismatch'
      actualType1: PrimitiveType | PrimitiveType[] | 'string'
      actualType2: PrimitiveType | PrimitiveType[] | 'string'
    }
  | { type: 'expression no statement' }
  | { type: 'procedure not found'; name: string }
  | { type: 'variable not present'; variables: string[] }
  | {
      type: 'variable type mismatch'
      expectedType: PrimitiveType | PrimitiveType[] | 'string'
      actualType: PrimitiveType | PrimitiveType[] | 'string'
    }
  | {
      type: 'condition must be boolean'
      actualType: PrimitiveType | PrimitiveType[] | 'string'
    }
  | { type: 'no surrounding range command' }
  | { type: 'undefined variable' | 'undefined binder' }
  | { type: 'not representable int64' }
  | { type: 'bad number literal' }
  | { type: 'range end must be int64 or string' }
  | {
      type:
        | 'instruction expects int8'
        | 'instruction expects int64'
        | 'instruction expects tuple'
    }
  | { type: 'undefined array' }
  | { type: 'index out of bounds' }
  | {
      type:
        | 'unary operator expects numeric'
        | "unary operator can't operate on tuples"
        | "unary operator can't operate on strings"
        | 'unary operator expects boolean'
    }
  | { type: "array length can't be negative" }
  | { type: 'string not allowed' }
) & { location: Location & { moduleName: string } }

export const isNumeric = (
  x: string | PrimitiveType[]
): x is 'int8' | 'int16' | 'int32' | 'int64' => {
  return x === 'int8' || x === 'int16' || x === 'int32' || x === 'int64'
}

// There might be duplicate dependencies
const findDependencies = ({ procedures }: CoqCPAST) => {
  function findDependencies(valueType: ValueType): void {
    switch (valueType.type) {
      case 'local binder':
        // Local binders do not introduce dependencies
        break
      case 'literal':
        // Literals do not introduce dependencies
        break
      case 'binaryOp':
        findDependencies(valueType.left)
        findDependencies(valueType.right)
        break
      case 'unaryOp':
        findDependencies(valueType.value)
        break
      case 'get':
        // Getting a variable does not introduce dependencies
        break
      case 'set':
        findDependencies(valueType.value)
        break
      case 'store':
        findDependencies(valueType.index)
        valueType.tuple.forEach((value) => findDependencies(value))
        break
      case 'retrieve':
        findDependencies(valueType.index)
        break
      case 'range':
        findDependencies(valueType.end)
        valueType.loopBody.forEach((instruction) =>
          findDependencies(instruction)
        )
        break
      case 'writeChar':
        findDependencies(valueType.value)
        break
      case 'subscript':
        findDependencies(valueType.value)
        break
      case 'condition':
        findDependencies(valueType.condition)
        valueType.body.forEach((instruction) => findDependencies(instruction))
        valueType.alternate.forEach((instruction) =>
          findDependencies(instruction)
        )
        break
      case 'sDivide':
      case 'divide':
      case 'less':
      case 'sLess':
        findDependencies(valueType.left)
        findDependencies(valueType.right)
        break
      case 'coerceInt8':
      case 'coerceInt16':
      case 'coerceInt32':
      case 'coerceInt64':
        findDependencies(valueType.value)
        break
      case 'call':
        valueType.presetVariables.forEach((value) => findDependencies(value))
        break
      case 'cross module call':
        dependencies.push(valueType.module)
        valueType.presetVariables.forEach((value) => findDependencies(value))
        break
      case 'break':
      case 'continue':
      case 'flush':
      case 'readChar':
        // These instructions do not introduce dependencies
        break
      default:
        consumeNever(valueType)
    }
  }
  const dependencies: string[] = []
  for (const procedure of procedures) {
    for (const instruction of procedure.body) {
      findDependencies(instruction)
    }
  }
  return dependencies
}

// Self loops aren't cyclic dependencies
const validateCyclicDependencies = (modules: CoqCPAST[]) => {
  const indexMap = new Map<string, number>()

  const existingModuleNames = modules.map((x) => x.moduleName)
  for (const [index, name] of existingModuleNames.entries()) {
    indexMap.set(name, index)
  }

  const edgeList: [number, number][] = []
  for (const [toNumber, module] of modules.entries()) {
    const dependencies = findDependencies(module).filter(
      (x) => x !== module.moduleName
    )
    for (const dependency of dependencies) {
      const fromNumber = indexMap.get(dependency)
      if (fromNumber === undefined) continue
      edgeList.push([fromNumber, toNumber])
    }
  }

  const cycle = findCycle(edgeList)

  if (cycle === undefined) return undefined

  // Error reporting
}

export const validateAST = ({
  procedures,
  environment,
}: CoqCPAST): ValidationError[] => {
  const errors: ValidationError[] = []
  if (environment !== null) {
    for (const [key, array] of (environment?.arrays || new Map()).entries()) {
      const raw = array.length.raw
      if (raw !== '0' && !/^[+-]?[1-9]\d*$/.test(raw)) {
        errors.push({
          type: 'bad number literal',
          location: array.length.location,
        })
        environment.arrays.delete(key)
        continue
      }
      const evaluated = BigInt(raw)
      if (evaluated < -(2n ** 63n) || evaluated >= 2n ** 64n) {
        errors.push({
          type: 'not representable int64',
          location: array.length.location,
        })
        environment.arrays.delete(key)
        continue
      }
      if (evaluated < 0n) {
        errors.push({
          type: "array length can't be negative",
          location: array.length.location,
        })
        environment.arrays.delete(key)
        continue
      }
    }
  }
  const procedureMap = new Map<string, Procedure>()
  for (const procedure of procedures) {
    type Type =
      | PrimitiveType
      | 'string'
      | 'statement'
      | 'illegal'
      | PrimitiveType[]
    let hasSurroundingRangeCommand = false
    const presentBinderType = new Map<string, 'int64' | 'int8'>()
    const dfs = (instruction: ValueType): Type => {
      switch (instruction.type) {
        case 'binaryOp': {
          switch (instruction.operator) {
            case 'add':
            case 'subtract':
            case 'multiply':
            case 'mod':
            case 'bitwise or':
            case 'bitwise xor':
            case 'bitwise and':
            case 'shift left':
            case 'shift right': {
              const leftType = dfs(instruction.left)
              const rightType = dfs(instruction.right)
              if (leftType === rightType && isNumeric(leftType)) return leftType
              else {
                if (leftType === 'illegal' || rightType === 'illegal')
                  return 'illegal'
                if (leftType === 'statement') {
                  errors.push({
                    type: 'expression no statement',
                    location: instruction.left.location,
                  })
                  return 'illegal'
                }
                if (rightType === 'statement') {
                  errors.push({
                    type: 'expression no statement',
                    location: instruction.right.location,
                  })
                  return 'illegal'
                }
                if (!isNumeric(leftType) || !isNumeric(rightType)) {
                  errors.push({
                    type: 'binary expression expects numeric',
                    actualType1: leftType,
                    actualType2: rightType,
                    location: instruction.location,
                  })
                  return 'illegal'
                }
                if (leftType !== rightType) {
                  errors.push({
                    type: 'binary expression type mismatch',
                    actualType1: leftType,
                    actualType2: rightType,
                    location: instruction.location,
                  })
                  return 'illegal'
                }
                return 'illegal'
              }
            }
            case 'equal':
            case 'noteq': {
              const leftType = dfs(instruction.left)
              const rightType = dfs(instruction.right)
              if (
                leftType === rightType &&
                (isNumeric(leftType) || leftType === 'bool')
              )
                return 'bool'
              else {
                if (leftType === 'illegal' || rightType === 'illegal')
                  return 'illegal'
                if (leftType === 'statement') {
                  errors.push({
                    type: 'expression no statement',
                    location: instruction.left.location,
                  })
                  return 'illegal'
                }
                if (rightType === 'statement') {
                  errors.push({
                    type: 'expression no statement',
                    location: instruction.right.location,
                  })
                  return 'illegal'
                }
                if (leftType !== rightType) {
                  errors.push({
                    type: 'binary expression type mismatch',
                    actualType1: leftType,
                    actualType2: rightType,
                    location: instruction.location,
                  })
                  return 'illegal'
                }
                return 'illegal'
              }
            }
            case 'boolean and':
            case 'boolean or': {
              const leftType = dfs(instruction.left)
              const rightType = dfs(instruction.right)
              if (leftType === rightType && leftType === 'bool') return leftType
              else {
                if (leftType === 'illegal' || rightType === 'illegal')
                  return 'illegal'
                if (leftType === 'statement') {
                  errors.push({
                    type: 'expression no statement',
                    location: instruction.left.location,
                  })
                  return 'illegal'
                }
                if (rightType === 'statement') {
                  errors.push({
                    type: 'expression no statement',
                    location: instruction.right.location,
                  })
                  return 'illegal'
                }
                if (leftType !== 'bool' || rightType !== 'bool') {
                  errors.push({
                    type: 'binary expression expects boolean',
                    actualType1: leftType,
                    actualType2: rightType,
                    location: instruction.location,
                  })
                  return 'illegal'
                }
                return 'illegal'
              }
            }
          }
        }
        case 'break': {
          if (!hasSurroundingRangeCommand) {
            errors.push({
              type: 'no surrounding range command',
              location: instruction.location,
            })
            return 'illegal'
          }
          return 'statement'
        }
        case 'call': {
          const {
            procedure: procedureName,
            presetVariables,
            location,
          } = instruction
          const procedure = procedureMap.get(procedureName)
          if (procedure === undefined) {
            errors.push({
              type: 'procedure not found',
              name: procedureName,
              location,
            })
            return 'illegal'
          }
          const { variables } = procedure

          const notPresent = [...presetVariables.keys()].filter(
            (x) => variables.get(x) === undefined
          )
          if (notPresent.length !== 0) {
            errors.push({
              type: 'variable not present',
              variables: notPresent,
              location,
            })
            return 'illegal'
          }

          let typeMismatch = false

          for (const [variableName, { type }] of variables.entries()) {
            const presetValue = presetVariables.get(variableName)
            if (presetValue === undefined) continue
            const actualType = dfs(presetValue)
            if (type !== actualType) {
              typeMismatch = true
              if (actualType === 'statement') {
                errors.push({
                  type: 'expression no statement',
                  location: presetValue.location,
                })
              } else if (actualType !== 'illegal') {
                errors.push({
                  type: 'variable type mismatch',
                  actualType,
                  expectedType: type,
                  location: presetValue.location,
                })
              }
            }
          }

          if (typeMismatch) return 'illegal'
          return 'statement'
        }
        case 'coerceInt16':
        case 'coerceInt32':
        case 'coerceInt64':
        case 'coerceInt8': {
          const type = dfs(instruction.value)
          if (type === 'illegal') return 'illegal'
          if (type === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          return instruction.type === 'coerceInt16'
            ? 'int16'
            : instruction.type === 'coerceInt32'
              ? 'int32'
              : instruction.type === 'coerceInt64'
                ? 'int64'
                : 'int8'
        }
        case 'condition': {
          const { alternate, body, condition, location } = instruction
          if (alternate.map(dfs).includes('illegal')) return 'illegal'
          if (body.map(dfs).includes('illegal')) return 'illegal'
          const conditionType = dfs(condition)
          if (conditionType === 'statement') {
            errors.push({ type: 'expression no statement', location })
            return 'illegal'
          }
          if (conditionType === 'illegal') return 'illegal'
          if (conditionType !== 'bool') {
            errors.push({
              type: 'condition must be boolean',
              actualType: conditionType,
              location,
            })
            return 'illegal'
          }
          return 'statement'
        }
        case 'continue': {
          if (!hasSurroundingRangeCommand) {
            errors.push({
              type: 'no surrounding range command',
              location: instruction.location,
            })
            return 'illegal'
          }
          return 'statement'
        }
        case 'divide':
        case 'sDivide':
        case 'less':
        case 'sLess': {
          const { left, right } = instruction
          const leftType = dfs(left)
          const rightType = dfs(right)
          if (leftType === 'illegal' || rightType === 'illegal')
            return 'illegal'
          if (leftType === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: left.location,
            })
            return 'illegal'
          }
          if (rightType === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: right.location,
            })
            return 'illegal'
          }
          if (!isNumeric(leftType) || !isNumeric(rightType)) {
            errors.push({
              type: 'instruction expects numeric',
              location: instruction.location,
              actualType1: leftType,
              actualType2: rightType,
            })
            return 'illegal'
          }
          if (leftType !== rightType) {
            errors.push({
              type: 'instruction type mismatch',
              location: instruction.location,
              actualType1: leftType,
              actualType2: rightType,
            })
            return 'illegal'
          }
          if (instruction.type === 'divide' || instruction.type === 'sDivide')
            return leftType
          else if (instruction.type === 'less' || instruction.type === 'sLess')
            return 'bool'
        }
        case 'flush':
          return 'statement'
        case 'get': {
          const { name } = instruction
          const variable = procedure.variables.get(name)
          if (variable === undefined) {
            errors.push({
              type: 'undefined variable',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (!isNumeric(variable.type) && variable.type !== 'bool')
            throw new Error(
              'unexpected! variable type not checked during parsing stage'
            )
          return variable.type
        }
        case 'literal': {
          if (instruction.valueType === 'boolean') return 'bool'
          else if (instruction.valueType === 'string') return 'string'
          else if (instruction.valueType === 'number') {
            if (
              instruction.raw !== '0' &&
              !/^[+-]?[1-9]\d*$/.test(instruction.raw)
            ) {
              errors.push({
                type: 'bad number literal',
                location: instruction.location,
              })
              return 'illegal'
            }
            const evaluated = BigInt(instruction.raw)
            if (evaluated < -(2n ** 63n) || evaluated >= 2n ** 64n) {
              errors.push({
                type: 'not representable int64',
                location: instruction.location,
              })
              return 'illegal'
            }
            return 'int64'
          }
          return consumeNever(instruction.valueType)
        }
        case 'local binder': {
          const { name } = instruction
          const binderType = presentBinderType.get(name)
          if (binderType === undefined) {
            errors.push({
              type: 'undefined binder',
              location: instruction.location,
            })
            return 'illegal'
          }
          return binderType
        }
        case 'range': {
          const { end, loopBody, loopVariable } = instruction
          const endType = dfs(end)
          if (endType === 'illegal') return 'illegal'
          if (endType === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (endType !== 'int64' && endType !== 'string') {
            errors.push({
              type: 'range end must be int64 or string',
              location: instruction.location,
            })
            return 'illegal'
          }
          const previousHasSurroundingRangeCommand = hasSurroundingRangeCommand
          hasSurroundingRangeCommand = true
          const binderTypeBefore = presentBinderType.get(loopVariable)
          presentBinderType.set(
            loopVariable,
            endType === 'string' ? 'int8' : 'int64'
          )
          const result = loopBody.map(dfs).includes('illegal')
            ? 'illegal'
            : 'statement'
          hasSurroundingRangeCommand = previousHasSurroundingRangeCommand
          if (binderTypeBefore === undefined)
            presentBinderType.delete(loopVariable)
          else presentBinderType.set(loopVariable, binderTypeBefore)
          return result
        }
        case 'readChar':
          return 'int64'
        case 'writeChar': {
          const type = dfs(instruction.value)
          if (type === 'illegal') return 'illegal'
          if (type === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (type !== 'int8') {
            errors.push({
              type: 'instruction expects int8',
              location: instruction.location,
            })
            return 'illegal'
          }
          return 'statement'
        }
        case 'retrieve': {
          const { index, name } = instruction
          const type = dfs(index)
          if (type === 'illegal') return 'illegal'
          if (type === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (type !== 'int64') {
            errors.push({
              type: 'instruction expects int64',
              location: instruction.location,
            })
            return 'illegal'
          }
          const array = environment?.arrays.get(name)
          if (array === undefined) {
            errors.push({
              type: 'undefined array',
              location: instruction.location,
            })
            return 'illegal'
          }
          // unfortunately, this step isn't too concerned with bounds checking
          // please fire up Coq
          return array.itemTypes
        }
        case 'set': {
          const { name, value } = instruction
          const actualType = dfs(value)
          const expectedType = procedure.variables.get(name)?.type
          if (expectedType === undefined) {
            errors.push({
              type: 'undefined variable',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (actualType === 'illegal') return 'illegal'
          if (actualType === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (expectedType !== actualType) {
            errors.push({
              type: 'variable type mismatch',
              expectedType,
              actualType,
              location: instruction.location,
            })
            return 'illegal'
          }
          return 'statement'
        }
        case 'store': {
          const { index, name, tuple } = instruction
          const elementType = environment?.arrays.get(name)?.itemTypes
          if (elementType === undefined) {
            errors.push({
              type: 'undefined array',
              location: instruction.location,
            })
            return 'illegal'
          }
          const actualType = tuple.map(dfs)
          const filterNotPermissible = (x: Type[]): PrimitiveType[] =>
            x.filter(
              (x): x is PrimitiveType =>
                x !== 'illegal' && x !== 'statement' && x !== 'string'
            )
          if (actualType.includes('illegal')) return 'illegal'
          for (const [index, type] of actualType.entries()) {
            if (type === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: tuple[index].location,
              })
            }
            if (type === 'string') {
              errors.push({
                type: 'string not allowed',
                location: tuple[index].location,
              })
            }
          }
          if (actualType.includes('statement')) return 'illegal'
          const coercedActualType = filterNotPermissible(actualType)
          if (tuple.length !== elementType.length) {
            errors.push({
              type: 'variable type mismatch',
              expectedType: elementType,
              actualType: coercedActualType,
              location: instruction.location,
            })
            return 'illegal'
          }
          for (const [index, type] of actualType.entries()) {
            if (type !== elementType[index]) {
              errors.push({
                type: 'variable type mismatch',
                expectedType: elementType,
                actualType: coercedActualType,
                location: instruction.location,
              })
              return 'illegal'
            }
          }
          const indexType = dfs(index)
          if (indexType === 'illegal') return 'illegal'
          if (indexType === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (indexType !== 'int64') {
            errors.push({
              type: 'instruction expects int64',
              location: instruction.location,
            })
            return 'illegal'
          }
          // no bounds check
          return 'statement'
        }
        case 'subscript': {
          const { index, value } = instruction
          const type = dfs(value)
          if (type === 'illegal') return 'illegal'
          if (type === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (!Array.isArray(type)) {
            errors.push({
              type: 'instruction expects tuple',
              location: instruction.location,
            })
            return 'illegal'
          }
          const indexType = dfs(index)
          if (indexType === 'illegal') return 'illegal'
          // now indexType is int64
          // sure, TypeScript can't infer this but it is true
          const lengthInt = BigInt(type.length)
          const indexInt = BigInt(index.raw)
          if (indexInt >= lengthInt || indexInt < 0n) {
            errors.push({
              type: 'index out of bounds',
              location: instruction.location,
            })
            return 'illegal'
          }
          const returnedType = type[Number(index.raw)]
          return returnedType
        }
        case 'unaryOp': {
          const { operator, value } = instruction
          const valueType = dfs(value)
          if (valueType === 'illegal') return 'illegal'
          if (valueType === 'statement') {
            errors.push({
              type: 'expression no statement',
              location: instruction.location,
            })
            return 'illegal'
          }
          if (isNumeric(valueType)) {
            switch (operator) {
              case 'bitwise not':
              case 'minus':
              case 'plus':
                return valueType
              case 'boolean not': {
                errors.push({
                  type: 'unary operator expects numeric',
                  location: instruction.location,
                })
                return 'illegal'
              }
            }
          }
          if (Array.isArray(valueType)) {
            errors.push({
              type: "unary operator can't operate on tuples",
              location: instruction.location,
            })
            return 'illegal'
          }
          if (valueType === 'string') {
            errors.push({
              type: "unary operator can't operate on strings",
              location: instruction.location,
            })
            return 'illegal'
          }
          if (valueType === 'bool') {
            switch (operator) {
              case 'bitwise not':
              case 'minus':
              case 'plus': {
                errors.push({
                  type: 'unary operator expects boolean',
                  location: instruction.location,
                })
                return 'illegal'
              }
              case 'boolean not':
                return 'bool'
            }
          }
          return consumeNever(valueType)
        }
      }
    }
    procedure.body.forEach(dfs)
    procedureMap.set(procedure.name, procedure)
  }
  return errors
}
