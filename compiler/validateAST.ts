import {
  UnaryOp,
  ValueType,
  BinaryOp,
  Procedure,
  PrimitiveType,
  Instruction,
  Environment,
  BinaryOperationInstruction,
  UnaryOperationInstruction,
  CoqCPAST,
  Location,
} from './parse'

type ValidationError = (
  | {
      type: 'binary expression expects numeric' | 'instruction expects numeric'
      actualType1: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
      actualType2: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
    }
  | {
      type: 'binary expression expects boolean'
      actualType1: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
      actualType2: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
    }
  | {
      type: 'binary expression type mismatch' | 'instruction type mismatch'
      actualType1: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
      actualType2: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
    }
  | { type: 'expression no statement' }
  | { type: 'procedure not found'; name: string }
  | { type: 'preset variable not present'; variables: string[] }
  | {
      type: 'preset variable type mismatch'
      expectedType: string
      actualType: string
    }
  | { type: 'condition must be boolean'; actualType: string }
  | { type: 'no surrounding range command' }
  | { type: 'undefined variable' }
  | { type: 'not representable int64' }
  | { type: 'bad number literal' }
) & { location: Location }

const validateAST = ({
  procedures,
  environment,
}: CoqCPAST): ValidationError[] => {
  const errors: ValidationError[] = []
  const procedureMap = new Map<string, Procedure>()
  for (const procedure of procedures) {
    type Type =
      | 'int8'
      | 'int16'
      | 'int32'
      | 'int64'
      | 'boolean'
      | 'statement'
      | 'illegal'
    const isNumeric = (
      x: string
    ): x is 'int8' | 'int16' | 'int32' | 'int64' => {
      return x === 'int8' || x === 'int16' || x === 'int32' || x === 'int64'
    }
    let hasSurroundingRangeCommand = false
    const binderType = new Map<string, string>()
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
                (isNumeric(leftType) || leftType === 'boolean')
              )
                return leftType
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
              if (leftType === rightType && leftType === 'boolean')
                return leftType
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
                if (leftType !== 'boolean' || rightType !== 'boolean') {
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
              type: 'preset variable not present',
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
                  type: 'preset variable type mismatch',
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
          if (conditionType !== 'boolean') {
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
        case 'less': {
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
          if (instruction.type === 'divide') return leftType
          else if (instruction.type === 'less') return 'boolean'
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
          if (!isNumeric(variable.type) && variable.type !== 'boolean')
            throw new Error(
              'unexpected! variable type not checked during parsing stage'
            )
          return variable.type
        }
        case 'literal': {
          if (instruction.valueType === 'boolean') return 'boolean'
          else if (instruction.valueType === 'number') {
            if (
              instruction.raw !== '0' &&
              !/^[1-9]\d*$/.test(instruction.raw)
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
        }
        case 'local binder': {
        }
      }
    }
    procedureMap.set(procedure.name, procedure)
  }
  return errors
}
