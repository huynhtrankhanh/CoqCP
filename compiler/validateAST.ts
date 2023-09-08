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
      type: 'binary expression expects numeric'
      actualType1: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
      actualType2: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
    }
  | {
      type: 'binary expression expects boolean'
      actualType1: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
      actualType2: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
    }
  | {
      type: 'binary expression type mismatch'
      actualType1: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
      actualType2: 'int8' | 'int16' | 'int32' | 'int64' | 'boolean'
    }
  | { type: 'expression no statement' }
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
        case 'break':
          return 'statement'
        case 'call': {
        }
      }
    }
    procedureMap.set(procedure.name, procedure)
  }
}
