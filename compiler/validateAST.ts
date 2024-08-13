import { PairMap } from './PairMap'
import { consumeNever } from './consumeNever'
import { sortModules, validateCyclicDependencies } from './dependencyGraph'
import {
  ValueType,
  Procedure,
  PrimitiveType,
  CoqCPAST,
  Location,
  COMMUNICATION,
} from './parse'

export type ValidationError =
  | ((
    | {
      type:
      | 'binary expression expects numeric'
      | 'instruction expects numeric'
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
    | { type: 'module not found'; name: string }
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
      | 'instruction expects address'
      | 'instruction expects int256'
      | 'instruction expects tuple'
      | 'instruction expects address or tuple'
    }
    | { type: 'instruction expects [int8] array' }
    | { type: 'instruction only available in blockchain environment' }
    | { type: 'instruction not available in blockchain environment' }
    | { type: 'undefined array' }
    | { type: 'index out of bounds' }
    | {
      type:
      | 'unary operator expects numeric'
      | "unary operator can't operate on tuples"
      | "unary operator can't operate on strings"
      | "unary operator can't operate on addresses"
      | 'unary operator expects boolean'
    }
    | { type: "array length can't be less than 1" }
    | { type: 'string not allowed' }
    | { type: 'call implicated in cycle' }
    | { type: 'must specify all arrays' }
    | {
      type: 'array shape mismatch'
      procedureModuleArrayShape: PrimitiveType[]
      currentModuleArrayShape: PrimitiveType[]
    }
    | {
      type:
      | 'array shape mismatch'
      | "array doesn't exist in procedure module"
      procedureModuleArray: string
    }
    | {
      type: "array doesn't exist in current module"
      currentModuleArray: string
    }
    | { type: 'duplicate procedure'; procedureName: string }
    | { type: 'index must be a number literal' }
  ) & { location: Location & { moduleName: string } })
  | { type: 'duplicate module'; module: CoqCPAST; moduleName: string }

export const isNumeric = (
  x: string | PrimitiveType[]
): x is 'int8' | 'int16' | 'int32' | 'int64' | 'int256' => {
  return (
    x === 'int8' ||
    x === 'int16' ||
    x === 'int32' ||
    x === 'int64' ||
    x === 'int256'
  )
}

export const sortAndValidateAST = (
  modules: CoqCPAST[],
  blockchain: boolean
): ValidationError[] => {
  const sortedModules = sortModules(modules)
  return validateAST(sortedModules, blockchain)
}

export const validateAST = (
  sortedModules: CoqCPAST[],
  blockchain: boolean
): ValidationError[] => {
  // Check for duplicate modules
  {
    const errors: ValidationError[] = []
    const names = sortedModules.map((x) => x.moduleName).sort()
    const mapNameToModule = new Map<string, CoqCPAST[]>()
    sortedModules.map((x) => {
      const array = mapNameToModule.get(x.moduleName)
      if (array === undefined) mapNameToModule.set(x.moduleName, [x])
      else array.push(x)
    })
    const n = names.length
    let cursor = 0
    while (cursor !== n) {
      let next = cursor
      while (next !== n && names[next] === names[cursor]) next++
      if (next - cursor > 1) {
        for (const module of mapNameToModule.get(names[cursor])!)
          errors.push({
            type: 'duplicate module',
            module,
            moduleName: names[cursor],
          })
      }
      cursor = next
    }
    if (errors.length) return errors
  }

  const cyclicDependencyCheck = validateCyclicDependencies(sortedModules)
  if (cyclicDependencyCheck.length) return cyclicDependencyCheck

  const crossModuleProcedureMap = new PairMap<string, string, Procedure>()
  const seenModules = new Map<string, CoqCPAST>()

  const errors: ValidationError[] = []

  for (const currentModule of sortedModules) {
    const { environment, procedures, moduleName } = currentModule
    seenModules.set(moduleName, currentModule)
    if (environment !== null) {
      for (const [key, array] of (environment?.arrays || new Map()).entries()) {
        const raw = array.length.raw
        if (raw !== '0' && !/^[+-]?[1-9]\d*$/.test(raw)) {
          errors.push({
            type: 'bad number literal',
            location: { ...array.length.location, moduleName },
          })
          environment.arrays.delete(key)
          continue
        }
        const evaluated = BigInt(raw)
        if (evaluated < -(2n ** 63n) || evaluated >= 2n ** 64n) {
          errors.push({
            type: 'not representable int64',
            location: { ...array.length.location, moduleName },
          })
          environment.arrays.delete(key)
          continue
        }
        if (evaluated < 1n) {
          errors.push({
            type: "array length can't be less than 1",
            location: { ...array.length.location, moduleName },
          })
          environment.arrays.delete(key)
          continue
        }
      }
    }
    const procedureMap = new Map<string, Procedure>()
    for (const procedure of procedures) {
      if (procedureMap.has(procedure.name)) {
        errors.push({
          type: 'duplicate procedure',
          procedureName: procedure.name,
          location: { ...procedure.nameLocation, moduleName },
        })
        continue
      }
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
                if (leftType === rightType && isNumeric(leftType))
                  return leftType
                else {
                  if (leftType === 'illegal' || rightType === 'illegal')
                    return 'illegal'
                  if (leftType === 'statement') {
                    errors.push({
                      type: 'expression no statement',
                      location: { ...instruction.left.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (rightType === 'statement') {
                    errors.push({
                      type: 'expression no statement',
                      location: { ...instruction.right.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (!isNumeric(leftType) || !isNumeric(rightType)) {
                    errors.push({
                      type: 'binary expression expects numeric',
                      actualType1: leftType,
                      actualType2: rightType,
                      location: { ...instruction.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (leftType !== rightType) {
                    errors.push({
                      type: 'binary expression type mismatch',
                      actualType1: leftType,
                      actualType2: rightType,
                      location: { ...instruction.location, moduleName },
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
                  (isNumeric(leftType) ||
                    leftType === 'bool' ||
                    leftType === 'address')
                )
                  return 'bool'
                else {
                  if (leftType === 'illegal' || rightType === 'illegal')
                    return 'illegal'
                  if (leftType === 'statement') {
                    errors.push({
                      type: 'expression no statement',
                      location: { ...instruction.left.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (rightType === 'statement') {
                    errors.push({
                      type: 'expression no statement',
                      location: { ...instruction.right.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (leftType !== rightType) {
                    errors.push({
                      type: 'binary expression type mismatch',
                      actualType1: leftType,
                      actualType2: rightType,
                      location: { ...instruction.location, moduleName },
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
                if (leftType === rightType && leftType === 'bool')
                  return leftType
                else {
                  if (leftType === 'illegal' || rightType === 'illegal')
                    return 'illegal'
                  if (leftType === 'statement') {
                    errors.push({
                      type: 'expression no statement',
                      location: { ...instruction.left.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (rightType === 'statement') {
                    errors.push({
                      type: 'expression no statement',
                      location: { ...instruction.right.location, moduleName },
                    })
                    return 'illegal'
                  }
                  if (leftType !== 'bool' || rightType !== 'bool') {
                    errors.push({
                      type: 'binary expression expects boolean',
                      actualType1: leftType,
                      actualType2: rightType,
                      location: { ...instruction.location, moduleName },
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
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'statement'
          }
          case 'call':
            function validateCall(
              procedure: Procedure,
              presetVariables: Map<string, ValueType>,
              location: Location
            ): 'statement' | 'illegal' {
              const { variables } = procedure

              const notPresent = [...presetVariables.keys()].filter(
                (x) => variables.get(x) === undefined
              )
              if (notPresent.length !== 0) {
                errors.push({
                  type: 'variable not present',
                  variables: notPresent,
                  location: { ...location, moduleName },
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
                      location: { ...presetValue.location, moduleName },
                    })
                  } else if (actualType !== 'illegal') {
                    errors.push({
                      type: 'variable type mismatch',
                      actualType,
                      expectedType: type,
                      location: { ...presetValue.location, moduleName },
                    })
                  }
                }
              }

              if (typeMismatch) return 'illegal'
              return 'statement'
            }
            {
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
                  location: { ...location, moduleName },
                })
                return 'illegal'
              }
              return validateCall(procedure, presetVariables, location)
            }
          case 'cross module call': {
            const {
              arrayMapping,
              procedure: procedureName,
              presetVariables,
              location,
              module: procedureModuleName,
            } = instruction
            if (!seenModules.has(procedureModuleName)) {
              errors.push({
                type: 'module not found',
                name: procedureModuleName,
                location: { ...location, moduleName },
              })
              return 'illegal'
            }

            const procedure = crossModuleProcedureMap.get([
              procedureModuleName,
              procedureName,
            ])

            if (procedure === undefined) {
              errors.push({
                type: 'procedure not found',
                name: procedureName,
                location: { ...location, moduleName },
              })
              return 'illegal'
            }

            const basicCheck = validateCall(
              procedure,
              presetVariables,
              location
            )

            if (basicCheck === 'illegal') return 'illegal'

            const procedureModule = seenModules.get(procedureModuleName)!

            if (
              arrayMapping.size <
              (procedureModule.environment?.arrays.size ?? 0)
            ) {
              errors.push({
                type: 'must specify all arrays',
                location: { ...location, moduleName },
              })
              return 'illegal'
            }

            for (const [
              procedureModuleArray,
              currentModuleArray,
            ] of arrayMapping.entries()) {
              const procedureModuleArrayDeclaration =
                procedureModule.environment?.arrays.get(procedureModuleArray)
              const currentModuleArrayDeclaration =
                currentModule.environment?.arrays.get(currentModuleArray)
              if (procedureModuleArrayDeclaration === undefined) {
                errors.push({
                  type: "array doesn't exist in procedure module",
                  procedureModuleArray,
                  location: { ...location, moduleName },
                })
                return 'illegal'
              }
              if (currentModuleArrayDeclaration === undefined) {
                errors.push({
                  type: "array doesn't exist in current module",
                  currentModuleArray,
                  location: { ...location, moduleName },
                })
                return 'illegal'
              }
              if (
                currentModuleArrayDeclaration.itemTypes.length !==
                procedureModuleArrayDeclaration.itemTypes.length ||
                currentModuleArrayDeclaration.itemTypes.some(
                  (element, index) =>
                    procedureModuleArrayDeclaration.itemTypes[index] !== element
                )
              ) {
                errors.push({
                  type: 'array shape mismatch',
                  procedureModuleArrayShape:
                    procedureModuleArrayDeclaration.itemTypes,
                  currentModuleArrayShape:
                    currentModuleArrayDeclaration.itemTypes,
                  location: { ...location, moduleName },
                })
                return 'illegal'
              }
            }

            return 'statement'
          }
          case 'coerceInt256':
          case 'coerceInt16':
          case 'coerceInt32':
          case 'coerceInt64':
          case 'coerceInt8': {
            const type = dfs(instruction.value)
            if (type === 'illegal') return 'illegal'
            if (type === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return instruction.type === 'coerceInt16'
              ? 'int16'
              : instruction.type === 'coerceInt32'
                ? 'int32'
                : instruction.type === 'coerceInt64'
                  ? 'int64'
                  : instruction.type === 'coerceInt256'
                    ? 'int256'
                    : 'int8'
          }
          case 'condition': {
            const { alternate, body, condition, location } = instruction
            if (alternate.map(dfs).includes('illegal')) return 'illegal'
            if (body.map(dfs).includes('illegal')) return 'illegal'
            const conditionType = dfs(condition)
            if (conditionType === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...location, moduleName },
              })
              return 'illegal'
            }
            if (conditionType === 'illegal') return 'illegal'
            if (conditionType !== 'bool') {
              errors.push({
                type: 'condition must be boolean',
                actualType: conditionType,
                location: { ...location, moduleName },
              })
              return 'illegal'
            }
            return 'statement'
          }
          case 'continue': {
            if (!hasSurroundingRangeCommand) {
              errors.push({
                type: 'no surrounding range command',
                location: { ...instruction.location, moduleName },
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
                location: { ...left.location, moduleName },
              })
              return 'illegal'
            }
            if (rightType === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...right.location, moduleName },
              })
              return 'illegal'
            }
            if (!isNumeric(leftType) || !isNumeric(rightType)) {
              errors.push({
                type: 'instruction expects numeric',
                location: { ...instruction.location, moduleName },
                actualType1: leftType,
                actualType2: rightType,
              })
              return 'illegal'
            }
            if (leftType !== rightType) {
              errors.push({
                type: 'instruction type mismatch',
                location: { ...instruction.location, moduleName },
                actualType1: leftType,
                actualType2: rightType,
              })
              return 'illegal'
            }
            if (instruction.type === 'divide' || instruction.type === 'sDivide')
              return leftType
            else if (
              instruction.type === 'less' ||
              instruction.type === 'sLess'
            )
              return 'bool'
          }
          case 'flush': {
            if (blockchain) {
              errors.push({
                type: 'instruction not available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'statement'
          }
          case 'get': {
            const { name } = instruction
            const variable = procedure.variables.get(name)
            if (variable === undefined) {
              errors.push({
                type: 'undefined variable',
                location: { ...instruction.location, moduleName },
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
                  location: { ...instruction.location, moduleName },
                })
                return 'illegal'
              }
              const evaluated = BigInt(instruction.raw)
              if (evaluated < -(2n ** 63n) || evaluated >= 2n ** 64n) {
                errors.push({
                  type: 'not representable int64',
                  location: { ...instruction.location, moduleName },
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
                location: { ...instruction.location, moduleName },
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
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (endType !== 'int64' && endType !== 'string') {
              errors.push({
                type: 'range end must be int64 or string',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            const previousHasSurroundingRangeCommand =
              hasSurroundingRangeCommand
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
          case 'readChar': {
            if (blockchain) {
              errors.push({
                type: 'instruction not available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'int64'
          }
          case 'writeChar': {
            if (blockchain) {
              errors.push({
                type: 'instruction not available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            const type = dfs(instruction.value)
            if (type === 'illegal') return 'illegal'
            if (type === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (type !== 'int8') {
              errors.push({
                type: 'instruction expects int8',
                location: { ...instruction.location, moduleName },
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
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (type !== 'int64') {
              errors.push({
                type: 'instruction expects int64',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (name === COMMUNICATION) {
              if (!blockchain) {
                errors.push({
                  type: 'instruction only available in blockchain environment',
                  location: { ...instruction.location, moduleName },
                })
                return 'illegal'
              }
              return 'int8'
            }
            const array = environment?.arrays.get(name)
            if (array === undefined) {
              errors.push({
                type: 'undefined array',
                location: { ...instruction.location, moduleName },
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
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (actualType === 'illegal') return 'illegal'
            if (actualType === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (expectedType !== actualType) {
              errors.push({
                type: 'variable type mismatch',
                expectedType,
                actualType,
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'statement'
          }
          case 'store': {
            const { index, name } = instruction
            const indexType = dfs(index)
            let invalid = false
            if (indexType === 'illegal') return 'illegal'
            if (indexType === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...instruction.location, moduleName },
              })
              invalid = true
            }
            if (indexType !== 'int64') {
              errors.push({
                type: 'instruction expects int64',
                location: { ...instruction.location, moduleName },
              })
              invalid = true
            }
            if (name === COMMUNICATION) {
              if (!blockchain) {
                errors.push({
                  type: 'instruction only available in blockchain environment',
                  location: { ...instruction.location, moduleName },
                })
                return 'illegal'
              }
              if (invalid) return 'illegal'
              return 'int8'
            }
            const { tuple } = instruction
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
                  location: { ...tuple[index].location, moduleName },
                })
              }
              if (type === 'string') {
                errors.push({
                  type: 'string not allowed',
                  location: { ...tuple[index].location, moduleName },
                })
              }
            }
            if (actualType.includes('statement')) return 'illegal'
            const coercedActualType = filterNotPermissible(actualType)
            const elementType = environment?.arrays.get(name)?.itemTypes
            if (elementType === undefined) {
              errors.push({
                type: 'undefined array',
                location: { ...instruction.location, moduleName },
              })
              invalid = true
              return 'illegal'
            }
            if (tuple.length !== elementType.length) {
              errors.push({
                type: 'variable type mismatch',
                expectedType: elementType,
                actualType: coercedActualType,
                location: { ...instruction.location, moduleName },
              })
              invalid = true
            }
            for (const [index, type] of actualType.entries()) {
              if (type !== elementType[index]) {
                errors.push({
                  type: 'variable type mismatch',
                  expectedType: elementType,
                  actualType: coercedActualType,
                  location: { ...instruction.location, moduleName },
                })
                invalid = true
              }
            }
            if (invalid) return 'illegal'
            return 'statement'
          }
          case 'subscript': {
            const { index, value } = instruction
            const type = dfs(value)
            if (type === 'illegal') return 'illegal'
            if (type === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...value.location, moduleName },
              })
              return 'illegal'
            }
            if (Array.isArray(type)) {
              const indexType = dfs(index)
              if (indexType === 'illegal') return 'illegal'
              const lengthInt = BigInt(type.length)

              if (index.type !== 'literal' || index.valueType !== 'number') {
                errors.push({
                  type: 'index must be a number literal',
                  location: { ...index.location, moduleName },
                })
                return 'illegal'
              }

              const indexInt = BigInt(index.raw)
              if (indexInt >= lengthInt || indexInt < 0n) {
                errors.push({
                  type: 'index out of bounds',
                  location: { ...index.location, moduleName },
                })
                return 'illegal'
              }
              const returnedType = type[Number(index.raw)]
              return returnedType
            }

            if (type === 'address' && blockchain) {
              const indexType = dfs(index)
              if (indexType === 'illegal') return 'illegal'
              if (indexType !== 'int64') {
                errors.push({
                  type: 'instruction expects int64',
                  location: { ...index.location, moduleName },
                })
              }
              return 'int8'
            }

            errors.push({
              type: blockchain
                ? 'instruction expects address or tuple'
                : 'instruction expects tuple',
              location: { ...instruction.location, moduleName },
            })
            return 'illegal'
          }
          case 'unaryOp': {
            const { operator, value } = instruction
            const valueType = dfs(value)
            if (valueType === 'illegal') return 'illegal'
            if (valueType === 'statement') {
              errors.push({
                type: 'expression no statement',
                location: { ...instruction.location, moduleName },
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
                    location: { ...instruction.location, moduleName },
                  })
                  return 'illegal'
                }
              }
            }
            if (Array.isArray(valueType)) {
              errors.push({
                type: "unary operator can't operate on tuples",
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (valueType === 'string') {
              errors.push({
                type: "unary operator can't operate on strings",
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            if (valueType === 'address') {
              errors.push({
                type: "unary operator can't operate on addresses",
                location: { ...instruction.location, moduleName },
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
                    location: { ...instruction.location, moduleName },
                  })
                  return 'illegal'
                }
                case 'boolean not':
                  return 'bool'
              }
            }
            return consumeNever(valueType)
          }
          case 'get sender': {
            if (!blockchain) {
              errors.push({
                type: 'instruction only available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'address'
          }
          case 'communication area size': {
            if (!blockchain) {
              errors.push({
                type: 'instruction only available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'int64'
          }
          case 'get money': {
            if (!blockchain) {
              errors.push({
                type: 'instruction only available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            return 'int256'
          }
          case 'construct address': {
            if (!blockchain) {
              errors.push({
                type: 'instruction only available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            let invalid = false
            for (const byte of instruction.bytes) {
              const type = dfs(byte)
              if (type === 'illegal') invalid = true
              else if (type !== 'int8') {
                invalid = true
                errors.push({
                  type: 'instruction expects int8',
                  location: { ...byte.location, moduleName },
                })
              }
            }
            if (invalid) return 'illegal'
            return 'address'
          }
          case 'donate': {
            if (!blockchain) {
              errors.push({
                type: 'instruction only available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            let invalid = false
            const { money, address } = instruction
            const moneyType = dfs(money)
            const addressType = dfs(address)
            if (moneyType === 'illegal') invalid = true
            else if (moneyType !== 'int256') {
              invalid = true
              errors.push({
                type: 'instruction expects int256',
                location: { ...money.location, moduleName },
              })
            }
            if (addressType === 'illegal') invalid = true
            else if (addressType !== 'address') {
              invalid = true
              errors.push({
                type: 'instruction expects address',
                location: { ...address.location, moduleName },
              })
            }
            if (invalid) return 'illegal'
            return 'statement'
          }
          case 'invoke': {
            if (!blockchain) {
              errors.push({
                type: 'instruction only available in blockchain environment',
                location: { ...instruction.location, moduleName },
              })
              return 'illegal'
            }
            let invalid = false
            const { money, address, array, communicationSize } = instruction
            const moneyType = dfs(money)
            const addressType = dfs(address)
            const communicationSizeType = dfs(communicationSize)
            if (moneyType === 'illegal') invalid = true
            else if (moneyType !== 'int256') {
              invalid = true
              errors.push({
                type: 'instruction expects int256',
                location: { ...money.location, moduleName },
              })
            }
            if (addressType === 'illegal') invalid = true
            else if (addressType !== 'address') {
              invalid = true
              errors.push({
                type: 'instruction expects address',
                location: { ...address.location, moduleName },
              })
            }
            if (communicationSizeType === 'illegal') invalid = true
            else if (communicationSizeType !== 'int64') {
              invalid = true
              errors.push({
                type: 'instruction expects int64',
                location: { ...communicationSize.location, moduleName }
              })
            }
            const environmentArray = environment?.arrays.get(array)
            if (environmentArray === undefined) {
              invalid = true
              errors.push({
                type: 'undefined array',
                location: { ...instruction.location, moduleName },
              })
            } else {
              if (
                environmentArray.itemTypes.length !== 1 ||
                environmentArray.itemTypes[0] !== 'int8'
              ) {
                invalid = true
                errors.push({
                  type: 'instruction expects [int8] array',
                  location: { ...instruction.location, moduleName },
                })
              }
            }
            if (invalid) return 'illegal'
            return 'statement'
          }
        }
      }
      procedure.body.forEach(dfs)
      procedureMap.set(procedure.name, procedure)
      crossModuleProcedureMap.set([moduleName, procedure.name], procedure)
    }
  }
  return errors
}
