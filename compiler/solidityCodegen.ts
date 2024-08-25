import { PairMap } from './PairMap'
import { assert } from './assert'
import { consumeNever } from './consumeNever'
import isPure from './isPure'
import {
  CoqCPAST,
  Procedure,
  ValueType,
  Instruction,
  PrimitiveType,
  BinaryOp,
  UnaryOp,
  COMMUNICATION,
} from './parse'

const indent = '    '

export const solidityCodegen = (sortedModules: CoqCPAST[]): string => {
  const crossModuleProcedureMap = new PairMap<string, string, Procedure>()
  const procedureNameMap = new PairMap<string, string, number>()
  const seenModules = new Map<string, CoqCPAST>()
  const mainModule = sortedModules.find((x) => x.moduleName === '')

  let joined =
    '// SPDX-License-Identifier: UNLICENSED\npragma solidity ^0.8.0;\n\n'

  // Generate structs for unique tuple types
  const structTypes = new Map<string, string>()
  let structCounter = 0

  const generateStructType = (types: PrimitiveType[]): string => {
    const typeString = types.map(solTypeName).join(',')
    if (!structTypes.has(typeString)) {
      const structName = `Tuple${structCounter++}`
      let struct = indent + `struct ${structName} {\n`
      types.forEach((type, index) => {
        struct += indent + `${indent}${solTypeName(type)} item${index};\n`
      })
      struct += indent + '}\n\n'
      joined += struct
      structTypes.set(typeString, structName)
    }
    return structTypes.get(typeString)!
  }

  joined += `contract SelfDestructContract {
    constructor(address payable _target) payable {
        // Transfer all the ether stored in this contract to the target address and self-destruct
        selfdestruct(_target);
    }
}
  
contract GeneratedCode {
    function constructAddress(
        uint8 p0, uint8 p1, uint8 p2, uint8 p3, uint8 p4,
        uint8 p5, uint8 p6, uint8 p7, uint8 p8, uint8 p9,
        uint8 p10, uint8 p11, uint8 p12, uint8 p13, uint8 p14,
        uint8 p15, uint8 p16, uint8 p17, uint8 p18, uint8 p19
    ) private pure returns (address) {
        bytes memory packed = abi.encodePacked(
            p0, p1, p2, p3, p4, p5, p6, p7, p8, p9,
            p10, p11, p12, p13, p14, p15, p16, p17, p18, p19
        );
        return address(bytes20(packed));
    }

    function shoot(address payable _target, uint256 _wei) private {
        new SelfDestructContract{value: _wei}(_target);
    }

`

  const solTypeName = (type: PrimitiveType): string => {
    switch (type) {
      case 'bool':
        return 'bool'
      case 'int8':
        return 'uint8'
      case 'int16':
        return 'uint16'
      case 'int32':
        return 'uint32'
      case 'int64':
        return 'uint64'
      case 'int256':
        return 'uint256'
      case 'address':
        return 'address'
      default:
        return consumeNever(type)
    }
  }

  const binaryOpToSolidity = (op: BinaryOp): string => {
    switch (op) {
      case 'add':
        return '+'
      case 'subtract':
        return '-'
      case 'multiply':
        return '*'
      case 'mod':
        return '%'
      case 'bitwise or':
        return '|'
      case 'bitwise xor':
        return '^'
      case 'bitwise and':
        return '&'
      case 'boolean and':
        return '&&'
      case 'boolean or':
        return '||'
      case 'shift right':
        return '>>'
      case 'shift left':
        return '<<'
      case 'equal':
        return '=='
      case 'noteq':
        return '!='
      default:
        return consumeNever(op)
    }
  }

  const unaryOpToSolidity = (op: UnaryOp): string => {
    switch (op) {
      case 'minus':
        return '-'
      case 'plus':
        return '+'
      case 'bitwise not':
        return '~'
      case 'boolean not':
        return '!'
      default:
        return consumeNever(op)
    }
  }

  // Generate storage variables for main module arrays
  if (mainModule && mainModule.environment) {
    for (const [name, description] of mainModule.environment.arrays) {
      const { itemTypes, length } = description
      const structType = generateStructType(itemTypes)
      joined += `${indent}${structType}[${length.raw}] public ${name};\n`
    }
  }

  joined += '\n'

  for (const module of sortedModules) {
    const { environment, procedures } = module
    const environmentNameMap = new Map<string, number>()
    if (environment !== null)
      for (const [index, name] of [...environment.arrays.keys()].entries()) {
        environmentNameMap.set(name, index)
      }

    // Define functions
    for (const procedure of procedures) {
      const { name, body, variables } = procedure
      const index = procedureNameMap.size()
      procedureNameMap.set([module.moduleName, name], index)
      crossModuleProcedureMap.set([module.moduleName, name], procedure)

      const envParams = environment
        ? [...environment.arrays.entries()].map(([_, description], index) => {
            const structType = generateStructType(description.itemTypes)
            return `${structType}[] memory environment${index}`
          })
        : []

      const localVariableIndex = new Map<string, number>()
      const localBinderMap = new Map<string, number>()

      for (const [index, variableName] of [...variables.keys()].entries()) {
        localVariableIndex.set(variableName, index)
      }

      const varParams = [...variables].map(
        ([_, value], index) => `${solTypeName(value.type)} local${index}`
      )

      const allParams = [
        ...envParams,
        ...varParams,
        'bytes memory communication',
      ].join(', ')

      joined += `${indent}function procedure${index}(${allParams}) private { unchecked {\n`

      // Generate function body
      const generateInstruction = (
        instruction: Instruction,
        inBlock:
          | { type: 'inside block'; indentLevel: number }
          | { type: 'not in block' } = {
          type: 'not in block',
        }
      ): string => {
        const adorn = (x: string): string => {
          if (inBlock.type === 'not in block') return x
          return indent.repeat(inBlock.indentLevel) + x + ';\n'
        }
        switch (instruction.type) {
          case 'get':
            return adorn(`local${localVariableIndex.get(instruction.name)}`)
          case 'set':
            return adorn(
              `local${localVariableIndex.get(
                instruction.name
              )} = ${generateValueType(instruction.value)}`
            )
          case 'store':
            if (instruction.name === COMMUNICATION) {
              return adorn(
                `communication[${generateValueType(
                  instruction.index
                )}] = ${generateValueType(instruction.value)}`
              )
            }
            const elementType = environment?.arrays.get(
              instruction.name
            )?.itemTypes
            assert(elementType !== undefined)
            const structType = generateStructType(elementType)
            return adorn(
              `environment${environmentNameMap.get(
                instruction.name
              )}[${generateValueType(
                instruction.index
              )}] = ${structType}(${instruction.tuple
                .map(generateValueType)
                .join(', ')})`
            )
          case 'retrieve':
            if (instruction.name === COMMUNICATION) {
              return adorn(
                `communication[${generateValueType(instruction.index)}]`
              )
            }
            return adorn(
              `environment${environmentNameMap.get(
                instruction.name
              )}[${generateValueType(instruction.index)}]`
            )
          case 'communication area size':
            return adorn(`msg.data.length`)
          case 'invoke': {
            assert(inBlock.type === 'inside block')
            const currentIndent = indent.repeat(inBlock.indentLevel)
            return `${currentIndent}{
${currentIndent}${indent}uint64 communicationSize = ${generateValueType(
              instruction.communicationSize
            )};
${currentIndent}${indent}(bool success, bytes memory returnData) = address(${generateValueType(
              instruction.address
            )}).call{value: ${generateValueType(
              instruction.money
            )}}(environment${environmentNameMap.get(
              instruction.array
            )}[0:communicationSize]);
${currentIndent}${indent}for (uint i = 0; i < communicationSize && i < returnData.length; i++)
${currentIndent}${indent}${indent}environment${environmentNameMap.get(
              instruction.array
            )}[i] = returnData[i];
${currentIndent}}\n`
          }
          case 'donate':
            return adorn(
              `shoot(${generateValueType(
                instruction.address
              )}, ${generateValueType(instruction.money)})`
            )
          case 'get sender':
            return adorn(`msg.sender`)
          case 'get money':
            return adorn(`msg.value`)
          case 'range': {
            if (
              instruction.end.type === 'literal' &&
              instruction.end.valueType === 'string'
            ) {
              return 'bananas'
            }
            const previous = localBinderMap.get(instruction.loopVariable)
            const localBinderIndex = localBinderMap.size
            localBinderMap.set(instruction.loopVariable, localBinderMap.size)
            assert(inBlock.type === 'inside block')
            const currentIndent = indent.repeat(inBlock.indentLevel)
            const expression =
              `${currentIndent}for (uint64 binder${localBinderIndex} = 0; ${
                instruction.loopVariable
              } < ${generateValueType(instruction.end)}; ${
                instruction.loopVariable
              }++) {\n` +
              instruction.loopBody
                .map((i) =>
                  generateInstruction(i, {
                    type: 'inside block',
                    indentLevel: inBlock.indentLevel + 1,
                  })
                )
                .join('') +
              `${currentIndent}}\n`
            if (previous === undefined)
              localBinderMap.delete(instruction.loopVariable)
            else localBinderMap.set(instruction.loopVariable, previous)
            return expression
          }
          case 'readChar':
          case 'writeChar':
          case 'flush':
            return `revert("Operation not supported in Solidity");\n`
          case 'binaryOp':
            return adorn(
              `(${generateValueType(instruction.left)} ${binaryOpToSolidity(
                instruction.operator
              )} ${generateValueType(instruction.right)})`
            )
          case 'unaryOp':
            return adorn(
              `(${unaryOpToSolidity(instruction.operator)}${generateValueType(
                instruction.value
              )})`
            )
          case 'subscript': {
            const isTuple = instruction.value.type === 'retrieve'
            if (isTuple) {
              assert(instruction.index.type === 'literal')
              return adorn(
                `${generateValueType(instruction.value)}.item${
                  instruction.index.raw
                }`
              )
            } else {
              return adorn(`${generateValueType(instruction.value)}`)
            }
          }
          case 'condition': {
            assert(inBlock.type === 'inside block')
            const currentIndent = indent.repeat(inBlock.indentLevel)
            return (
              `${currentIndent}if (${generateValueType(
                instruction.condition
              )}) {\n` +
              instruction.body
                .map((i) =>
                  generateInstruction(i, {
                    type: 'inside block',
                    indentLevel: inBlock.indentLevel + 1,
                  })
                )
                .join('') +
              `${currentIndent}} else {\n` +
              instruction.alternate
                .map((i) =>
                  generateInstruction(i, {
                    type: 'inside block',
                    indentLevel: inBlock.indentLevel + 1,
                  })
                )
                .join('') +
              `${currentIndent}}\n`
            )
          }
          case 'sDivide':
            return adorn(
              `(toSigned(${generateValueType(
                instruction.left
              )}) / toSigned(${generateValueType(instruction.right)}))`
            )
          case 'divide':
            return adorn(
              `(${generateValueType(instruction.left)} / ${generateValueType(
                instruction.right
              )})`
            )
          case 'coerceInt8':
            return adorn(`uint8(${generateValueType(instruction.value)})`)
          case 'coerceInt16':
            return adorn(`uint16(${generateValueType(instruction.value)})`)
          case 'coerceInt32':
            return adorn(`uint32(${generateValueType(instruction.value)})`)
          case 'coerceInt64':
            return adorn(`uint64(${generateValueType(instruction.value)})`)
          case 'coerceInt256':
            return adorn(`uint256(${generateValueType(instruction.value)})`)
          case 'less':
            return adorn(
              `(${generateValueType(instruction.left)} < ${generateValueType(
                instruction.right
              )})`
            )
          case 'sLess':
            return adorn(
              `(toSigned(${generateValueType(
                instruction.left
              )}) < toSigned(${generateValueType(instruction.right)}))`
            )
          case 'call': {
            const arrays = Array.from({
              length: environment?.arrays?.size || 0,
            }).map((_, i) => 'environment' + i)
            const procedure = crossModuleProcedureMap.get([
              module.moduleName,
              instruction.procedure,
            ])
            assert(procedure !== undefined)
            const variables = [...procedure.variables.entries()].map(
              ([variableName, declaration]) => {
                const supplied = instruction.presetVariables.get(variableName)
                if (supplied === undefined) {
                  if (declaration.type === 'bool') return 'false'
                  if (declaration.type === 'address') return 'address(0)'
                  return '0'
                }
                return generateValueType(supplied)
              }
            )
            const procedureName = procedureNameMap.get([
              module.moduleName,
              instruction.procedure,
            ])
            assert(procedureName !== undefined)
            return adorn(
              `procedure${procedureName}(${[
                ...arrays,
                ...variables,
                'communication',
              ].join(', ')})`
            )
          }
          case 'cross module call': {
            const foreignEnvironment = seenModules.get(
              instruction.module
            )?.environment
            assert(foreignEnvironment !== undefined)
            const arrays = (() => {
              if (foreignEnvironment === null) return []
              return [...foreignEnvironment.arrays.keys()].map(
                (name) =>
                  'environment' +
                  environmentNameMap.get(instruction.arrayMapping.get(name)!)
              )
            })()
            const procedure = crossModuleProcedureMap.get([
              instruction.module,
              instruction.procedure,
            ])
            assert(procedure !== undefined)
            const variables = [...procedure.variables.entries()].map(
              ([variableName, declaration]) => {
                const supplied = instruction.presetVariables.get(variableName)
                if (supplied === undefined) {
                  if (declaration.type === 'bool') return 'false'
                  if (declaration.type === 'address') return 'address(0)'
                  return '0'
                }
                return generateValueType(supplied)
              }
            )
            const procedureName = procedureNameMap.get([
              instruction.module,
              instruction.procedure,
            ])
            assert(procedureName !== undefined)
            return adorn(
              `procedure${procedureName}(${[
                ...arrays,
                ...variables,
                'communication',
              ].join(', ')})`
            )
          }
          case 'break':
            return adorn(`break`)
          case 'continue':
            return adorn(`continue`)
          case 'construct address':
            return adorn(
              `constructAddress(${instruction.bytes
                .map((x) => generateValueType(x))
                .join(', ')})`
            )
          default:
            return consumeNever(instruction)
        }
      }

      const generateValueType = (value: ValueType): string => {
        switch (value.type) {
          case 'literal':
            if (value.valueType === 'boolean') return value.raw
            if (value.valueType === 'number') return 'uint64(' + value.raw + ')'
            if (value.valueType === 'string') return `"${value.raw}"`
            return consumeNever(value.valueType)
          case 'local binder':
            return value.name
          default:
            return generateInstruction(value, { type: 'not in block' })
        }
      }

      joined += body
        .map((instruction) =>
          generateInstruction(instruction, {
            type: 'inside block',
            indentLevel: 2,
          })
        )
        .join('')
      joined += `${indent}} }\n\n`
    }

    seenModules.set(module.moduleName, module)
  }

  // Generate fallback function
  if (mainModule) {
    const mainProcedure = mainModule.procedures.find((p) => p.name === 'main')
    if (mainProcedure) {
      const mainIndex = procedureNameMap.get([mainModule.moduleName, 'main'])
      if (mainIndex !== undefined) {
        const envArgs = mainModule.environment
          ? [...mainModule.environment.arrays.keys()].join(', ')
          : ''
        const varArgs = Array(mainProcedure.variables.size).fill('0').join(', ')
        joined += `${indent}fallback() external payable {
        ${indent}${indent}main(${envArgs}${
          envArgs && varArgs ? ', ' : ''
        }${varArgs});
        ${indent}}\n\n`
      }
    }
  }

  joined += '}\n'

  return joined
}
