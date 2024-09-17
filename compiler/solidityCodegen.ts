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
      struct +=
        indent +
        '}\n\n' +
        `${indent}function arrayGet(${structName}[] storage array, uint64 index) private returns (${structName} memory) {\n${indent}${indent}if (index >= array.length) { assembly { revert(0, 0) } }\n${indent}${indent}return array[index];\n${indent}}\n\n${indent}function arraySet(${structName}[] storage array, uint64 index, ${structName} memory value) private {\n${indent}${indent}if (index >= array.length) { assembly { revert(0, 0) } }\n${indent}${indent}array[index] = value;\n${indent}}\n\n`
      joined += struct
      structTypes.set(typeString, structName)
    }
    return structTypes.get(typeString)!
  }

  joined +=
    `contract SelfDestructContract {
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

    function communicationGet(bytes memory communication, uint64 index) private returns (uint8) {
        if (index >= communication.length) { assembly { revert(0, 0) } }
        return uint8(communication[index]);
    }

    function communicationSet(bytes memory communication, uint64 index, uint8 value) private {
        if (index >= communication.length) { assembly { revert(0, 0) } }
        communication[index] = bytes1(value);
    }

` +
    [8, 16, 32, 64, 256]
      .map(
        (
          width
        ) => `    function sdivint${width}(int${width} a, int${width} b) private returns (int${width}) {
        if ((b == -1 && a == type(int${width}).min) || b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

    function divint${width}(uint${width} a, uint${width} b) private returns (uint${width}) {
        if (b == 0) { assembly { revert(0, 0) } }
        return a / b;
    }

`
      )
      .join('')

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

  let constructorBody = ''

  // Generate storage variables for main module arrays
  if (mainModule && mainModule.environment) {
    let index = 0
    for (const [_, description] of mainModule.environment.arrays) {
      const { itemTypes, length } = description
      const structType = generateStructType(itemTypes)
      joined += `${indent}${structType}[] public environment${index};\n`
      constructorBody += `${indent}${indent}environment${index} = new ${structType}[](${length.raw});\n`
      index++
    }
  }

  joined += `\n${indent}constructor() {\n${constructorBody}${indent}}\n`

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
            return `${structType}[] storage environment${index}`
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

      type GeneratedExpression = {
        expression: string
        type: PrimitiveType | PrimitiveType[] | 'statement'
      }

      const generateInstruction = (
        instruction: Instruction,
        inBlock:
          | { type: 'inside block'; indentLevel: number }
          | { type: 'not in block' } = {
          type: 'not in block',
        }
      ): GeneratedExpression => {
        const adorn = (
          x: string,
          type: PrimitiveType | PrimitiveType[] | 'statement'
        ): GeneratedExpression => {
          if (inBlock.type === 'not in block') return { expression: x, type }
          return {
            expression: indent.repeat(inBlock.indentLevel) + x + ';\n',
            type: 'statement',
          }
        }

        switch (instruction.type) {
          case 'get':
            return adorn(
              `local${localVariableIndex.get(instruction.name)}`,
              variables.get(instruction.name)!.type
            )
          case 'set':
            return adorn(
              `local${localVariableIndex.get(instruction.name)} = ${
                generateValueType(instruction.value).expression
              }`,
              'statement'
            )
          case 'store':
            if (instruction.name === COMMUNICATION) {
              return adorn(
                `communicationSet(communication, ${
                  generateValueType(instruction.index).expression
                }, ${generateValueType(instruction.value).expression})`,
                'statement'
              )
            }
            const elementType = environment?.arrays.get(
              instruction.name
            )?.itemTypes
            assert(elementType !== undefined)
            const structType = generateStructType(elementType)
            return adorn(
              `arraySet(environment${environmentNameMap.get(
                instruction.name
              )}, ${
                generateValueType(instruction.index).expression
              }, ${structType}(${instruction.tuple
                .map((t) => generateValueType(t).expression)
                .join(', ')}))`,
              'statement'
            )
          case 'retrieve':
            if (instruction.name === COMMUNICATION) {
              return adorn(
                `communicationGet(communication, ${
                  generateValueType(instruction.index).expression
                })`,
                'int8'
              )
            }
            const retrievedType = environment?.arrays.get(
              instruction.name
            )?.itemTypes
            assert(retrievedType !== undefined)
            return adorn(
              `arrayGet(environment${environmentNameMap.get(
                instruction.name
              )}, ${generateValueType(instruction.index).expression})`,
              retrievedType
            )
          case 'communication area size':
            return adorn(`msg.data.length`, 'int256')
          case 'invoke':
            assert(inBlock.type === 'inside block')
            const currentIndent = indent.repeat(inBlock.indentLevel)
            return {
              expression: `${currentIndent}{
${currentIndent}${indent}uint64 communicationSize = ${
                generateValueType(instruction.communicationSize).expression
              };
${currentIndent}${indent}bytes memory callData = new bytes(communicationSize);
${currentIndent}${indent}for (uint64 i = 0; i < communicationSize; i++) callData[i] = bytes1(arrayGet(environment${environmentNameMap.get(
                instruction.array
              )}, i).item0);
${currentIndent}${indent}(bool success, bytes memory returnData) = address(${
                generateValueType(instruction.address).expression
              }).call{value: ${
                generateValueType(instruction.money).expression
              }}(callData);
${currentIndent}${indent}for (uint64 i = 0; i < communicationSize && i < returnData.length; i++)
${currentIndent}${indent}${indent}arraySet(environment${environmentNameMap.get(
                instruction.array
              )}, i, ${generateStructType(['int8'])}(uint8(returnData[i])));
${currentIndent}}\n`,
              type: 'statement',
            }
          case 'donate':
            return adorn(
              `shoot(payable(${
                generateValueType(instruction.address).expression
              }), ${generateValueType(instruction.money).expression})`,
              'statement'
            )
          case 'get sender':
            return adorn(`msg.sender`, 'address')
          case 'get money':
            return adorn(`msg.value`, 'int256')
          case 'range':
            assert(inBlock.type === 'inside block')
            const rangeIndent = indent.repeat(inBlock.indentLevel)
            const localBinderIndex = localBinderMap.size
            localBinderMap.set(instruction.loopVariable, localBinderMap.size)
            const rangeExpression =
              `${rangeIndent}for (uint64 binder${localBinderIndex} = 0; binder${localBinderIndex} < ${
                generateValueType(instruction.end).expression
              }; binder${localBinderIndex}++) {\n` +
              instruction.loopBody
                .map(
                  (i) =>
                    generateInstruction(i, {
                      type: 'inside block',
                      indentLevel: inBlock.indentLevel + 1,
                    }).expression
                )
                .join('') +
              `${rangeIndent}}\n`
            return { expression: rangeExpression, type: 'statement' }
          case 'readChar':
          case 'writeChar':
          case 'flush':
            return adorn(
              `revert("Operation not supported in Solidity")`,
              'statement'
            )
          case 'binaryOp': {
            const left = generateValueType(instruction.left)
            const right = generateValueType(instruction.right)
            let resultType: PrimitiveType

            switch (instruction.operator) {
              case 'equal':
              case 'noteq':
                resultType = 'bool'
                break
              case 'add':
              case 'subtract':
              case 'multiply':
              case 'mod':
              case 'bitwise or':
              case 'bitwise xor':
              case 'bitwise and':
              case 'shift right':
              case 'shift left':
                resultType = getBinaryOpResultType(left.type, right.type)
                break
              case 'boolean and':
              case 'boolean or':
                resultType = 'bool'
                break
              default:
                return consumeNever(instruction)
            }

            return adorn(
              `(${left.expression} ${binaryOpToSolidity(
                instruction.operator
              )} ${right.expression})`,
              resultType
            )
          }
          case 'unaryOp': {
            const value = generateValueType(instruction.value)
            let resultType: PrimitiveType

            switch (instruction.operator) {
              case 'plus':
                return value
              case 'minus':
                return adorn(`((~${value.expression}) + 1)`, value.type)
              case 'bitwise not':
                resultType = value.type as PrimitiveType // Assuming it's not a tuple type
                break
              case 'boolean not':
                resultType = 'bool'
                break
              default:
                return consumeNever(instruction)
            }

            return adorn(
              `(${unaryOpToSolidity(instruction.operator)}${value.expression})`,
              resultType
            )
          }
          case 'sDivide':
          case 'divide': {
            const left = generateValueType(instruction.left)
            const right = generateValueType(instruction.right)
            const resultType = getBinaryOpResultType(left.type, right.type)
            const op = instruction.type === 'sDivide' ? left.type : ''
            const divideFn =
              (instruction.type === 'sDivide' ? 'sdiv' : 'div') + resultType

            return adorn(
              `${divideFn}(${op}(${left.expression}), ${op}(${right.expression}))`,
              resultType
            )
          }
          case 'coerceInt8':
            return adorn(
              `uint8(${generateValueType(instruction.value).expression})`,
              'int8'
            )
          case 'coerceInt16':
            return adorn(
              `uint16(${generateValueType(instruction.value).expression})`,
              'int16'
            )
          case 'coerceInt32':
            return adorn(
              `uint32(${generateValueType(instruction.value).expression})`,
              'int32'
            )
          case 'coerceInt64':
            return adorn(
              `uint64(${generateValueType(instruction.value).expression})`,
              'int64'
            )
          case 'coerceInt256':
            return adorn(
              `uint256(${generateValueType(instruction.value).expression})`,
              'int256'
            )
          case 'less':
            return adorn(
              `(${generateValueType(instruction.left).expression} < ${
                generateValueType(instruction.right).expression
              })`,
              'bool'
            )
          case 'sLess': {
            const left = generateValueType(instruction.left)
            return adorn(
              `(${left.type}(${left.expression}) < ${left.type}(${
                generateValueType(instruction.right).expression
              }))`,
              'bool'
            )
          }
          case 'call':
          case 'cross module call': {
            const procedureName =
              instruction.type === 'call'
                ? procedureNameMap.get([
                    module.moduleName,
                    instruction.procedure,
                  ])
                : procedureNameMap.get([
                    instruction.module,
                    instruction.procedure,
                  ])
            assert(procedureName !== undefined)
            const procedure =
              instruction.type === 'call'
                ? crossModuleProcedureMap.get([
                    module.moduleName,
                    instruction.procedure,
                  ])
                : crossModuleProcedureMap.get([
                    instruction.module,
                    instruction.procedure,
                  ])
            assert(procedure !== undefined)

            const arrays =
              instruction.type === 'call'
                ? Array.from(
                    { length: environment?.arrays?.size || 0 },
                    (_, i) => 'environment' + i
                  )
                : (() => {
                    const foreignEnvironment = seenModules.get(
                      instruction.module
                    )?.environment
                    assert(foreignEnvironment !== undefined)
                    if (foreignEnvironment === null) return []
                    return [...foreignEnvironment.arrays.keys()].map(
                      (name) =>
                        'environment' +
                        environmentNameMap.get(
                          instruction.arrayMapping.get(name)!
                        )
                    )
                  })()

            const variables = [...procedure.variables.entries()].map(
              ([variableName, declaration]) => {
                const supplied = instruction.presetVariables.get(variableName)
                if (supplied === undefined) {
                  if (declaration.type === 'bool') return 'false'
                  if (declaration.type === 'address') return 'address(0)'
                  return '0'
                }
                return generateValueType(supplied).expression
              }
            )

            return adorn(
              `procedure${procedureName}(${[
                ...arrays,
                ...variables,
                'communication',
              ].join(', ')})`,
              'statement'
            )
          }
          case 'break':
            return adorn(`break`, 'statement')
          case 'continue':
            return adorn(`continue`, 'statement')
          case 'construct address':
            return adorn(
              `constructAddress(${instruction.bytes
                .map((x) => generateValueType(x).expression)
                .join(', ')})`,
              'address'
            )
          case 'condition': {
            assert(inBlock.type === 'inside block')
            const conditionIndent = indent.repeat(inBlock.indentLevel)
            const conditionExpression =
              `${conditionIndent}if (${
                generateValueType(instruction.condition).expression
              }) {\n` +
              instruction.body
                .map(
                  (i) =>
                    generateInstruction(i, {
                      type: 'inside block',
                      indentLevel: inBlock.indentLevel + 1,
                    }).expression
                )
                .join('') +
              `${conditionIndent}} else {\n` +
              instruction.alternate
                .map(
                  (i) =>
                    generateInstruction(i, {
                      type: 'inside block',
                      indentLevel: inBlock.indentLevel + 1,
                    }).expression
                )
                .join('') +
              `${conditionIndent}}\n`
            return { expression: conditionExpression, type: 'statement' }
          }
          case 'subscript': {
            const isTuple = instruction.value.type === 'retrieve'
            if (isTuple) {
              assert(instruction.index.type === 'literal')
              const value = generateValueType(instruction.value)
              assert(Array.isArray(value.type))
              return adorn(
                `${value.expression}.item${instruction.index.raw}`,
                value.type[Number(instruction.index.raw)]
              )
            } else {
              return adorn(`${generateValueType(instruction.value)}`, 'int8')
            }
          }
          default:
            return consumeNever(instruction)
        }
      }

      const getBinaryOpResultType = (
        left: PrimitiveType | PrimitiveType[] | 'statement',
        right: PrimitiveType | PrimitiveType[] | 'statement'
      ): PrimitiveType => {
        if (
          Array.isArray(left) ||
          Array.isArray(right) ||
          left === 'statement' ||
          right === 'statement'
        ) {
          throw new Error(
            'Cannot perform binary operations on tuple types ' +
              JSON.stringify(left) +
              ' ' +
              JSON.stringify(right)
          )
        }

        const typeOrder: (
          | 'bool'
          | 'int8'
          | 'int16'
          | 'int32'
          | 'int64'
          | 'int256'
          | 'address'
        )[] = ['bool', 'int8', 'int16', 'int32', 'int64', 'int256', 'address']
        return typeOrder[
          Math.max(typeOrder.indexOf(left), typeOrder.indexOf(right))
        ]
      }

      const generateValueType = (value: ValueType): GeneratedExpression => {
        switch (value.type) {
          case 'literal':
            if (value.valueType === 'boolean')
              return { expression: value.raw, type: 'bool' }
            if (value.valueType === 'number') {
              return { expression: 'uint64(' + value.raw + ')', type: 'int64' }
            }
            if (value.valueType === 'string')
              return { expression: `"${value.raw}"`, type: 'int8' } // Assuming string is treated as byte array
            return consumeNever(value.valueType)
          case 'local binder':
            return {
              expression: 'binder' + localBinderMap.get(value.name),
              type: 'int64',
            } // Assuming binders are always int64
          default:
            return generateInstruction(value, { type: 'not in block' })
        }
      }

      joined += body
        .map(
          (instruction) =>
            generateInstruction(instruction, {
              type: 'inside block',
              indentLevel: 2,
            }).expression
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
        const envArgs = Array.from(
          { length: mainModule.environment?.arrays?.size || 0 },
          (_, index) => 'environment' + index
        )
        const varArgs = [...mainProcedure.variables.values()].map((x) => {
          if (x.type === 'bool') return 'false'
          if (x.type === 'address') return 'address(0)'
          return '0'
        })
        joined += `${indent}fallback() external payable {
${indent}${indent}bytes memory data = msg.data;
${indent}${indent}procedure${procedureNameMap.get(['', 'main'])}(${[
          ...envArgs,
          ...varArgs,
          'data',
        ].join(', ')});
${indent}${indent}assembly {
${indent}${indent}${indent}return(add(data, 0x20), mload(data))
${indent}${indent}}
${indent}}\n`
      }
    } else {
      joined += `${indent}fallback() external payable {}\n`
    }
  }

  joined += '}\n'

  return joined
}
