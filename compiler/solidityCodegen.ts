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
      let struct = `struct ${structName} {\n`
      types.forEach((type, index) => {
        struct += `${indent}${solTypeName(type)} item${index};\n`
      })
      struct += '}\n\n'
      joined += struct
      structTypes.set(typeString, structName)
    }
    return structTypes.get(typeString)!
  }

  joined += 'contract GeneratedCode {\n'

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

    // Define functions
    for (const procedure of procedures) {
      const { name, body, variables } = procedure
      const index = procedureNameMap.size
      procedureNameMap.set([module.moduleName, name], index)

      const envParams = environment
        ? [...environment.arrays.entries()].map(([arrayName, description]) => {
            const structType = generateStructType(description.itemTypes)
            return `${structType}[] memory ${arrayName}`
          })
        : []

      const varParams = [...variables].map(
        ([varName, value]) => `${solTypeName(value.type)} ${varName}`
      )

      const allParams = [...envParams, ...varParams].join(', ')

      joined += `${indent}function ${name}(${allParams}) public {\n`

      // Generate function body
      const generateInstruction = (
        instruction: Instruction,
        indentLevel: number = 2
      ): string => {
        const currentIndent = indent.repeat(indentLevel)

        switch (instruction.type) {
          case 'get':
            return `${currentIndent}${instruction.name}\n`
          case 'set':
            return `${currentIndent}${instruction.name} = ${generateValueType(instruction.value)};\n`
          case 'store':
            if (instruction.name === 'communication') {
              return `${currentIndent}abi.encode(${instruction.tuple.map(generateValueType).join(', ')});\n`
            }
            const structType = generateStructType(
              instruction.tuple.map((v) => v.type as PrimitiveType)
            )
            return `${currentIndent}${instruction.name}[${generateValueType(instruction.index)}] = ${structType}(${instruction.tuple.map(generateValueType).join(', ')});\n`
          case 'retrieve':
            if (instruction.name === 'communication') {
              return `${currentIndent}abi.decode(msg.data, (uint8[]));\n`
            }
            return `${currentIndent}${instruction.name}[${generateValueType(instruction.index)}]\n`
          case 'communication area size':
            return `${currentIndent}msg.data.length\n`
          case 'invoke':
            return `${currentIndent}
            (bool success, bytes memory returnData) = address(${generateValueType(instruction.address)}).call{value: ${generateValueType(instruction.money)}}(
                abi.encodeWithSignature("${instruction.array}", ${generateValueType(instruction.communicationSize)})
            );
            require(success, "External call failed");
            assembly {
                let returnDataSize := mload(returnData)
                let dest := mload(0x40)
                mstore(0x40, add(dest, returnDataSize))
                codecopy(dest, add(returnData, 0x20), returnDataSize)
                ${instruction.array} := dest
            }
            \n`
          case 'donate':
            return `${currentIndent}payable(${generateValueType(instruction.address)}).transfer(${generateValueType(instruction.money)});\n`
          case 'get sender':
            return `${currentIndent}msg.sender\n`
          case 'get money':
            return `${currentIndent}msg.value\n`
          case 'range':
            return (
              `${currentIndent}for (uint ${instruction.loopVariable} = 0; ${instruction.loopVariable} < ${generateValueType(instruction.end)}; ${instruction.loopVariable}++) {\n` +
              instruction.loopBody
                .map((i) => generateInstruction(i, indentLevel + 1))
                .join('') +
              `${currentIndent}}\n`
            )
          case 'readChar':
          case 'writeChar':
          case 'flush':
            return `${currentIndent}revert("Operation not supported in Solidity");\n`
          case 'binaryOp':
            return `${currentIndent}(${generateValueType(instruction.left)} ${binaryOpToSolidity(instruction.operator)} ${generateValueType(instruction.right)})\n`
          case 'unaryOp':
            return `${currentIndent}(${unaryOpToSolidity(instruction.operator)}${generateValueType(instruction.value)})\n`
          case 'subscript':
            return `${currentIndent}${generateValueType(instruction.value)}.item${generateValueType(instruction.index)}\n`
          case 'condition':
            return (
              `${currentIndent}if (${generateValueType(instruction.condition)}) {\n` +
              instruction.body
                .map((i) => generateInstruction(i, indentLevel + 1))
                .join('') +
              `${currentIndent}} else {\n` +
              instruction.alternate
                .map((i) => generateInstruction(i, indentLevel + 1))
                .join('') +
              `${currentIndent}}\n`
            )
          case 'sDivide':
            return `${currentIndent}(int256(${generateValueType(instruction.left)}) / int256(${generateValueType(instruction.right)}))\n`
          case 'divide':
            return `${currentIndent}(${generateValueType(instruction.left)} / ${generateValueType(instruction.right)})\n`
          case 'coerceInt8':
            return `${currentIndent}uint8(${generateValueType(instruction.value)})\n`
          case 'coerceInt16':
            return `${currentIndent}uint16(${generateValueType(instruction.value)})\n`
          case 'coerceInt32':
            return `${currentIndent}uint32(${generateValueType(instruction.value)})\n`
          case 'coerceInt64':
            return `${currentIndent}uint64(${generateValueType(instruction.value)})\n`
          case 'coerceInt256':
            return `${currentIndent}uint256(${generateValueType(instruction.value)})\n`
          case 'less':
            return `${currentIndent}(${generateValueType(instruction.left)} < ${generateValueType(instruction.right)})\n`
          case 'sLess':
            return `${currentIndent}(int256(${generateValueType(instruction.left)}) < int256(${generateValueType(instruction.right)}))\n`
          case 'call':
            const args = Array.from(instruction.presetVariables.entries())
              .map(([name, value]) => `${name}: ${generateValueType(value)}`)
              .join(', ')
            return `${currentIndent}${instruction.procedure}(${args});\n`
          case 'cross module call':
            const crossArgs = Array.from(instruction.presetVariables.entries())
              .map(([name, value]) => `${name}: ${generateValueType(value)}`)
              .join(', ')
            return `${currentIndent}${instruction.module}_${instruction.procedure}(${crossArgs});\n`
          case 'break':
            return `${currentIndent}break;\n`
          case 'continue':
            return `${currentIndent}continue;\n`
          case 'construct address':
            return `${currentIndent}address(uint160(uint256(${instruction.bytes.map(generateValueType).join(' | ')})))\n`
          default:
            return consumeNever(instruction)
        }
      }

      const generateValueType = (value: ValueType): string => {
        switch (value.type) {
          case 'literal':
            if (value.valueType === 'boolean') return value.raw
            if (value.valueType === 'number') return value.raw
            if (value.valueType === 'string') return `"${value.raw}"`
            return consumeNever(value.valueType)
          case 'local binder':
            return value.name
          default:
            return generateInstruction(value, 0).trim()
        }
      }

      joined += body
        .map((instruction) => generateInstruction(instruction))
        .join('')
      joined += `${indent}}\n\n`
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
        ${indent}${indent}main(${envArgs}${envArgs && varArgs ? ', ' : ''}${varArgs});
        ${indent}}\n\n`
      }
    }
  }

  joined += '}\n'

  return joined
}
