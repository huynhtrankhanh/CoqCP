import { consumeNever } from './consumeNever'
import { CoqCPAST, Instruction, ValueType } from './parse'

const indent = '  '

export const cppCodegen = ({ environment, procedures }: CoqCPAST): string => {
  const environmentNameMap = new Map<string, number>()
  const procedureNameMap = new Map<string, number>()

  const environmentCode = (() => {
    if (environment === null) return ''

    let counter = 0

    const get = (name: string) => {
      environmentNameMap.set(name, counter)
      return counter++
    }

    return (
      [...environment.arrays]
        .map(([name, description]) => {
          const { itemTypes, length } = description
          return (
            'std::tuple<' +
            itemTypes.map((x) => 'u' + x + '_t').join(', ') +
            '> environment_' +
            get(name) +
            '[' +
            length +
            '];\n'
          )
        })
        .join('') + '\n'
    )
  })()

  const mainCode = procedures
    .map(({ name, body, variables }, index) => {
      procedureNameMap.set(name, index)
      const localNameMap = new Map<string, number>()
      return (
        indent +
        'auto procedure_' +
        index +
        ' = [&](' +
        [...variables]
          .map(([name, value], index) => {
            const { type } = value
            localNameMap.set(name, index)
            return 'u' + type + '_t local_' + index
          })
          .join(', ') +
        ') {\n' +
        body
          .map((instruction) => {
            const print = (instruction: ValueType): string => {
              if (instruction.type === 'binaryOp') {
                const operator = ((): string => {
                  if (instruction.operator === 'add') return '+'
                  if (instruction.operator === 'subtract') return '-'
                  if (instruction.operator === 'multiply') return '*'
                  if (instruction.operator === 'mod') return '%'
                  if (instruction.operator === 'bitwise or') return '|'
                  if (instruction.operator === 'bitwise xor') return '^'
                  if (instruction.operator === 'bitwise and') return '&'
                  if (instruction.operator === 'shift right') return '>>'
                  if (instruction.operator === 'shift left') return '<<'
                  if (instruction.operator === 'equal') return '=='
                  if (instruction.operator === 'noteq') return '!='
                  return consumeNever(instruction.operator)
                })()
                return (
                  '(' +
                  print(instruction.left) +
                  ' ' +
                  operator +
                  ' ' +
                  print(instruction.right) +
                  ')'
                )
              }
              if (instruction.type === 'unaryOp') {
                const operator = ((): string => {
                  if (instruction.operator === 'plus') return '+'
                  if (instruction.operator === 'minus') return '-'
                  if (instruction.operator === 'bitwise not') return '~'
                  if (instruction.operator === 'boolean not') return '!'
                  return consumeNever(instruction.operator)
                })()
                return '(' + operator + print(instruction.value) + ')'
              }
              if (instruction.type === 'get') {
                return 'local_' + localNameMap.get(instruction.name)
              }
              if (instruction.type === 'set') {
                return (
                  'local_' +
                  localNameMap.get(instruction.name) +
                  ' = ' +
                  print(instruction.value)
                )
              }
              if (instruction.type === 'store') {
                return (
                  'environment_' +
                  environmentNameMap.get(instruction.name) +
                  '[' +
                  print(instruction.index) +
                  '] = ' +
                  '{ ' +
                  instruction.tuples.map(print).join(', ') +
                  ' }'
                )
              }
              if (instruction.type === 'retrieve') {
                return (
                  'environment_' +
                  environmentNameMap.get(instruction.name) +
                  '[' +
                  print(instruction.index) +
                  ']'
                )
              }
              if (instruction.type === 'readInt8') {
                return 'readInt8()'
              }
              if (instruction.type === 'writeInt8') {
                return 'writeInt8(' + print(instruction.value) + ')'
              }
              if (instruction.type === 'subscript') {
                return (
                  'get<' +
                  instruction.index.value +
                  '>(' +
                  print(instruction.value) +
                  ')'
                )
              }
              if (instruction.type === 'sDivide') {
                return (
                  '(toSigned(' +
                  print(instruction.left) +
                  ') / toSigned(' +
                  print(instruction.right) +
                  '))'
                )
              }
              if (instruction.type === 'divide') {
                return (
                  '(' +
                  print(instruction.left) +
                  ' / ' +
                  print(instruction.right) +
                  ')'
                )
              }
              if (instruction.type === 'coerceInt8') {
                return 'uint8_t(' + print(instruction.value) + ')'
              }
              if (instruction.type === 'coerceInt16') {
                return 'uint16_t(' + print(instruction.value) + ')'
              }
              if (instruction.type === 'coerceInt32') {
                return 'uint32_t(' + print(instruction.value) + ')'
              }
              if (instruction.type === 'coerceInt64') {
                return 'uint64_t(' + print(instruction.value) + ')'
              }
              if (instruction.type === 'less') {
                return (
                  '(' +
                  print(instruction.left) +
                  ' < ' +
                  print(instruction.right) +
                  ')'
                )
              }
              if (instruction.type === 'sLess') {
                return (
                  '(toSigned(' +
                  print(instruction.left) +
                  ') < toSigned(' +
                  print(instruction.right) +
                  '))'
                )
              }
              if (instruction.type === 'call') {
                const index = procedureNameMap.get(instruction.procedure)
                if (index === undefined) {
                  throw new Error('you forgot to validate')
                }
                const { variables } = procedures[index]
                const supplied = instruction.presetVariables
                return (
                  'procedure_' +
                  index +
                  '(' +
                  [...variables.keys()]
                    .map((x) => {
                      const value = supplied.get(x)
                      if (value === undefined) return '0'
                      else return print(value)
                    })
                    .join(', ') +
                  ')'
                )
              }
              if (
                instruction.type === 'break' ||
                instruction.type === 'continue'
              )
                return instruction.type
              if (instruction.type === 'literal') {
                if (instruction.valueType === 'boolean') return instruction.raw
                else return 'uint64_t(' + instruction.raw + ')'
              }
              if (instruction.type === "flush") {
                return "flushSTDOUT()"
              }
              
              return consumeNever(instruction.type)
            }
            return print(instruction) + ';\n'
          })
          .join('') +
        '};'
      )
    })
    .join('\n')

  const toSigned = [8, 16, 32, 64]
    .map((x) => 'int' + x + '_t toSigned(uint' + x + '_t x) { return x; }\n')
    .join('')

  return (
    '#include <iostream>\n#include <tuple>\n' +
    toSigned +
    environmentCode +
    'int main() {\n' +
    mainCode +
    '}'
  )
}
