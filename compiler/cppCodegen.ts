import { consumeNever } from './consumeNever'
import { CoqCPAST, ValueType } from './parse'

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
            itemTypes
              .map((x) => (x === 'bool' ? x : 'u' + x + '_t'))
              .join(', ') +
            '> environment_' +
            get(name) +
            '[' +
            length.raw +
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
            const localBinderMap = new Map<string, number>()
            const print = (
              instruction: ValueType,
              state:
                | { type: 'not inside block' }
                | { type: 'inside block'; indentationLevel: number } = {
                type: 'not inside block',
              }
            ): string => {
              const adorn = (x: string) => {
                if (state.type === 'not inside block') return x
                return indent.repeat(state.indentationLevel) + x + ';\n'
              }

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
                  if (instruction.operator === 'boolean and') return '&&'
                  if (instruction.operator === 'boolean or') return '||'
                  return consumeNever(instruction.operator)
                })()
                return adorn(
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
                return adorn('(' + operator + print(instruction.value) + ')')
              }
              if (instruction.type === 'get') {
                return adorn('local_' + localNameMap.get(instruction.name))
              }
              if (instruction.type === 'set') {
                return adorn(
                  'local_' +
                    localNameMap.get(instruction.name) +
                    ' = ' +
                    print(instruction.value)
                )
              }
              if (instruction.type === 'store') {
                return adorn(
                  'environment_' +
                    environmentNameMap.get(instruction.name) +
                    '[' +
                    print(instruction.index) +
                    '] = ' +
                    '{ ' +
                    instruction.tuple.map((x) => print(x)).join(', ') +
                    ' }'
                )
              }
              if (instruction.type === 'retrieve') {
                return adorn(
                  'environment_' +
                    environmentNameMap.get(instruction.name) +
                    '[' +
                    print(instruction.index) +
                    ']'
                )
              }
              if (instruction.type === 'readChar') {
                return adorn('readChar()')
              }
              if (instruction.type === 'writeChar') {
                return adorn('writeChar(' + print(instruction.value) + ')')
              }
              if (instruction.type === 'subscript') {
                return adorn(
                  'get<' +
                    instruction.index.raw +
                    '>(' +
                    print(instruction.value) +
                    ')'
                )
              }
              if (instruction.type === 'sDivide') {
                return adorn(
                  '(toSigned(' +
                    print(instruction.left) +
                    ') / toSigned(' +
                    print(instruction.right) +
                    '))'
                )
              }
              if (instruction.type === 'divide') {
                return adorn(
                  '(' +
                    print(instruction.left) +
                    ' / ' +
                    print(instruction.right) +
                    ')'
                )
              }
              if (instruction.type === 'coerceInt8') {
                return adorn('uint8_t(' + print(instruction.value) + ')')
              }
              if (instruction.type === 'coerceInt16') {
                return adorn('uint16_t(' + print(instruction.value) + ')')
              }
              if (instruction.type === 'coerceInt32') {
                return adorn('uint32_t(' + print(instruction.value) + ')')
              }
              if (instruction.type === 'coerceInt64') {
                return adorn('uint64_t(' + print(instruction.value) + ')')
              }
              if (instruction.type === 'less') {
                return adorn(
                  '(' +
                    print(instruction.left) +
                    ' < ' +
                    print(instruction.right) +
                    ')'
                )
              }
              if (instruction.type === 'sLess') {
                return adorn(
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
                return adorn(
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
                return adorn(instruction.type)
              if (instruction.type === 'literal') {
                if (instruction.valueType === 'boolean')
                  return adorn(instruction.raw)
                else return adorn('uint64_t(' + instruction.raw + ')')
              }
              if (instruction.type === 'flush') {
                return adorn('flushSTDOUT()')
              }
              if (instruction.type === 'condition') {
                const { condition, body, alternate } = instruction
                if (state.type === 'not inside block') {
                  throw new Error('condition must be inside block')
                }
                const { indentationLevel } = state
                const baseIndent = indent.repeat(indentationLevel)
                return (
                  baseIndent +
                  'if (' +
                  print(condition) +
                  ') {\n' +
                  body
                    .map((x) =>
                      print(x, {
                        type: 'inside block',
                        indentationLevel: indentationLevel + 1,
                      })
                    )
                    .join('') +
                  baseIndent +
                  '}\n'
                )
              }
              if (instruction.type === 'range') {
                const { end, loopVariable, loopBody } = instruction
                const previousIndex = localBinderMap.get(loopVariable)

                const index = localBinderMap.size
                localBinderMap.set(loopVariable, index)

                if (state.type === 'not inside block') {
                  throw new Error('range must be inside block')
                }
                const { indentationLevel } = state

                const baseIndent = indent.repeat(indentationLevel)

                const constructed =
                  baseIndent +
                  'for (uint64_t binder_' +
                  index +
                  ' = 0; binder_' +
                  index +
                  ' < ' +
                  print(end) +
                  '; binder_' +
                  index +
                  '++) {\n' +
                  loopBody
                    .map((x) =>
                      print(x, {
                        type: 'inside block',
                        indentationLevel: indentationLevel + 1,
                      })
                    )
                    .join('') +
                  baseIndent +
                  '}\n'

                if (previousIndex === undefined) {
                  localBinderMap.delete(loopVariable)
                } else {
                  localBinderMap.set(loopVariable, previousIndex)
                }
                return constructed
              }
              if (instruction.type === 'local binder') {
                const index = localBinderMap.get(instruction.name)
                if (index === undefined) {
                  throw new Error('you forgot to validate')
                }
                return adorn('binder_' + index)
              }

              return consumeNever(instruction.type)
            }
            return print(instruction, {
              type: 'inside block',
              indentationLevel: 2,
            })
          })
          .join('') +
        indent +
        '};\n'
      )
    })
    .join('')

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
