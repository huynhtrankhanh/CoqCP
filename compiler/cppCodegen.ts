import { PairMap } from './PairMap'
import { assert } from './assert'
import { consumeNever } from './consumeNever'
import isPure from './isPure'
import { CoqCPAST, Procedure, ValueType } from './parse'

const indent = '  '
const preamble = (() => {
  const toSigned = [8, 16, 32, 64]
    .map((x) => 'int' + x + '_t toSigned(uint' + x + '_t x) { return x; }\n')
    .join('')

  const binaryOp = `auto binaryOp(auto a, auto b, auto f)
{
  auto c = a();
  auto d = b();
  return f(c, d);
}
`

  const charOps = `/**
 * Author: chilli
 * License: CC0
 * Source: Own work
 * Description: Read an integer from stdin. Usage requires your program to pipe in
 * input from file.
 * Usage: ./a.out < input.txt
 * Time: About 5x as fast as cin/scanf.
 * Status: tested on SPOJ INTEST, unit tested
 */

inline uint64_t readChar() { // like getchar()
  static char buf[1 << 16];
  static size_t bc, be;
  if (bc >= be) {
    buf[0] = 0, bc = 0;
    be = fread(buf, 1, sizeof(buf), stdin);
  }
  if (bc >= be) return -1;
  return buf[bc++]; // returns -1 on EOF
}

void writeChar(uint8_t x) {
  std::cout << (char)x;
}

void flushSTDOUT() {
  std::cout << std::flush;
}
`

  return (
    '#include <iostream>\n#include <tuple>\n#include <cstdlib>\n#include <cstdint>\nusing std::get;\n' +
    charOps +
    toSigned +
    binaryOp
  )
})()

export const cppCodegen = (sortedModules: CoqCPAST[]): string => {
  const crossModuleProcedureMap = new PairMap<string, string, Procedure>()
  const procedureNameMap = new PairMap<string, string, number>()
  const seenModules = new Map<string, CoqCPAST>()

  let joined = ''

  for (const module of sortedModules) {
    const { environment, procedures } = module
    const environmentNameMap = new Map<string, number>()

    const environmentCode = (() => {
      if (environment === null) return []

      let counter = 0

      const get = (name: string) => {
        environmentNameMap.set(name, counter)
        return counter++
      }

      return [...environment.arrays].map(([name, description]) => {
        const { itemTypes } = description
        return (
          'std::tuple<' +
          itemTypes.map((x) => (x === 'bool' ? x : 'u' + x + '_t')).join(', ') +
          '> *environment_' +
          get(name)
        )
      })
    })()

    const mapProcedureNameToArrayIndex = new Map<string, number>()

    const mainCode = procedures
      .map((procedure, arrayIndex) => {
        const { name, body, variables } = procedure
        const index = procedureNameMap.size()
        procedureNameMap.set([module.moduleName, name], index)
        mapProcedureNameToArrayIndex.set(procedure.name, arrayIndex)
        const localNameMap = new Map<string, number>()
        const code =
          indent +
          'auto procedure_' +
          index +
          ' = [&](' +
          [
            ...environmentCode,
            ...[...variables].map(([name, value], index) => {
              const { type } = value
              localNameMap.set(name, index)
              return 'u' + type + '_t local_' + index
            }),
          ].join(', ') +
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
                  if (
                    instruction.operator === 'boolean and' ||
                    instruction.operator === 'boolean or'
                  ) {
                    const operator =
                      instruction.operator === 'boolean and' ? '&&' : '||'
                    return adorn(
                      print(instruction.left) +
                        ' ' +
                        operator +
                        ' ' +
                        print(instruction.right)
                    )
                  }
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
                  if (isPure(instruction.left) && isPure(instruction.right))
                    return adorn(
                      '(' +
                        print(instruction.left) +
                        ' ' +
                        operator +
                        ' ' +
                        print(instruction.right) +
                        ')'
                    )
                  return adorn(
                    'binaryOp([&]() { return ' +
                      print(instruction.left) +
                      '; }, [&]() { return ' +
                      print(instruction.right) +
                      '; }, [&](auto a, auto b) { return a ' +
                      operator +
                      ' b; })'
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
                  assert(typeof instruction.name === 'string')
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
                  assert(typeof instruction.name === 'string')
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
                  assert(instruction.index.type === 'literal')
                  return adorn(
                    'get<' +
                      instruction.index.raw +
                      '>(' +
                      print(instruction.value) +
                      ')'
                  )
                }
                if (instruction.type === 'sDivide') {
                  if (isPure(instruction.left) && isPure(instruction.right)) {
                    return adorn(
                      '(toSigned(' +
                        print(instruction.left) +
                        ') / toSigned(' +
                        print(instruction.right) +
                        '))'
                    )
                  }
                  return adorn(
                    'binaryOp([&]() { return toSigned(' +
                      print(instruction.left) +
                      '); }, [&]() { return toSigned(' +
                      print(instruction.right) +
                      '); }, [&](auto a, auto b) { return a / b; })'
                  )
                }
                if (instruction.type === 'divide') {
                  if (isPure(instruction.left) && isPure(instruction.right)) {
                    return adorn(
                      '(' +
                        print(instruction.left) +
                        ' / ' +
                        print(instruction.right) +
                        ')'
                    )
                  }
                  return adorn(
                    'binaryOp([&]() { return ' +
                      print(instruction.left) +
                      '; }, [&]() { return ' +
                      print(instruction.right) +
                      '; }, [&](auto a, auto b) { return a / b; })'
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
                  if (isPure(instruction.left) && isPure(instruction.right)) {
                    return adorn(
                      '(' +
                        print(instruction.left) +
                        ' < ' +
                        print(instruction.right) +
                        ')'
                    )
                  }
                  return adorn(
                    'binaryOp([&]() { return ' +
                      print(instruction.left) +
                      '; }, [&]() { return ' +
                      print(instruction.right) +
                      '; }, [&](auto a, auto b) { return a < b; })'
                  )
                }
                if (instruction.type === 'sLess') {
                  if (isPure(instruction.left) && isPure(instruction.right)) {
                    return adorn(
                      '(toSigned(' +
                        print(instruction.left) +
                        ') < toSigned(' +
                        print(instruction.right) +
                        '))'
                    )
                  }
                  return adorn(
                    'binaryOp([&]() { return toSigned(' +
                      print(instruction.left) +
                      '); }, [&]() { return toSigned(' +
                      print(instruction.right) +
                      '); }, [&](auto a, auto b) { return a < b; })'
                  )
                }
                if (instruction.type === 'call') {
                  const arrayIndex = mapProcedureNameToArrayIndex.get(
                    instruction.procedure
                  )
                  const index = procedureNameMap.get([
                    module.moduleName,
                    instruction.procedure,
                  ])!
                  if (arrayIndex === undefined) {
                    throw new Error('you forgot to validate')
                  }
                  const { variables } = procedures[arrayIndex]
                  const supplied = instruction.presetVariables
                  const argumentList = [...variables.keys()].map((x) => {
                    const value = supplied.get(x)
                    if (value === undefined) return '0'
                    else return print(value)
                  })
                  const environmentArrays = Array.from({
                    length: environment?.arrays.size || 0,
                  }).map((_, i) => 'environment_' + i)
                  if ([...supplied.values()].some((x) => !isPure(x))) {
                    // emit workaround code
                    return adorn(
                      '([&]() {' +
                        argumentList
                          .map(
                            (value, index) =>
                              `auto workaround_${index} = ${value}; `
                          )
                          .join('') +
                        'procedure_' +
                        arrayIndex +
                        '(' +
                        [
                          ...environmentArrays,
                          ...argumentList.map(
                            (_, index) => 'workaround_' + index
                          ),
                        ].join(', ') +
                        ');})()'
                    )
                  }
                  return adorn(
                    'procedure_' +
                      index +
                      '(' +
                      [...environmentArrays, ...argumentList].join(', ') +
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
                    '} else {\n' +
                    alternate
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

                  let constructed = ''
                  if (end.type === 'literal' && end.valueType === 'string') {
                    constructed =
                      baseIndent +
                      'for (uint8_t binder_' +
                      index +
                      ' : { ' +
                      (() => {
                        const encoder = new TextEncoder()
                        const encoded = encoder.encode(end.raw)
                        return encoded.join(', ')
                      })() +
                      ' }) {\n' +
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
                  } else {
                    constructed =
                      baseIndent +
                      'for (uint64_t binder_' +
                      index +
                      ' = 0, loop_end = ' +
                      print(end) +
                      '; binder_' +
                      index +
                      ' < loop_end; binder_' +
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
                  }
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
                if (instruction.type === 'cross module call') {
                  const index = procedureNameMap.get([
                    instruction.module,
                    instruction.procedure,
                  ])
                  if (index === undefined) {
                    throw new Error('you forgot to validate')
                  }
                  const foreignModule = seenModules.get(instruction.module)
                  if (foreignModule === undefined) {
                    throw new Error('you forgot to validate')
                  }
                  const { variables } = crossModuleProcedureMap.get([
                    instruction.module,
                    instruction.procedure,
                  ])!
                  const supplied = instruction.presetVariables
                  const argumentList = [...variables.keys()].map((x) => {
                    const value = supplied.get(x)
                    if (value === undefined) return '0'
                    else return print(value)
                  })
                  const environmentArrays = (() => {
                    const iterator = foreignModule.environment?.arrays.keys()
                    if (iterator === undefined) return []
                    return [...iterator]
                  })().map((array) => {
                    const mappedArray = instruction.arrayMapping.get(array)
                    if (mappedArray === undefined)
                      throw new Error('you forgot to validate')
                    const name = environmentNameMap.get(mappedArray)
                    if (name === undefined)
                      throw new Error('you forgot to validate')
                    return 'environment_' + name
                  })
                  if ([...supplied.values()].some((x) => !isPure(x))) {
                    // emit workaround code
                    return adorn(
                      '([&]() {' +
                        argumentList
                          .map(
                            (value, index) =>
                              `auto workaround_${index} = ${value}; `
                          )
                          .join('') +
                        'procedure_' +
                        index +
                        '(' +
                        [
                          ...environmentArrays,
                          ...argumentList.map(
                            (_, index) => 'workaround_' + index
                          ),
                        ].join(', ') +
                        ');})()'
                    )
                  }
                  return adorn(
                    'procedure_' +
                      index +
                      '(' +
                      [...environmentArrays, ...argumentList].join(', ') +
                      ')'
                  )
                }

                assert(instruction.type !== 'coerceInt256')
                assert(instruction.type !== 'communication area size')
                assert(instruction.type !== 'construct address')
                assert(instruction.type !== 'donate')
                assert(instruction.type !== 'get money')
                assert(instruction.type !== 'get sender')
                assert(instruction.type !== 'invoke')

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
        crossModuleProcedureMap.set(
          [module.moduleName, procedure.name],
          procedure
        )
        return code
      })
      .join('')

    joined += mainCode

    'int main() {\n' +
      indent +
      'std::cin.tie(0)->sync_with_stdio(0);\n' +
      mainCode +
      (() => {
        const mainNumber = procedureNameMap.get([module.moduleName, 'main'])
        if (mainNumber === undefined) return ''
        const definition = procedures.find(({ name }) => name === 'main')
        assert(definition !== undefined)
        return (
          indent +
          'procedure_' +
          mainNumber +
          '(' +
          Array(definition.variables.size).fill(0).join(', ') +
          ');\n'
        )
      })() +
      '}'
    seenModules.set(module.moduleName, module)
  }

  const mainModule = seenModules.get('')
  const mainModuleEnvironmentCode = (() => {
    if (mainModule === undefined) return ''
    const arrays = mainModule.environment?.arrays
    if (arrays === undefined) return ''
    let i = 0
    let string = ''
    for (const { itemTypes, length } of arrays.values()) {
      string +=
        'std::tuple<' +
        itemTypes.map((x) => (x === 'bool' ? x : 'u' + x + '_t')).join(', ') +
        '> environment_' +
        i +
        '[' +
        length.raw +
        '];\n'
      i++
    }
    return string
  })()

  const mainFunctionCall = (() => {
    if (mainModule === undefined) return ''
    const arrays = mainModule.environment?.arrays
    const environmentArguments = (() => {
      if (arrays === undefined) return ''
      return Array.from({ length: arrays.size }).map(
        (_, index) => 'environment_' + index
      )
    })()
    const procedure = crossModuleProcedureMap.get(['', 'main'])
    if (procedure === undefined) return ''
    const localVariableCount = procedure.variables.size
    const localVariables = Array.from({ length: localVariableCount }).fill('0')
    const procedureId = procedureNameMap.get(['', 'main'])
    if (procedureId === undefined) throw new Error("shouldn't happen")
    return (
      indent +
      'procedure_' +
      procedureId +
      '(' +
      [...environmentArguments, ...localVariables].join(', ') +
      ');\n'
    )
  })()

  return (
    preamble +
    mainModuleEnvironmentCode +
    'int main() {\n' +
    indent +
    'std::cin.tie(0)->sync_with_stdio(0);\n' +
    joined +
    mainFunctionCall +
    '}\n'
  )
}
