import { mkdtempSync, rmSync, writeFileSync } from 'fs'
import { tmpdir } from 'os'
import path from 'path'
import { execFileSync } from 'child_process'
import { CoqCPASTTransformer } from './parse'
import { sortModules } from './dependencyGraph'
import { validateAST } from './validateAST'
import { analyzeArrayGrowth } from './arrayGrowth'
import { cppCodegen } from './cppCodegen'
import { coqCodegen } from './coqCodegen'

const parse = (source) => new CoqCPASTTransformer(source).transform()
const compile = (sources) => {
  const modules = sortModules(sources.map(parse))
  expect(validateAST(modules)).toEqual([])
  return { modules, cpp: cppCodegen(modules), coq: coqCodegen(modules) }
}
const runCpp = (code, input = '') => {
  const directory = mkdtempSync(path.join(tmpdir(), 'coqcp-growth-'))
  try {
    const source = path.join(directory, 'program.cpp')
    const executable = path.join(directory, 'program')
    writeFileSync(source, code)
    execFileSync('g++', [
      '-std=c++20',
      '-O1',
      '-fsanitize=address,undefined',
      source,
      '-o',
      executable,
    ])
    return execFileSync(executable, { input, encoding: 'utf8' })
  } finally {
    rmSync(directory, { recursive: true, force: true })
  }
}

test('growth preserves tuples, initializes new fields, never shrinks, and evaluates the size once', () => {
  const { cpp, coq } = compile([
    `
    environment({ data: array([int8, bool], 1), fixed: array([int8], 2) })
    procedure('extend', {}, () => {
      if (true) { range(1, (i) => { grow('data', readChar() - 48) }) }
    })
    procedure('main', {}, () => {
      store('data', 0, [coerceInt8(65), true])
      call('extend', {})
      writeChar(retrieve('data', 0)[0])
      writeChar(coerceInt8(coerceInt8(retrieve('data', 0)[1]) + coerceInt8(48)))
      writeChar(coerceInt8(retrieve('data', 2)[0] + coerceInt8(48)))
      writeChar(coerceInt8(coerceInt8(retrieve('data', 2)[1]) + coerceInt8(48)))
      store('data', 2, [coerceInt8(66), false])
      grow('data', 1)
      grow('data', 0)
      grow('data', 3)
      writeChar(retrieve('data', 2)[0])
      writeChar(coerceInt8(readChar()))
    })`,
  ])
  expect(cpp).toContain(
    'std::vector<std::tuple<uint8_t, bool>> environment_0(1)'
  )
  expect(cpp).toContain('std::tuple<uint8_t> environment_1[2]')
  expect(coq).toContain('grow arrayIndex0')
  expect(coq).toContain('size (0%Z, false)')
  expect(runCpp(cpp, '3Z')).toBe('A100BZ')
})

test('growth propagates through transitive mappings and aliases shared with read-only modules', () => {
  const { modules, cpp } = compile([
    `module(Leaf)
     environment({ x: array([int8], 1), alias: array([int8], 1) })
     procedure('extend', {}, () => {
       grow('x', 128)
       store('alias', 127, [coerceInt8(75)])
     })`,
    `module(Middle)
     environment({ y: array([int8], 1) })
     procedure('extend', {}, () => {
       call(Leaf, { x: 'y', alias: 'y' }, 'extend', {})
     })`,
    `module(Reader)
     environment({ z: array([int8], 1) })
     procedure('read', {}, () => { writeChar(retrieve('z', 0)[0]) })`,
    `environment({ a: array([int8], 1), b: array([int8], 1), fixed: array([int16], 1) })
     procedure('main', {}, () => {
       store('a', 0, [coerceInt8(65)])
       store('b', 0, [coerceInt8(66)])
       call(Middle, { y: 'a' }, 'extend', {})
       call(Reader, { z: 'a' }, 'read', {})
       call(Reader, { z: 'b' }, 'read', {})
       writeChar(retrieve('a', 127)[0])
     })`,
  ])
  const growth = analyzeArrayGrowth(modules)
  expect([...growth.get('')].sort()).toEqual(['a', 'b'])
  expect([...growth.get('Leaf')].sort()).toEqual(['alias', 'x'])
  expect(growth.get('Reader').has('z')).toBe(true)
  expect(cpp).toContain('std::tuple<uint16_t> environment_2[1]')
  expect(runCpp(cpp)).toBe('ABK')
})

test('fixed programs keep static storage and raw pointer parameters', () => {
  const { cpp } = compile([
    `
    environment({ data: array([int8], 2) })
    procedure('main', {}, () => { writeChar(retrieve('data', 0)[0]) })
  `,
  ])
  expect(cpp).toContain('std::tuple<uint8_t> environment_0[2]')
  expect(cpp).toContain('std::tuple<uint8_t> *environment_0')
  expect(cpp).not.toContain('std::vector')
})

test.each(['grow()', "grow('a')", 'grow(1, 2)', "grow('a', 2, 3)"])(
  'rejects malformed growth: %s',
  (statement) => {
    expect(() =>
      parse(`procedure('main', {}, () => { ${statement} })`)
    ).toThrow()
  }
)

test.each([
  ["grow('missing', 2)", 'undefined array'],
  ["grow('a', true)", 'instruction expects int64'],
  ["grow('a', coerceInt8(2))", 'instruction expects int64'],
  ["grow('a', grow('a', 2))", 'expression no statement'],
  ["set('x', grow('a', 2))", 'expression no statement'],
])('validates growth types: %s', (statement, errorType) => {
  const errors = validateAST([
    parse(`environment({ a: array([int8], 1) })
    procedure('main', { x: int64 }, () => { ${statement} })`),
  ])
  expect(errors.some((error) => error.type === errorType)).toBe(true)
})

test.each([
  'getSender()',
  'getMoney()',
  'communicationSize()',
  'coerceInt256(0)',
  'address()',
  "invoke(0, 0, 'a', 1)",
  'donate(0, 0)',
  'retrieve(0)',
  'store(0, 1)',
])('removes blockchain instruction: %s', (statement) => {
  expect(() => parse(`procedure('main', {}, () => { ${statement} })`)).toThrow()
})

test.each(['address', 'int256'])('removes blockchain type %s', (type) => {
  expect(() => parse(`environment({ a: array([${type}], 1) })`)).toThrow()
  expect(() => parse(`procedure('main', { x: ${type} }, () => {})`)).toThrow()
})

test('arrays that grow can start empty', () => {
  const { cpp, coq } = compile([
    `
    environment({ data: array([int8], 0) })
    procedure('main', {}, () => {
      grow('data', 2)
      store('data', 1, [coerceInt8(88)])
      writeChar(retrieve('data', 1)[0])
    })
  `,
  ])
  expect(cpp).toContain('std::vector<std::tuple<uint8_t>> environment_0(0)')
  expect(coq).toContain('repeat (0%Z) 0')
  expect(runCpp(cpp)).toBe('X')
})
