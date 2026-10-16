import { CoqCPASTTransformer } from './parse'
import { sortModules } from './dependencyGraph'
import { validateAST } from './validateAST'
import { cppCodegen } from './cppCodegen'
import { coqCodegen } from './coqCodegen'
import { floatInstructions, floatLiteralBits } from './floatInstructions'
import { floatRuntime } from './floatRuntime'
import { execFileSync, spawnSync } from 'child_process'
import { mkdtempSync, writeFileSync, rmSync } from 'fs'
import { tmpdir } from 'os'
import path from 'path'

const rocq = process.env.ROCQ || '/opt/rocq/9.3.0/bin/rocq'
const parse = (source) => new CoqCPASTTransformer(source).transform()
const compile = (sources) => {
  const modules = sortModules(sources.map(parse))
  expect(validateAST(modules)).toEqual([])
  return { cpp: cppCodegen(modules), coq: coqCodegen(modules) }
}
const temporary = (fn) => {
  const directory = mkdtempSync(path.join(tmpdir(), 'coqcp-floats-'))
  try {
    return fn(directory)
  } finally {
    rmSync(directory, { recursive: true, force: true })
  }
}
const buildNative = (directory, cpp, flags = []) => {
  const source = path.join(directory, 'program.cpp'),
    executable = path.join(directory, 'program')
  writeFileSync(source, cpp)
  execFileSync(
    'g++',
    [
      '-std=c++20',
      '-O2',
      '-Wall',
      '-Wextra',
      ...flags,
      source,
      '-o',
      executable,
    ],
    { stdio: 'pipe' }
  )
  return executable
}
const compileCoq = (directory, coq) => {
  const file = path.join(directory, 'Floats.v')
  writeFileSync(file, coq)
  execFileSync(
    rocq,
    [
      'compile',
      '-q',
      '-R',
      path.resolve(__dirname, '../theories'),
      'CoqCP',
      file,
    ],
    { stdio: 'pipe' }
  )
}

test('float literals round directly to the target format, including ties and subnormals', () => {
  const bits = (s, text) => BigInt(floatLiteralBits(s, text))
  expect(bits(32, '1.000000059604644775390625')).toBe(0x3f800000n)
  // Just above the f32 midpoint, but rounds to that midpoint in binary64.
  expect(bits(32, '1.0000000596046447753906250000000001')).toBe(0x3f800001n)
  expect(bits(32, '0x1p-150')).toBe(0n)
  expect(bits(32, '0x1.000001p-150')).toBe(1n)
  expect(bits(64, '0x1p-1074')).toBe(1n)
  expect(bits(64, '-0')).toBe(1n << 63n)
  expect(bits(64, '1e999999999')).toBe(0x7ff0000000000000n)
  expect(bits(32, '-1e-999999999')).toBe(1n << 31n)
  expect(bits(32, '-nan')).toBe(bits(32, 'nan'))
  expect(() => bits(32, 'nan:0x123')).toThrow()
})

test.each([
  'f32Copysign(f32(1), f32("nan"))',
  'i32ReinterpretF32(f32(1))',
  'i64ReinterpretF64(f64(1))',
  'f64Copysign(f64(1), f64("nan"))',
])('rejects NaN bit observers: %s', (expression) => {
  expect(() =>
    parse(`procedure('main', {}, () => { ${expression} })`)
  ).toThrow()
})
test.each([
  'f32(1) + f64(1)',
  'coerceInt32(f32(1))',
  'f32(1) | f32(2)',
  '~f64(1)',
  'sDivide(f32(1), f32(2))',
  'sLess(f64(1), f64(2))',
  'f32Add(f32(1), 1)',
  'f32ConvertI32S(1)',
])('rejects invalid float typing: %s', (expression) => {
  expect(
    validateAST([
      parse(`procedure('main', {r: int32}, () => { set('r', ${expression}) })`),
    ])
  ).not.toEqual([])
})

test(
  'every supported scalar instruction compiles in both backends',
  () =>
    temporary((directory) => {
      const value = (type) =>
        type === 'float32'
          ? 'f32(1)'
          : type === 'float64'
            ? 'f64(1)'
            : type === 'int32'
              ? 'coerceInt32(1)'
              : '1'
      const body = Object.entries(floatInstructions)
        .map(([name, op]) => name + '(' + op.args.map(value).join(', ') + ')')
        .join('\n')
      const { cpp, coq } = compile([`procedure('main', {}, () => { ${body} })`])
      expect(
        execFileSync(buildNative(directory, cpp), { encoding: 'utf8' })
      ).toBe('')
      compileCoq(directory, coq)
    }),
  60000
)

test(
  'floats survive locals, array growth, loops, tuples, defaults and cross-module arguments',
  () =>
    temporary((directory) => {
      const { cpp, coq } = compile([
        `module(Helper)
     environment({ a: array([float32, float64, bool], 0) })
     procedure('save', { x: float32, y: float64, zero: float64 }, () => {
       grow('a', 2)
       range(1, i => { store('a', 1, [get('x'), get('y') + get('zero'), true]) })
     })`,
        `environment({ a: array([float32, float64, bool], 0) })
     procedure('local', { x: float32 }, () => {
       writeChar(coerceInt8(i32TruncF32U(get('x'))))
     })
     procedure('main', { x: float32, y: float64 }, () => {
       set('x', f32(64) + f32(1))
       set('y', -f64("-66"))
       call(Helper, {a: 'a'}, 'save', {x: get('x'), y: get('y')})
       set('x', retrieve('a', 1)[0])
       set('y', retrieve('a', 1)[1])
       call('local', {x: get('x')})
       writeChar(coerceInt8(i64TruncF64U(get('y'))))
       if (retrieve('a', 1)[2] && f32Eq(retrieve('a', 0)[0], f32(0))) { writeChar(coerceInt8(67)) }
       set('x', f32Sub(f32Mul(f32('0x1.0008p0'), f32('0x1.fffp-1')), f32(1)))
       set('y', f64Sub(f64Mul(f64('0x1.0000002p0'), f64('0x1.ffffffcp-1')), f64(1)))
       if (get('x') == f32(0) && get('y') == f64(0)) { writeChar(coerceInt8(68)) }
     })`,
      ])
      expect(
        execFileSync(
          buildNative(directory, cpp, [
            '-O3',
            '-march=native',
            '-ffp-contract=fast',
          ]),
          { encoding: 'utf8' }
        )
      ).toBe('ABCD')
      compileCoq(
        directory,
        coq +
          `
From CoqCP Require Import Execution.
Example generated_float_execution :
  option_map (fun result => stdout (snd result))
    (exec (funcdef_0__main (fun _ => false) (fun _ => 0%Z))
      {| memory := arrays _ environment1; stdin := []; stdout := [] |}) =
  Some [65%Z;66%Z;67%Z;68%Z].
Proof. vm_compute. reflexivity. Qed.
`
      )
    }),
  60000
)

// Encode tiny Wasm modules directly: the test oracle is Node's built-in Wasm
// engine, with bit reinterpretation confined to tests, never the source DSL.
const leb = (n) => {
  const r = []
  do {
    let b = n & 127
    n >>>= 7
    r.push(b | (n ? 128 : 0))
  } while (n)
  return r
}
const vec = (xs) => [...leb(xs.length), ...xs.flat()]
const section = (id, xs) => [id, ...leb(xs.length), ...xs]
const instructions = {}
for (const [size, base, compare] of [
  [32, 0x8b, 0x5b],
  [64, 0x99, 0x61],
]) {
  ;[
    'Abs',
    'Neg',
    'Ceil',
    'Floor',
    'Trunc',
    'Nearest',
    'Sqrt',
    'Add',
    'Sub',
    'Mul',
    'Div',
    'Min',
    'Max',
  ].forEach((op, i) => (instructions[`f${size}${op}`] = [base + i]))
  ;['Eq', 'Ne', 'Lt', 'Gt', 'Le', 'Ge'].forEach(
    (op, i) => (instructions[`f${size}${op}`] = [compare + i])
  )
}
Object.assign(instructions, {
  f32ConvertI32S: [0xb2],
  f32ConvertI32U: [0xb3],
  f32ConvertI64S: [0xb4],
  f32ConvertI64U: [0xb5],
  f32DemoteF64: [0xb6],
  f64ConvertI32S: [0xb7],
  f64ConvertI32U: [0xb8],
  f64ConvertI64S: [0xb9],
  f64ConvertI64U: [0xba],
  f64PromoteF32: [0xbb],
  f32ReinterpretI32: [0xbe],
  f64ReinterpretI64: [0xbf],
})
for (const [iwidth, fwidth, base, satbase] of [
  [32, 32, 0xa8, 0],
  [32, 64, 0xaa, 2],
  [64, 32, 0xae, 4],
  [64, 64, 0xb0, 6],
])
  for (const [sign, offset] of [
    ['S', 0],
    ['U', 1],
  ]) {
    instructions[`i${iwidth}TruncF${fwidth}${sign}`] = [base + offset]
    instructions[`i${iwidth}TruncSatF${fwidth}${sign}`] = [
      0xfc,
      satbase + offset,
    ]
  }
const wasmFunction = (name, op) => {
  const is64 = (t) => t.endsWith('64')
  const type = (t) => (is64(t) ? 0x7e : 0x7f)
  const code = [0]
  op.args.forEach((t, i) => {
    code.push(0x20, i)
    if (t.startsWith('float')) code.push(is64(t) ? 0xbf : 0xbe)
  })
  code.push(...instructions[name])
  if (op.result.startsWith('float')) code.push(is64(op.result) ? 0xbd : 0xbc)
  code.push(0x0b)
  const binary = [
    0,
    97,
    115,
    109,
    1,
    0,
    0,
    0,
    ...section(
      1,
      vec([[0x60, ...vec(op.args.map((t) => [type(t)])), 1, type(op.result)]])
    ),
    ...section(3, vec([[0]])),
    ...section(7, vec([[1, 102, 0, 0]])),
    ...section(10, vec([[...leb(code.length), ...code]])),
  ]
  return new WebAssembly.Instance(
    new WebAssembly.Module(Uint8Array.from(binary))
  ).exports.f
}
const canonical = (result, type) => {
  const width = type === 'bool' ? 32 : Number(type.match(/\d+/)[0])
  let bits = BigInt.asUintN(width, BigInt(result))
  if (type.startsWith('float')) {
    const frac = width === 32 ? 23n : 52n,
      exp = width === 32 ? 255n : 2047n
    if (((bits >> frac) & exp) === exp && (bits & ((1n << frac) - 1n)) !== 0n)
      bits = (exp << frac) | (1n << (frac - 1n))
  }
  return bits.toString()
}

test(
  'native IEEE results match Wasm for all scalar operations and boundary cases',
  () =>
    temporary((directory) => {
      const entries = Object.entries(floatInstructions)
      let cases = '',
        input = '',
        expected = [],
        coqChecks = [],
        traps = []
      const edge32 = [
        0n,
        0x80000000n,
        1n,
        0x80000001n,
        0x007fffffn,
        0x00800000n,
        0x3f000000n,
        0xbf000000n,
        0x3fc00000n,
        0x40200000n,
        0x3f800000n,
        0xbf800000n,
        0x7f7fffffn,
        0x7f800000n,
        0xff800000n,
        0x7fc00001n,
        0xff800001n,
        0x4f000000n,
        0xcf000000n,
        0x5f000000n,
        0xdf000000n,
      ]
      const edge64 = [
        0n,
        1n << 63n,
        1n,
        (1n << 63n) | 1n,
        0x000fffffffffffffn,
        0x0010000000000000n,
        0x3fe0000000000000n,
        0xbfe0000000000000n,
        0x3ff8000000000000n,
        0x4004000000000000n,
        0x3ff0000000000000n,
        0xbff0000000000000n,
        0x7fefffffffffffffn,
        0x7ff0000000000000n,
        0xfff0000000000000n,
        0x7ff0000000000001n,
        0xfff8000000000001n,
        0x43e0000000000000n,
        0xc3e0000000000000n,
        0x43f0000000000000n,
        0xc3f0000000000000n,
      ]
      let seed = 0x974bac92856de021n
      const random = (width) => {
        seed = BigInt.asUintN(64, seed ^ (seed << 13n))
        seed ^= seed >> 7n
        seed = BigInt.asUintN(64, seed ^ (seed << 17n))
        return BigInt.asUintN(width, seed)
      }
      const argCPP = (type, i) =>
        type.startsWith('float')
          ? `coqcp_${type}::from_bits(static_cast<uint${type.slice(5)}_t>(a${i}))`
          : `static_cast<u${type}_t>(a${i})`
      const intEdges = (width) => [
        0n,
        1n,
        (1n << BigInt(width - 1)) - 1n,
        1n << BigInt(width - 1),
        (1n << BigInt(width)) - 1n,
        (1n << 24n) + 1n,
        (1n << 24n) + 3n,
      ]
      entries.forEach(([name, op], index) => {
        const result = op.result.startsWith('float')
          ? `std::bit_cast<typename decltype(r)::word_type>(r.native())`
          : 'r'
        cases += `case ${index}: { auto r = ${op.cpp}(${op.args.map(argCPP).join(',')}); std::cout << static_cast<uint64_t>(${result}) << '\\n'; break; }\n`
        const fn = wasmFunction(name, op)
        const add = (args, checkCoq = false) => {
          const wasmArgs = args.map((arg, i) =>
            op.args[i].endsWith('64')
              ? BigInt.asIntN(64, arg)
              : Number(BigInt.asIntN(32, arg))
          )
          let result
          try {
            result = fn(...wasmArgs)
          } catch (e) {
            if (!(e instanceof WebAssembly.RuntimeError)) throw e
            if (checkCoq) {
              traps.push(`${index} ${args[0]} ${args[1] || 0n}\n`)
              const fmt = op.args[0] === 'float32' ? 'Binary32' : 'Binary64'
              coqChecks.push(
                `(floatTruncInt ${name.startsWith('i32') ? 32 : 64} ${name.endsWith('S')} (floatFromBits ${fmt} ${args[0]})) = None`
              )
            }
            return
          }
          if (checkCoq) {
            const literal = (bits, type) =>
              type.startsWith('float')
                ? `(floatFromBits ${type === 'float32' ? 'Binary32' : 'Binary64'} ${bits})`
                : type === 'bool'
                  ? BigInt(bits) === 0n
                    ? 'false'
                    : 'true'
                  : `${bits}%Z`
            const operation = op.trap
              ? op.coq.replace('Action $STATE', '')
              : op.coq
            const expression = `(${operation} ${args.map((arg, i) => literal(arg, op.args[i])).join(' ')})`
            const value = literal(canonical(result, op.result), op.result)
            coqChecks.push(
              `${expression} = ${op.trap ? '(Some ' + value + ')' : value}`
            )
          }
          expected.push(canonical(result, op.result))
          input += `${index} ${args[0]} ${args[1] || 0n}\n`
        }
        const edge = op.args.map((type) =>
          type.startsWith('int')
            ? intEdges(Number(type.slice(3)))
            : type.endsWith('64')
              ? edge64
              : edge32
        )
        if (op.args.length === 2)
          for (const a of edge[0])
            for (const b of edge[1])
              add([a, b], edge[0].indexOf(a) < 5 || edge[1].indexOf(b) === 10)
        else for (const a of edge[0]) add([a], true)
        for (let i = 0; i < 1000; i++)
          add(
            op.args.map((type) => random(type.endsWith('64') ? 64 : 32)),
            i < 5
          )
      })
      const cpp =
        '#include <iostream>\n#include <cstdint>\n#include <cstdlib>\n' +
        floatRuntime +
        `
  int main() {
    // Deliberately dirty the incoming environment. Startup must restore Wasm.
    std::fesetround(FE_UPWARD);
    #if defined(__SSE2__)
    _mm_setcsr(_mm_getcsr() | 0x8040);
    #endif
    coqcp_float_environment environment;
    unsigned op; uint64_t a0,a1;
    while(std::cin >> op >> a0 >> a1) { switch(op) { ${cases} } }
  }`
      const executable = buildNative(directory, cpp, [
        '-ffp-contract=fast',
        '-fsanitize=undefined',
      ])
      const actual = execFileSync(executable, {
        input,
        encoding: 'utf8',
        maxBuffer: 16 * 1024 * 1024,
      })
        .trim()
        .split('\n')
      expect(actual).toHaveLength(expected.length)
      const lines = input.trim().split('\n')
      const outputs = actual.map((value, i) =>
        canonical(value, entries[Number(lines[i].split(' ')[0])][1].result)
      )
      expect(outputs).toEqual(expected)
      for (const input of traps) {
        const result = spawnSync(executable, { input, cwd: directory })
        expect(result.signal).toBe('SIGABRT')
      }
      compileCoq(
        directory,
        `From CoqCP Require Import Options FloatingPoint.\nFrom stdpp Require Import list.\nLocal Open Scope Z_scope.\n` +
          coqChecks
            .map(
              (check, i) =>
                `Example wasm_case_${i} : ${check}. Proof. vm_compute. reflexivity. Qed.\n`
            )
            .join('')
      )
    }),
  60000
)

test(
  'float expressions and reordered procedure presets preserve source evaluation order',
  () =>
    temporary((directory) => {
      const { cpp, coq } = compile([
        `module(Helper)
     procedure('out', { x: float32, y: float32 }, () => {
       writeChar(coerceInt8(i32TruncF32U(get('x'))))
       writeChar(coerceInt8(i32TruncF32U(get('y'))))
     })`,
        `procedure('out', { x: float64, y: float64 }, () => {
       writeChar(coerceInt8(i32TruncF64U(get('x'))))
       writeChar(coerceInt8(i32TruncF64U(get('y'))))
     })
     procedure('main', {}, () => {
       call('out', {y: f64ConvertI64U(readChar()), x: f64ConvertI64U(readChar())})
       call(Helper, {}, 'out', {y: f32ConvertI64U(readChar()), x: f32ConvertI64U(readChar())})
       writeChar(coerceInt8(i32TruncF32U(f32Sub(f32ConvertI64U(readChar()), f32ConvertI64U(readChar())))))
     })`,
      ])
      expect(
        execFileSync(buildNative(directory, cpp), {
          input: 'ABCDBA',
          encoding: 'utf8',
        })
      ).toBe('BADC\x01')
      compileCoq(
        directory,
        coq +
          `
From CoqCP Require Import Execution.
Example evaluation_order :
  option_map (fun result => stdout (snd result))
    (exec (funcdef_0__main (fun _ => false) (fun _ => 0%Z))
      {| memory := arrays _ environment1; stdin := [65%Z;66%Z;67%Z;68%Z;66%Z;65%Z]; stdout := [] |}) =
  Some [66%Z;65%Z;68%Z;67%Z;1%Z].
Proof. vm_compute. reflexivity. Qed.
`
      )
    }),
  30000
)
