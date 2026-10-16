import type { CoqCPAST, PrimitiveType } from './parse'

export const isFloat = (x: unknown): x is 'float32' | 'float64' =>
  x === 'float32' || x === 'float64'

export const floatFormat = (x: 'float32' | 'float64'): string =>
  x === 'float32' ? 'Binary32' : 'Binary64'

export const coqType = (x: PrimitiveType): string =>
  isFloat(x) ? '(floatValue ' + floatFormat(x) + ')' : x === 'bool' ? 'bool' : 'Z'

export const coqZero = (x: PrimitiveType): string =>
  isFloat(x)
    ? '(floatZero ' + floatFormat(x) + ')'
    : x === 'bool' ? 'false' : '0%Z'

export const cppType = (x: PrimitiveType): string =>
  isFloat(x) ? 'coqcp_' + x : x === 'bool' ? 'bool' : 'u' + x + '_t'

/** Inspect AST nodes and declarations, without matching names/string literals. */
export function usesFloats(modules: CoqCPAST[]): boolean {
  const visit = (value: unknown): boolean => {
    if (Array.isArray(value)) return value.some(visit)
    if (value instanceof Map) return [...value.values()].some(visit)
    if (value === null || typeof value !== 'object') return false
    const node = value as { type?: unknown; itemTypes?: unknown }
    if (
      node.type === 'float literal' || node.type === 'floatOp' || isFloat(node.type)
    ) return true
    if (Array.isArray(node.itemTypes) && node.itemTypes.some(isFloat)) return true
    return Object.values(value).some(visit)
  }
  return visit(modules)
}

export interface FloatInstruction {
  args: PrimitiveType[]
  result: PrimitiveType
  coq: string
  cpp: string
  trap?: boolean
}

export const floatInstructions: Record<string, FloatInstruction> =
  Object.create(null)

for (const size of [32, 64]) {
  const f = ('float' + size) as PrimitiveType
  const prefix = 'f' + size
  for (const op of ['Abs', 'Neg', 'Ceil', 'Floor', 'Trunc', 'Nearest', 'Sqrt']) {
    floatInstructions[prefix + op] = {
      args: [f], result: f, coq: 'float' + op,
      cpp: 'coqcp_' + op.toLowerCase(),
    }
  }
  const comparisons = ['Eq', 'Ne', 'Lt', 'Le', 'Gt', 'Ge']
  for (const op of ['Add', 'Sub', 'Mul', 'Div', 'Min', 'Max', ...comparisons]) {
    floatInstructions[prefix + op] = {
      args: [f, f], result: comparisons.includes(op) ? 'bool' : f,
      coq: 'float' + op, cpp: 'coqcp_' + op.toLowerCase(),
    }
  }
  const fmt = size === 32 ? 'Binary32' : 'Binary64'
  for (const width of [32, 64]) {
    const i = ('int' + width) as PrimitiveType
    if (width === size) {
      floatInstructions[prefix + 'ReinterpretI' + width] = {
        args: [i], result: f, coq: 'floatFromBits ' + fmt,
        cpp: 'coqcp_float' + size + '::from_bits',
      }
    }
    for (const sign of ['S', 'U']) {
      const signed = sign === 'S'
      floatInstructions[prefix + 'ConvertI' + width + sign] = {
        args: [i], result: f,
        coq: `floatConvertInt ${fmt} ${width} ${signed}`,
        cpp: `coqcp_convert<coqcp_float${size}, ${signed}>`,
      }
      for (const sat of ['', 'Sat']) {
        floatInstructions['i' + width + 'Trunc' + sat + 'F' + size + sign] = {
          args: [f], result: i,
          coq: `floatTrunc${sat}Int${sat ? '' : 'Action $STATE'} ${width} ${signed}`,
          cpp: `coqcp_trunc_int<uint${width}_t, ${signed}, ${!!sat}>`,
          trap: !sat,
        }
      }
    }
  }
}
floatInstructions.f32DemoteF64 = {
  args: ['float64'], result: 'float32',
  coq: 'floatCast Binary32', cpp: 'coqcp_cast<coqcp_float32>',
}
floatInstructions.f64PromoteF32 = {
  args: ['float32'], result: 'float64',
  coq: 'floatCast Binary64', cpp: 'coqcp_cast<coqcp_float64>',
}

/** Exact decimal/hexadecimal literal conversion with one target-format rounding.
 * Never pass through JavaScript's binary64 Number. */
export function floatLiteralBits(size: 32 | 64, input: string): string {
  let text = input.trim().toLowerCase()
  let sign = 0n
  if (/^[+-]/.test(text)) {
    sign = text[0] === '-' ? 1n : 0n
    text = text.slice(1)
  }
  const p = size === 32 ? 24n : 53n
  const bias = size === 32 ? 127n : 1023n
  const signBits = sign << BigInt(size - 1)
  const infinity = ((1n << BigInt(size === 32 ? 8 : 11)) - 1n) << (p - 1n)
  if (text === 'inf' || text === 'infinity') return (signBits | infinity).toString()
  if (text === 'nan') return (infinity | (1n << (p - 2n))).toString()
  const hex = /^0x([0-9a-f]+)(?:\.([0-9a-f]*))?p([+-]?\d+)$/.exec(text)
  const dec = /^(?:(\d+)(?:\.(\d*))?|\.(\d+))(?:e([+-]?\d+))?$/.exec(text)
  if (!hex && !dec) throw new Error('invalid floating-point literal: ' + input)
  const fraction = hex ? hex[2] || '' : dec![2] || dec![3] || ''
  const digits = hex ? hex[1] + fraction : (dec![1] || '') + fraction
  let n = BigInt((hex ? '0x' : '') + (digits || '0'))
  let d = 1n
  if (n === 0n) return signBits.toString()
  const exponent = BigInt(hex ? hex[3] : dec![4] || '0') -
    BigInt(fraction.length) * (hex ? 4n : 1n)
  // Bound work for huge exponents; these bounds exceed binary64's entire range.
  if (exponent > 20000n) return (signBits | infinity).toString()
  if (exponent < -20000n - BigInt(digits.length) * 4n) return signBits.toString()
  const base = hex ? 2n : 10n
  if (exponent >= 0n) n *= base ** exponent
  else d = base ** -exponent

  let top = BigInt(n.toString(2).length - d.toString(2).length)
  if (top >= 0n ? n < (d << top) : (n << -top) < d) top--
  const emin = 1n - bias - (p - 1n)
  let e = top - (p - 1n)
  if (e < emin) e = emin
  if (e > 0n) d <<= e
  else n <<= -e

  let q = n / d
  const r = n % d
  if (2n*r > d || (2n*r === d && (q & 1n) !== 0n)) q++
  if (q >= (1n << p)) {
    q >>= 1n
    e++
  }
  if (e + p - 1n > bias) return (signBits | infinity).toString()
  const hidden = 1n << (p - 1n)
  return (signBits | (q < hidden
    ? q
    : ((e + bias + p - 1n) << (p - 1n)) | (q - hidden))).toString()
}
