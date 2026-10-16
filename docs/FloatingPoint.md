# Floating point

CoqCP supports `float32` (IEEE binary32) and `float64` (IEEE binary64) in
locals, array tuple fields, procedure arguments, and module interfaces. Their
default value is positive zero. Array growth initializes float fields to
positive zero and preserves existing values.

Generated C++ uses native `float` and `double`, with no software arithmetic
emulator or additional dependency. The formal model uses the `SpecFloat`
module already provided by Rocq, at precisions 24 and 53 and maximum exponents
128 and 1024. Both backends follow [WebAssembly scalar numeric semantics](https://webassembly.github.io/spec/core/exec/numerics.html),
with all NaNs identified as a single abstract value.

## Literals and expressions

```js
environment({ values: array([float32, float64], 4) })
procedure('main', { x: float32, y: float64 }, () => {
  set('x', f32('0.1'))
  set('y', f64Sqrt(f64(2)))
  store('values', 0, [get('x') + f32(1), get('y')])
})
```

`f32(...)` and `f64(...)` accept a decimal numeric literal or a string containing
a decimal number, hexadecimal float such as `'0x1.8p-2'`, `'inf'`, `'-inf'`,
`'nan'`, or `'-0'`. Strings also allow leading signs. Constants are converted
exactly to their target format with one rounding step; binary32 constants do
not pass through JavaScript's binary64 arithmetic. For example,
`f32('1.0000000596046447753906250000000001')` rounds upward, although conversion
through binary64 would incorrectly round it down. NaN payload literal syntax
is rejected.

Same-format `+`, `-`, `*`, unary `+`/`-`, `divide(a, b)`, `less(a, b)`, `==`, and
`!=` work on floats. Equality uses IEEE rules: NaN is unequal to everything,
including itself; positive and negative zero compare equal. Ordered comparisons
with NaN are false. Bit operations, remainder, signed integer operations, and
`coerceInt*` reject floats. Use explicit conversion instructions below. There
are no implicit conversions between integers, binary32, and binary64.

## Instructions

Each `fN` below is either `f32` or `f64`; `iM` is either `i32` or `i64`.
The suffix `S` means signed and `U` unsigned. Integer arguments/results use the
existing `int32`/`int64` types and their two's-complement bit encodings.

| Instructions                                   | Behavior                                                                                 |
| ---------------------------------------------- | ---------------------------------------------------------------------------------------- |
| `fNAbs`, `fNNeg`                               | Absolute value and negation                                                              |
| `fNCeil`, `fNFloor`, `fNTrunc`, `fNNearest`    | Integral rounding; nearest breaks ties to even and preserves signed zero                 |
| `fNSqrt`                                       | Correctly rounded square root                                                            |
| `fNAdd`, `fNSub`, `fNMul`, `fNDiv`             | Arithmetic with one rounding per operation                                               |
| `fNMin`, `fNMax`                               | NaN-propagating minimum/maximum; mixed zeros produce negative/positive zero respectively |
| `fNEq`, `fNNe`, `fNLt`, `fNLe`, `fNGt`, `fNGe` | IEEE comparisons                                                                         |
| `fNConvertIMS`, `fNConvertIMU`                 | Integer-to-float conversion, e.g. `f32ConvertI64U`                                       |
| `iMTruncFNS`, `iMTruncFNU`                     | Truncate toward zero, trapping on NaN, infinity, or out-of-range truncated results       |
| `iMTruncSatFNS`, `iMTruncSatFNU`               | Saturating truncation; NaN becomes zero                                                  |
| `f32DemoteF64`, `f64PromoteF32`                | Format conversion; promotion is exact                                                    |
| `f32ReinterpretI32`, `f64ReinterpretI64`       | Decode integer bits as a float; every NaN encoding denotes the same abstract NaN         |

Examples: `f32Nearest(f32('2.5'))` is 2;
`i32TruncF64U(f64('-0.9'))` is 0; `i32TruncF64U(f64('-1'))` traps.
Floating-point division by zero produces infinity or NaN, rather than an
integer-division trap. Overflow rounds to infinity; subnormals are retained.

## NaN opacity and determinism

The source language provides no float-to-integer bit reinterpretation,
`copysign`, raw byte access, or float/integer storage aliasing. `copysign` is
excluded because `copysign(1, nan)` would reveal a NaN's sign. Numerical
float-to-integer conversions trap or saturate on NaN and reveal no payload.
Typed array mappings require identical tuple types, so floats cannot be read
through integer arrays.

The Rocq value type has one NaN constructor, with no sign or payload fields.
Native NaNs may carry hardware payloads internally; no supported language
operation exposes them. Absolute value and negation are therefore deterministic
on the abstract NaN even though Wasm specifies their concrete sign-bit changes.
Signaling and quiet NaNs are indistinguishable, as in Wasm. Floating-point
exception flags are not exposed.

At generated-program startup, the runtime installs `FE_TONEAREST`
(round-to-nearest, ties-to-even), masks floating-point exception traps, and
clears flush-to-zero/denormals-are-zero controls. This happens once, rather
than around each arithmetic operation. Compiler directives disable contraction
and unsafe floating-point optimization throughout the generated procedures,
so a multiply followed by an add is rounded twice, rather than fused.

The native backend requires C++20 on an IEEE SSE2 or AArch64 target, with
operations evaluated in their declared formats (`FLT_EVAL_METHOD == 0`). Fast
math is rejected at compilation. Existing POSIX I/O requirements still apply.
The runtime uses only standard C++ headers and target control-register support;
it installs no library. The arithmetic wrapper contains a single native value
and permits inlining of the hardware operations.

## Formal model and checks

`theories/FloatingPoint.v` defines the arithmetic, comparisons, conversions,
traps, saturating operations, bit decoding, and local-variable actions. Local
float storage uses a proved lossless encoding into the existing abstract local
store; this encoding is not a source-language operation or IEEE bitcast.
`floatDecode_encode` proves round trips, `floatNaN_fields` proves that input NaN
signs/payloads disappear, `floatTruncInt_range` proves the range of successful
integer conversions, and `eliminate_float_roundtrip` proves set/get behavior
inside generated actions. `floatValid` states the finite-format invariant when
reasoning directly about arbitrary Rocq values.

The compiler tests run all scalar instruction families against Node's built-in
WebAssembly engine using edge cases and deterministic random inputs, comparing
float results modulo NaN payload/sign. They also check trapping conversions,
compute matching Rocq results, and prove byte output for generated programs
using float locals, tuples, growth, loops, and cross-module calls. Rounding-mode
and subnormal-control tests start from an intentionally incompatible host state;
contraction tests compile with optimization and fusion enabled on the command
line. CI runs these tests and the existing kernel axiom-policy check.

The compiler and C++ toolchain retain the project's existing trust boundary:
tests compare their behavior with the formal model; the compiler passes and
native machine code are not themselves formally verified.
