/** Native IEEE operations. No software floating-point emulation or new library. */
export const floatRuntime = String.raw`
#include <cstdint>
#include <cstdlib>
#include <bit>
#include <cfloat>
#include <cmath>
#include <cfenv>
#include <limits>
#include <type_traits>
#if defined(__SSE2__)
#include <xmmintrin.h>
#elif !defined(__aarch64__)
#error "CoqCP floats require an SSE2 or AArch64 IEEE floating-point target"
#endif
#ifdef __FAST_MATH__
#error "CoqCP floats cannot be compiled with fast-math"
#endif
#if defined(__clang__)
#pragma STDC FENV_ACCESS ON
#pragma clang fp contract(off)
#elif defined(__GNUC__)
#pragma GCC optimize ("rounding-math", "no-fast-math", "fp-contract=off")
#endif
static_assert(FLT_EVAL_METHOD == 0, "CoqCP requires evaluation in the declared binary32/binary64 format");
struct coqcp_float_environment {
  coqcp_float_environment() {
    if (std::fesetenv(FE_DFL_ENV) || std::fesetround(FE_TONEAREST)) std::abort();
#if defined(__SSE2__)
    // Clear rounding-control, flush-to-zero, and denormals-are-zero bits.
    _mm_setcsr((_mm_getcsr() & ~unsigned(0xE040)) | 0x1F80);
#elif defined(__aarch64__)
    uint64_t control;
    asm volatile("mrs %0, fpcr" : "=r"(control));
    control &= ~((uint64_t(3) << 22) | (uint64_t(1) << 24) | (uint64_t(1) << 19) | (uint64_t(31) << 8) | uint64_t(3));
    asm volatile("msr fpcr, %0; isb" :: "r"(control) : "memory");
#endif
  }
};
template<class Native, class Word> class coqcp_float {
  Native value_ = Native(0);
public:
  using native_type = Native;
  using word_type = Word;
  static_assert(std::numeric_limits<Native>::is_iec559);
  static_assert(sizeof(Native) == sizeof(Word));
  coqcp_float() = default;
  // Only integer zero is supplied implicitly, for default-initialized locals.
  coqcp_float(int zero) { if (zero != 0) std::abort(); }
  static coqcp_float from_native(Native value) {
    coqcp_float result;
    // NaN sign and payload may remain in hardware, but the DSL has no
    // operation that can observe them. Avoid a NaN check on every arithmetic op.
    result.value_ = value;
    return result;
  }
  static coqcp_float from_bits(Word bits) { return from_native(std::bit_cast<Native>(bits)); }
  Native native() const { return value_; }
  friend coqcp_float operator+(coqcp_float a) { return a; }
  friend coqcp_float operator-(coqcp_float a) { return from_native(-a.value_); }
  friend coqcp_float operator+(coqcp_float a, coqcp_float b) { return from_native(a.value_ + b.value_); }
  friend coqcp_float operator-(coqcp_float a, coqcp_float b) { return from_native(a.value_ - b.value_); }
  friend coqcp_float operator*(coqcp_float a, coqcp_float b) { return from_native(a.value_ * b.value_); }
  friend coqcp_float operator/(coqcp_float a, coqcp_float b) { return from_native(a.value_ / b.value_); }
  friend bool operator==(coqcp_float a, coqcp_float b) { return a.value_ == b.value_; }
  friend bool operator!=(coqcp_float a, coqcp_float b) { return a.value_ != b.value_; }
  friend bool operator<(coqcp_float a, coqcp_float b) { return a.value_ < b.value_; }
  friend bool operator<=(coqcp_float a, coqcp_float b) { return a.value_ <= b.value_; }
  friend bool operator>(coqcp_float a, coqcp_float b) { return a.value_ > b.value_; }
  friend bool operator>=(coqcp_float a, coqcp_float b) { return a.value_ >= b.value_; }
};
using coqcp_float32 = coqcp_float<float, uint32_t>;
using coqcp_float64 = coqcp_float<double, uint64_t>;
static_assert(std::numeric_limits<float>::digits == 24 && std::numeric_limits<float>::max_exponent == 128);
static_assert(std::numeric_limits<double>::digits == 53 && std::numeric_limits<double>::max_exponent == 1024);
template<class F> F coqcp_abs(F x) { return F::from_native(std::fabs(x.native())); }
template<class F> F coqcp_neg(F x) { return -x; }
template<class F> F coqcp_sqrt(F x) { volatile typename F::native_type r = std::sqrt(x.native()); return F::from_native(r); }
template<class F> F coqcp_ceil(F x) { return F::from_native(std::ceil(x.native())); }
template<class F> F coqcp_floor(F x) { return F::from_native(std::floor(x.native())); }
template<class F> F coqcp_trunc(F x) { return F::from_native(std::trunc(x.native())); }
template<class F> F coqcp_nearest(F x) { return F::from_native(std::nearbyint(x.native())); }
template<class F> F coqcp_add(F a, F b) { return a+b; }
template<class F> F coqcp_sub(F a, F b) { return a-b; }
template<class F> F coqcp_mul(F a, F b) { return a*b; }
template<class F> F coqcp_div(F a, F b) { return a/b; }
template<class F> bool coqcp_eq(F a, F b) { return a==b; }
template<class F> bool coqcp_ne(F a, F b) { return a!=b; }
template<class F> bool coqcp_lt(F a, F b) { return a<b; }
template<class F> bool coqcp_le(F a, F b) { return a<=b; }
template<class F> bool coqcp_gt(F a, F b) { return a>b; }
template<class F> bool coqcp_ge(F a, F b) { return a>=b; }
template<class F> F coqcp_min(F a, F b) {
  if (std::isnan(a.native()) || std::isnan(b.native())) return F::from_native(std::numeric_limits<typename F::native_type>::quiet_NaN());
  if (a.native() == 0 && b.native() == 0) return F::from_native(std::signbit(a.native()) || std::signbit(b.native()) ? -typename F::native_type(0) : typename F::native_type(0));
  return a < b ? a : b;
}
template<class F> F coqcp_max(F a, F b) {
  if (std::isnan(a.native()) || std::isnan(b.native())) return F::from_native(std::numeric_limits<typename F::native_type>::quiet_NaN());
  if (a.native() == 0 && b.native() == 0) return F::from_native(std::signbit(a.native()) && std::signbit(b.native()) ? -typename F::native_type(0) : typename F::native_type(0));
  return a > b ? a : b;
}
template<class F, bool Signed, class I> F coqcp_convert(I x) {
  using N = typename F::native_type;
  if constexpr (Signed) { volatile N r = static_cast<N>(std::bit_cast<std::make_signed_t<I>>(x)); return F::from_native(r); }
  else { volatile N r = static_cast<N>(x); return F::from_native(r); }
}
template<class F, class G> F coqcp_cast(G x) { volatile typename F::native_type r = static_cast<typename F::native_type>(x.native()); return F::from_native(r); }
template<class I, bool Signed, bool Saturating, class F> I coqcp_trunc_int(F x) {
  // Powers of two are exactly representable in both formats. Check the
  // truncated value before casting, so no undefined C++ float-to-int occurs.
  using N = typename F::native_type;
  constexpr unsigned width = sizeof(I)*8;
  N v = std::trunc(x.native());
  N limit = std::ldexp(N(1), Signed ? width-1 : width);
  N lower = Signed ? -limit : N(0);
  if (std::isnan(v)) { if constexpr (Saturating) return 0; else std::abort(); }
  if (v < lower) { if constexpr (Saturating) return Signed ? I(1) << (width-1) : I(0); else std::abort(); }
  if (v >= limit) { if constexpr (Saturating) return Signed ? (I(1) << (width-1))-1 : I(-1); else std::abort(); }
  if constexpr (Signed) return static_cast<I>(static_cast<std::make_signed_t<I>>(v));
  else return static_cast<I>(v);
}
// Keep these directives active for generated procedures as well: inlining
// and expression optimization must preserve the same floating-point rules.
`
