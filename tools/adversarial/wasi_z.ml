(* Portable arithmetic for the WASI compiler. Num's bignum primitives have
   Wasm implementations in wasm_of_ocaml; Zarith's stubs require JavaScript. *)
type t = Big_int.big_int
exception Overflow
let zero = Big_int.zero_big_int
let one = Big_int.unit_big_int
let of_int = Big_int.big_int_of_int
let of_int64 = Big_int.big_int_of_int64
let to_int n = try Big_int.int_of_big_int n with Failure _ -> raise Overflow
let to_int64 n = try Big_int.int64_of_big_int n with Failure _ -> raise Overflow
let to_string = Big_int.string_of_big_int
let of_string = Big_int.big_int_of_string
let sign = Big_int.sign_big_int
let abs = Big_int.abs_big_int
let neg = Big_int.minus_big_int
let add = Big_int.add_big_int
let sub = Big_int.sub_big_int
let mul = Big_int.mult_big_int
let succ = Big_int.succ_big_int
let pred = Big_int.pred_big_int
let compare = Big_int.compare_big_int
let equal = Big_int.eq_big_int
let lt = Big_int.lt_big_int
let gt = Big_int.gt_big_int
let leq = Big_int.le_big_int
let geq = Big_int.ge_big_int
let min = Big_int.min_big_int
let max = Big_int.max_big_int
let gcd = Big_int.gcd_big_int
let pow = Big_int.power_big_int_positive_int
let div_rem a b =
  let q, r = Big_int.quomod_big_int (abs a) (abs b) in
  (if sign a * sign b < 0 then neg q else q), (if sign a < 0 then neg r else r)
let div a b = fst (div_rem a b)
let rem a b = snd (div_rem a b)
let ediv_rem = Big_int.quomod_big_int
let ediv a b = fst (ediv_rem a b)
let erem a b = snd (ediv_rem a b)
let fdiv a b =
  let q, r = div_rem a b in
  if sign r <> 0 && sign a * sign b < 0 then pred q else q
let cdiv a b = neg (fdiv (neg a) b)
let lcm a b = if sign a = 0 || sign b = 0 then zero else abs (mul (div a (gcd a b)) b)
let is_even a = equal (rem a (of_int 2)) zero
let lognot a = neg (succ a)
let logand a b =
  if sign a >= 0 && sign b >= 0 then Big_int.and_big_int a b
  else if sign a < 0 && sign b < 0 then
    lognot (Big_int.or_big_int (lognot a) (lognot b))
  else
    let negative, positive = if sign a < 0 then a, b else b, a in
    Big_int.xor_big_int positive (Big_int.and_big_int (lognot negative) positive)
let logor a b =
  if sign a >= 0 && sign b >= 0 then Big_int.or_big_int a b
  else if sign a < 0 && sign b < 0 then
    lognot (Big_int.and_big_int (lognot a) (lognot b))
  else
    let negative, positive = if sign a < 0 then a, b else b, a in
    let inverted = lognot negative in
    lognot (Big_int.xor_big_int inverted (Big_int.and_big_int inverted positive))
let logxor a b =
  let x = if sign a < 0 then lognot a else a in
  let y = if sign b < 0 then lognot b else b in
  let result = Big_int.xor_big_int x y in
  if (sign a < 0) <> (sign b < 0) then lognot result else result
let format spec n =
  if spec = "%d" then to_string n
  else if spec = "%#x" || spec = "%x" then
    let rec digits n acc =
      if equal n zero then acc else
      let q, r = div_rem n (of_int 16) in
      digits q (String.make 1 "0123456789abcdef".[to_int r] ^ acc)
    in
    (if sign n < 0 then "-" else "") ^ (if spec = "%#x" then "0x" else "") ^
    (if equal n zero then "0" else digits (abs n) "")
  else invalid_arg "Unsupported bigint format"
let ( + ) = add
let ( - ) = sub
let ( * ) = mul
let ( / ) = div
let ( ~- ) = neg
let ( asr ) = Big_int.shift_right_big_int
let ( lsl ) = Big_int.shift_left_big_int
let ( land ) = logand
let ( lor ) = logor
let ( lxor ) = logxor
