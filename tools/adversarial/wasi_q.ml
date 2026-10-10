type t = Ratio.ratio
(* Rocq expects Zarith's canonical rationals. Num otherwise leaves arithmetic
   results unreduced, making numerator/denominator extraction incompatible and
   allowing repeated solver operations to grow intermediate values rapidly. *)
let () = Arith_status.set_normalize_ratio true
let make a b = Ratio.normalize_ratio (Ratio.create_ratio a b)
let num n = Ratio.numerator_ratio (Ratio.normalize_ratio n)
let den n = Ratio.denominator_ratio (Ratio.normalize_ratio n)
let of_bigint = Ratio.ratio_of_big_int
let of_int = Ratio.ratio_of_int
let zero = of_int 0
let one = of_int 1
let minus_one = of_int (-1)
let neg = Ratio.minus_ratio
let abs = Ratio.abs_ratio
let add = Ratio.add_ratio
let sub = Ratio.sub_ratio
let mul = Ratio.mult_ratio
let div = Ratio.div_ratio
let inv = Ratio.inverse_ratio
let sign = Ratio.sign_ratio
let compare = Ratio.compare_ratio
let equal = Ratio.eq_ratio
let lt = Ratio.lt_ratio
let gt = Ratio.gt_ratio
let leq = Ratio.le_ratio
let geq = Ratio.ge_ratio
let min = Ratio.min_ratio
let max = Ratio.max_ratio
let to_bigint n = Z.div (num n) (den n)
let to_int n = Z.to_int (to_bigint n)
let to_float = Ratio.float_of_ratio
let to_string n =
  let numerator = Z.to_string (num n) and denominator = den n in
  if Z.equal denominator Z.one then numerator
  else numerator ^ "/" ^ Z.to_string denominator
let of_string = Ratio.ratio_of_string
let of_float f =
  if not (Float.is_finite f) then invalid_arg "Non-finite rational";
  if f = 0. then zero else
  let m, e = Float.frexp f in
  let numerator = Z.of_int64 (Int64.of_float (Float.ldexp m 53)) in
  if e >= 53 then of_bigint (Z.mul numerator (Z.pow (Z.of_int 2) (e - 53)))
  else make numerator (Z.pow (Z.of_int 2) (53 - e))
let ( + ) = add
let ( - ) = sub
let ( * ) = mul
let ( / ) = div
let ( ~- ) = neg
