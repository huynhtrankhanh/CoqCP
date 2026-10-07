From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Stdlib.Strings.Ascii.
Open Scope type_scope.
Inductive arrayIndex0 :=
| arraydef_0_PrintInt64_buffer.

Definition environment0 : Environment arrayIndex0 := {| arrayType := fun name => match name with | arraydef_0_PrintInt64_buffer => Z end; arrays := fun name => match name with | arraydef_0_PrintInt64_buffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable0 : EqDecision arrayIndex0 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable0 name : EqDecision (arrayType _ environment0 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0_PrintInt64_unsigned :=
| vardef_0_PrintInt64_unsigned_num
| vardef_0_PrintInt64_unsigned_i
| vardef_0_PrintInt64_unsigned_tmpChar.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_PrintInt64_unsigned : EqDecision varsfuncdef_0_PrintInt64_unsigned := ltac:(solve_decision).
Definition funcdef_0_PrintInt64_unsigned_body : Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue unit := ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  (((Done _ _ _ 48%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned x) >>=
  fun _ => Done _ _ _ tt
) else (
  ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i) x) >>=
  fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop (((addInt 64 (modIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) (Done _ _ _ 10%Z)) (Done _ _ _ 48%Z)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_tmpChar) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_tmpChar)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (arraydef_0_PrintInt64_buffer) x y)) >>=
    fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) (Done _ _ _ 10%Z)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num) x)) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (((subInt 64 (subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (arraydef_0_PrintInt64_buffer) x) >>= fun x => writeChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0_PrintInt64_unsigned (bools : varsfuncdef_0_PrintInt64_unsigned -> bool) (numbers : varsfuncdef_0_PrintInt64_unsigned -> Z) : Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0_PrintInt64_unsigned_body.
Inductive varsfuncdef_0_PrintInt64_signed :=
| vardef_0_PrintInt64_signed_num.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_PrintInt64_signed : EqDecision varsfuncdef_0_PrintInt64_signed := ltac:(solve_decision).
Definition funcdef_0_PrintInt64_signed_body : Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed) withLocalVariablesReturnValue unit := ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun a => (Done _ _ _ 0%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64)))) >>= fun x => if x then (
  (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun x => Done _ _ _ (coerceInt (-x) 64)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num) x) >>=
  fun _ => (((Done _ _ _ 45%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed x) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0_PrintInt64_unsigned y x)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0_PrintInt64_signed (bools : varsfuncdef_0_PrintInt64_signed -> bool) (numbers : varsfuncdef_0_PrintInt64_signed -> Z) : Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0_PrintInt64_signed_body.
Inductive arrayIndex1 :=
| arraydef_0__sequence
| arraydef_0__prefix
| arraydef_0__factorial
| arraydef_0__inverseFactorial
| arraydef_0__roots
| arraydef_0__work
| arraydef_0__other
| arraydef_0__poly
| arraydef_0__arena
| arraydef_0__frames
| arraydef_0__result
| arraydef_0__printBuffer.

Definition environment1 : Environment arrayIndex1 := {| arrayType := fun name => match name with | arraydef_0__sequence => Z | arraydef_0__prefix => Z | arraydef_0__factorial => Z | arraydef_0__inverseFactorial => Z | arraydef_0__roots => Z | arraydef_0__work => Z | arraydef_0__other => Z | arraydef_0__poly => Z | arraydef_0__arena => Z | arraydef_0__frames => Z * Z * Z * Z * Z | arraydef_0__result => Z | arraydef_0__printBuffer => Z end; arrays := fun name => match name with | arraydef_0__sequence => repeat (0%Z) 0 | arraydef_0__prefix => repeat (0%Z) 0 | arraydef_0__factorial => repeat (0%Z) 0 | arraydef_0__inverseFactorial => repeat (0%Z) 0 | arraydef_0__roots => repeat (0%Z) 0 | arraydef_0__work => repeat (0%Z) 0 | arraydef_0__other => repeat (0%Z) 0 | arraydef_0__poly => repeat (0%Z) 0 | arraydef_0__arena => repeat (0%Z) 0 | arraydef_0__frames => repeat (0%Z, 0%Z, 0%Z, 0%Z, 0%Z) 32 | arraydef_0__result => repeat (0%Z) 3 | arraydef_0__printBuffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable1 : EqDecision arrayIndex1 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable1 name : EqDecision (arrayType _ environment1 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__power :=
| vardef_0__power_base
| vardef_0__power_exponent
| vardef_0__power_answer.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__power : EqDecision varsfuncdef_0__power := ltac:(solve_decision).
Definition funcdef_0__power_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power) withLocalVariablesReturnValue unit := (((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_answer) x) >>=
fun _ => ((Done _ _ _ 64%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((modIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent)) (Done _ _ _ 2%Z)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_answer)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base))) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_answer) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base))) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base) x)) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 2%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_answer)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (arraydef_0__result) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__power (bools : varsfuncdef_0__power -> bool) (numbers : varsfuncdef_0__power -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__power_body.
Inductive varsfuncdef_0__ntt :=
| vardef_0__ntt_size
| vardef_0__ntt_j
| vardef_0__ntt_bit
| vardef_0__ntt_tmp
| vardef_0__ntt_k
| vardef_0__ntt_left
| vardef_0__ntt_right
| vardef_0__ntt_start.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__ntt : EqDecision varsfuncdef_0__ntt := ltac:(solve_decision).
Definition funcdef_0__ntt_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue unit := (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (binder_0 >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_tmp) x)) >>=
    fun _ => (liftToWithinLoop (binder_0 >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_tmp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit) x)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 21%Z) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j) x)) >>=
    fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit) x)) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)))) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((multInt 64 (multInt 64 binder_1 (Done _ _ _ 2%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) >>= fun x => loop (Z.to_nat x) (fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
      (liftToWithinLoop (((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left) x)) >>=
      fun _ => (liftToWithinLoop ((modIntUnsigned (multInt 64 ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) binder_2) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__roots) x) ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right) x)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) >>= fun x => ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => ((modIntUnsigned (subInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left)) (Done _ _ _ 998244353%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
      fun _ => Done _ _ _ tt
    ))))) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__ntt (bools : varsfuncdef_0__ntt -> bool) (numbers : varsfuncdef_0__ntt -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__ntt_body.
Inductive varsfuncdef_0__convolve :=
| vardef_0__convolve_skip
| vardef_0__convolve_length
| vardef_0__convolve_span
| vardef_0__convolve_base
| vardef_0__convolve_count
| vardef_0__convolve_size
| vardef_0__convolve_scale
| vardef_0__convolve_tmp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__convolve : EqDecision varsfuncdef_0__convolve := ltac:(solve_decision).
Definition funcdef_0__convolve_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue unit := (((addInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_length)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_skip))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_count) x) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_count)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => ((liftToWithinLoop (binder_0 >>= fun a => (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_length)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_skip))) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop (binder_0 >>= fun x => (((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_skip)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__poly) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ntt_size) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ntt y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__other) x y)) >>=
  fun _ => (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => ((liftToWithinLoop (binder_0 >>= fun a => (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span)) (Done _ _ _ 1%Z)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop (binder_0 >>= fun x => ((modIntUnsigned (multInt 64 (modIntUnsigned (multInt 64 ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__factorial) x) (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__inverseFactorial) x)) (Done _ _ _ 998244353%Z)) ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__inverseFactorial) x)) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ntt_size) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ntt y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun preset0 => (Done _ _ _ 998244351%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__power_base) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__power_exponent) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__power y x)) >>=
fun _ => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_scale) x) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((modIntUnsigned (multInt 64 (modIntUnsigned (multInt 64 (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__other) x)) (Done _ _ _ 998244353%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_scale))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((divIntUnsigned (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) (Done _ _ _ 1%Z)) (Done _ _ _ 2%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_tmp) x)) >>=
  fun _ => (liftToWithinLoop ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => (((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => (liftToWithinLoop ((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_tmp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ntt_size) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ntt y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_count)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_base)) binder_0) >>= fun x => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__arena) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__convolve (bools : varsfuncdef_0__convolve -> bool) (numbers : varsfuncdef_0__convolve -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__convolve_body.
Inductive varsfuncdef_0__solve :=
| vardef_0__solve_begin
| vardef_0__solve_end
| vardef_0__solve_reverse
| vardef_0__solve_balance
| vardef_0__solve_minimum
| vardef_0__solve_count
| vardef_0__solve_depth
| vardef_0__solve_top
| vardef_0__solve_length
| vardef_0__solve_l
| vardef_0__solve_r
| vardef_0__solve_phase
| vardef_0__solve_base
| vardef_0__solve_saved
| vardef_0__solve_middle
| vardef_0__solve_special
| vardef_0__solve_small
| vardef_0__solve_hi
| vardef_0__solve_flag
| vardef_0__solve_value
| vardef_0__solve_previous
| vardef_0__solve_size
| vardef_0__solve_ch.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__solve : EqDecision varsfuncdef_0__solve := ltac:(solve_decision).
Definition funcdef_0__solve_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x y) >>=
fun _ => ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_end)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_begin))) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (booleanLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_reverse))) >>= fun x => if x then (
    (liftToWithinLoop ((xorBits (((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_end)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__sequence) x) >>= fun x => Done _ _ _ (coerceInt x 64)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_ch) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_begin)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__sequence) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_ch) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance) x)) >>=
    fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag) x)) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_minimum)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64))))) >>= fun x => if x then (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_minimum) x)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag) x)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) (Done _ _ _ 1%Z)) >>= fun x => ((addInt 64 ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x y)) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y) >>=
fun _ => ((addInt 64 (multInt 64 (Done _ _ _ 4%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count))) (Done _ _ _ 1%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (element_tuple)))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_phase) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved) x)) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r))) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle) x)) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_phase)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun a => (Done _ _ _ 33%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
        (liftToWithinLoop ((subInt 64 ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) binder_1) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x) ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag) x)) >>=
        fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous) x)) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => loop (Z.to_nat x) (fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
            (liftToWithinLoop ((binder_2 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
            fun _ => (liftToWithinLoop (binder_2 >>= fun x => ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
            fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous) x)) >>=
            fun _ => Done _ _ _ tt
          ))))) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
          fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => loop (Z.to_nat x) (fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
            (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
            fun _ => ((liftToWithinLoop ((addInt 64 binder_2 (Done _ _ _ 1%Z)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
              (liftToWithinLoop (((addInt 64 binder_2 (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => (liftToWithinLoop (binder_2 >>= fun x => ((modIntUnsigned (addInt 64 (binder_2 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
            fun _ => Done _ _ _ tt
          ))))) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ))))) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
        (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      (liftToWithinLoop ((subInt 64 ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((subInt 64 (addInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi) x)) >>=
        fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun preset1 => (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top)) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_skip) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_length) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_span) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_base) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__convolve y x))) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun tuple_element_1 => ((Done _ _ _ 1%Z) >>= fun tuple_element_2 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top)) >>= fun tuple_element_3 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi)) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_phase)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun tuple_element_1 => ((Done _ _ _ 2%Z) >>= fun tuple_element_2 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base)) >>= fun tuple_element_3 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
        (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
        fun _ => ((liftToWithinLoop (binder_1 >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
          (liftToWithinLoop ((binder_1 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop (binder_1 >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
          (liftToWithinLoop ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__arena) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => (liftToWithinLoop (binder_1 >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
        fun _ => Done _ _ _ tt
      ))))) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
        (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__result) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__solve (bools : varsfuncdef_0__solve -> bool) (numbers : varsfuncdef_0__solve -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__solve_body.
Inductive varsfuncdef_0__main :=
| vardef_0__main_n
| vardef_0__main_ch
| vardef_0__main_balance
| vardef_0__main_minimum
| vardef_0__main_split
| vardef_0__main_size
| vardef_0__main_k
| vardef_0__main_z
| vardef_0__main_answer.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue unit := (((Done _ _ _ 500000%Z) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__sequence) size (0%Z)) >>=
fun _ => ((Done _ _ _ 500001%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 41%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__sequence) x y)) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n) x)) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_minimum)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64))))) >>= fun x => if x then (
    (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_minimum) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__prefix) size (0%Z)) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) size (0%Z)) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) size (0%Z)) >>=
fun _ => ((addInt 64 (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 64%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__poly) size (0%Z)) >>=
fun _ => ((addInt 64 (multInt 64 (Done _ _ _ 4%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 128%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__arena) size (0%Z)) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun a => (addInt 64 (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 1%Z)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__work) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__other) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) size (0%Z)) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 3%Z) >>= fun preset0 => (divIntUnsigned (Done _ _ _ 998244352%Z) (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)))) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__power_base) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__power_exponent) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__power y x))) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_z) x)) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x y)) >>=
  fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) (Done _ _ _ 1%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) binder_1) (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_z))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x y)) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x y) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x) (addInt 64 binder_0 (Done _ _ _ 1%Z))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x) >>= fun preset0 => (Done _ _ _ 998244351%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__power_base) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__power_exponent) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__power y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x y) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x) (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0)) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_begin) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_end) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__solve y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer) x) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun preset1 => (Done _ _ _ true) >>= fun preset2 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_begin) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_end) preset1)) >>= fun x => ((Done _ _ _ (fun x => false)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_reverse) preset2)) >>= fun y => liftToWithLocalVariables (funcdef_0__solve y x)) >>=
fun _ => ((modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer)) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer) x) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment1) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main x) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__main_body.
