From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Coq.Strings.Ascii.
Open Scope type_scope.
Inductive arrayIndex0 :=
| arraydef_0__dp.

Definition environment0 : Environment arrayIndex0 := {| arrayType := fun name => match name with | arraydef_0__dp => Z end; arrays := fun name => match name with | arraydef_0__dp => repeat (0%Z) 1000000 end |}.

#[export] Instance arrayIndexEqualityDecidable0 : EqDecision arrayIndex0 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable0 name : EqDecision (arrayType _ environment0 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__main :=
| vardef_0__main_commSize
| vardef_0__main_temp
| vardef_0__main_remainder
| vardef_0__main_N
| vardef_0__main_pos_limit
| vardef_0__main_b0
| vardef_0__main_b1
| vardef_0__main_b2
| vardef_0__main_b3
| vardef_0__main_limit
| vardef_0__main_limit_plus_1
| vardef_0__main_product
| vardef_0__main_i_idx
| vardef_0__main_i
| vardef_0__main_i_minus_1
| vardef_0__main_pos_weight
| vardef_0__main_w0
| vardef_0__main_w1
| vardef_0__main_w2
| vardef_0__main_w3
| vardef_0__main_weight
| vardef_0__main_pos_value
| vardef_0__main_v0
| vardef_0__main_v1
| vardef_0__main_v2
| vardef_0__main_v3
| vardef_0__main_value
| vardef_0__main_current_idx
| vardef_0__main_prev_idx
| vardef_0__main_prev_val
| vardef_0__main_remaining_w
| vardef_0__main_prev_remaining_idx
| vardef_0__main_prev_remaining_val
| vardef_0__main_new_val
| vardef_0__main_max_idx
| vardef_0__main_max_value
| vardef_0__main_j
| vardef_0__main_w
| vardef_0__main_shift_val
| vardef_0__main_mod_val.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) (addresses : varsfuncdef_0__main -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((getCommunicationSize _ _ _) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_commSize) x) >>=
fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_commSize)) >>= fun a => ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  Done _ _ _ tt
) else (
  ((subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_commSize)) ((Done _ _ _ 4%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_temp) x) >>=
  fun _ => ((modIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_temp)) ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_remainder) x) >>=
  fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_remainder)) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
    Done _ _ _ tt
  ) else (
    ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_temp)) ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_N) x) >>=
    fun _ => ((multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_N)) ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_limit) x) >>=
    fun _ => ((andBits (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_limit)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b0) x) >>=
    fun _ => ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_limit)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b1) x) >>=
    fun _ => ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_limit)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b2) x) >>=
    fun _ => ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_limit)) ((Done _ _ _ 3%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b3) x) >>=
    fun _ => ((orBits (orBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b0)) ((Done _ _ _ 24%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b1)) ((Done _ _ _ 16%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b2)) ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_b3))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit) x) >>=
    fun _ => ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1) x) >>=
    fun _ => ((multInt 64 (addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_N)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_product) x) >>=
    fun _ => ((((Done _ _ _ 1000000%Z) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun a => (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_product)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
      Done _ _ _ tt
    ) else (
      ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_N)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
        (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i_idx)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i) x)) >>=
        fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i_minus_1) x)) >>=
        fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i_minus_1)) ((Done _ _ _ 4%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_weight) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_weight)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w0) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_weight)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w1) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_weight)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w2) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_weight)) ((Done _ _ _ 3%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w3) x)) >>=
        fun _ => (liftToWithinLoop ((orBits (orBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w0)) ((Done _ _ _ 24%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w1)) ((Done _ _ _ 16%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w2)) ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w3))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_weight) x)) >>=
        fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 ((Done _ _ _ 4%Z) >>= fun x => Done _ _ _ (coerceInt x 64)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_N))) (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i_minus_1)) ((Done _ _ _ 4%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_value) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_value)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v0) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_value)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v1) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_value)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v2) x)) >>=
        fun _ => (liftToWithinLoop ((andBits (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_pos_value)) ((Done _ _ _ 3%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) ((Done _ _ _ 255%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v3) x)) >>=
        fun _ => (liftToWithinLoop ((orBits (orBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v0)) ((Done _ _ _ 24%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v1)) ((Done _ _ _ 16%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) (shiftLeft 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v2)) ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64)))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_v3))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_value) x)) >>=
        fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
          (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w) x)) >>=
          fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_idx) x)) >>=
          fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i_minus_1)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_idx) x)) >>=
          fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_idx)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dp) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_val) x)) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w)) >>= fun a => (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_weight)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_idx)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_val)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dp) x y)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_w)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_weight))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_remaining_w) x)) >>=
            fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i_minus_1)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_remaining_w))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_remaining_idx) x)) >>=
            fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_remaining_idx)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dp) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_remaining_val) x)) >>=
            fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_remaining_val)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_value))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_new_val) x)) >>=
            fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_val)) >>= fun a => (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_new_val)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
              (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_idx)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_new_val)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dp) x y)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_idx)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_prev_val)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dp) x y)) >>=
              fun _ => Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ))))) >>=
        fun _ => Done _ _ _ tt
      )))) >>=
      fun _ => ((addInt 64 (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_N)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit_plus_1))) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_limit))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_idx) x) >>=
      fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_idx)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__dp) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value) x) >>=
      fun _ => ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_commSize)) >>= fun a => ((Done _ _ _ 8%Z) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
          (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y)) >>=
          fun _ => Done _ _ _ tt
        )))) >>=
        fun _ => (((Done _ _ _ 72057594037927936%Z) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 1%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 2%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 3%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 4%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 5%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val) x) >>=
        fun _ => ((Done _ _ _ 6%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_shift_val))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => ((Done _ _ _ 7%Z) >>= fun x => ((modIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_max_value)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
