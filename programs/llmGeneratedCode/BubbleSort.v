From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Coq.Strings.Ascii.
Open Scope type_scope.
Inductive arrayIndex0 :=
| arraydef_0__data.

Definition environment0 : Environment arrayIndex0 := {| arrayType := fun name => match name with | arraydef_0__data => Z end; arrays := fun name => match name with | arraydef_0__data => repeat (0%Z) 10 end |}.

#[export] Instance arrayIndexEqualityDecidable0 : EqDecision arrayIndex0 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable0 name : EqDecision (arrayType _ environment0 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__main :=
| vardef_0__main_i
| vardef_0__main_j
| vardef_0__main_current_int
| vardef_0__main_temp
| vardef_0__main_array_size.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) (addresses : varsfuncdef_0__main -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((Done _ _ _ 10%Z) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_array_size) x) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_array_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_int) x)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 8%Z) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_int)) (multInt 64 (((addInt 64 (multInt 64 binder_0 (Done _ _ _ 8%Z)) binder_1) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 64)) (shiftLeft 64 (Done _ _ _ 1%Z) (multInt 64 (subInt 64 (Done _ _ _ 7%Z) binder_1) (Done _ _ _ 8%Z))))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_int) x)) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current_int)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_array_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((subInt 64 (subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_array_size)) (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_i))) (Done _ _ _ 1%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop ((((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x) >>= fun a => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
      (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_temp) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) >>= fun x => (((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_j)) (Done _ _ _ 1%Z)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__data) x y)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
