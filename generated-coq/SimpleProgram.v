From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Coq.Strings.Ascii.
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
Definition funcdef_0_PrintInt64_unsigned (bools : varsfuncdef_0_PrintInt64_unsigned -> bool) (numbers : varsfuncdef_0_PrintInt64_unsigned -> Z) (addresses : varsfuncdef_0_PrintInt64_unsigned -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
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
Inductive varsfuncdef_0_PrintInt64_signed :=
| vardef_0_PrintInt64_signed_num.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_PrintInt64_signed : EqDecision varsfuncdef_0_PrintInt64_signed := ltac:(solve_decision).
Definition funcdef_0_PrintInt64_signed (bools : varsfuncdef_0_PrintInt64_signed -> bool) (numbers : varsfuncdef_0_PrintInt64_signed -> Z) (addresses : varsfuncdef_0_PrintInt64_signed -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun a => (Done _ _ _ 0%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64)))) >>= fun x => if x then (
  (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun x => Done _ _ _ (coerceInt (-x) 64)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num) x) >>=
  fun _ => (((Done _ _ _ 45%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed x) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0_PrintInt64_unsigned y x z)) >>=
fun _ => Done _ _ _ tt).
Inductive arrayIndex1 :=
| arraydef_0__buffer.

Definition environment1 : Environment arrayIndex1 := {| arrayType := fun name => match name with | arraydef_0__buffer => Z end; arrays := fun name => match name with | arraydef_0__buffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable1 : EqDecision arrayIndex1 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable1 name : EqDecision (arrayType _ environment1 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__main : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) (addresses : varsfuncdef_0__main -> list Z): Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses ((loopString ("The number is ") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((addInt 64 (Done _ _ _ 1%Z) (Done _ _ _ 1%Z)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_signed_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_signed y x z) (arrayType _ environment1) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__buffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => Done _ _ _ tt).
