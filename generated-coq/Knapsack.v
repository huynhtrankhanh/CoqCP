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
| arraydef_0_ReadUnsignedInt64_resultArray.

Definition environment1 : Environment arrayIndex1 := {| arrayType := fun name => match name with | arraydef_0_ReadUnsignedInt64_resultArray => Z end; arrays := fun name => match name with | arraydef_0_ReadUnsignedInt64_resultArray => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable1 : EqDecision arrayIndex1 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable1 name : EqDecision (arrayType _ environment1 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0_ReadUnsignedInt64_ :=
| vardef_0_ReadUnsignedInt64__tmpChar
| vardef_0_ReadUnsignedInt64__result.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_ReadUnsignedInt64_ : EqDecision varsfuncdef_0_ReadUnsignedInt64_ := ltac:(solve_decision).
Definition funcdef_0_ReadUnsignedInt64__body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 48%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 58%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)))) >>= fun x => if x then (
    (continue arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result)) (Done _ _ _ 10%Z)) (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) (Done _ _ _ 48%Z))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result) x)) >>=
  fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 48%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 58%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result)) (Done _ _ _ 10%Z)) (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) (Done _ _ _ 48%Z))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_ (arraydef_0_ReadUnsignedInt64_resultArray) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0_ReadUnsignedInt64_ (bools : varsfuncdef_0_ReadUnsignedInt64_ -> bool) (numbers : varsfuncdef_0_ReadUnsignedInt64_ -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0_ReadUnsignedInt64__body.
Inductive arrayIndex2 :=
| arraydef_0__dp
| arraydef_0__weights
| arraydef_0__values
| arraydef_0__message
| arraydef_0__n
| arraydef_0__input
| arraydef_0__printBuffer.

Definition environment2 : Environment arrayIndex2 := {| arrayType := fun name => match name with | arraydef_0__dp => Z | arraydef_0__weights => Z | arraydef_0__values => Z | arraydef_0__message => Z | arraydef_0__n => Z | arraydef_0__input => Z | arraydef_0__printBuffer => Z end; arrays := fun name => match name with | arraydef_0__dp => repeat (0%Z) 0 | arraydef_0__weights => repeat (0%Z) 0 | arraydef_0__values => repeat (0%Z) 0 | arraydef_0__message => repeat (0%Z) 1 | arraydef_0__n => repeat (0%Z) 1 | arraydef_0__input => repeat (0%Z) 1 | arraydef_0__printBuffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable2 : EqDecision arrayIndex2 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable2 name : EqDecision (arrayType _ environment2 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__getweight :=
| vardef_0__getweight_index.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__getweight : EqDecision varsfuncdef_0__getweight := ltac:(solve_decision).
Definition funcdef_0__getweight_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getweight) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getweight (vardef_0__getweight_index)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getweight (arraydef_0__weights) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getweight (arraydef_0__message) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__getweight (bools : varsfuncdef_0__getweight -> bool) (numbers : varsfuncdef_0__getweight -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__getweight_body.
Inductive varsfuncdef_0__getvalue :=
| vardef_0__getvalue_index.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__getvalue : EqDecision varsfuncdef_0__getvalue := ltac:(solve_decision).
Definition funcdef_0__getvalue_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getvalue) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getvalue (vardef_0__getvalue_index)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getvalue (arraydef_0__values) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__getvalue (arraydef_0__message) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__getvalue (bools : varsfuncdef_0__getvalue -> bool) (numbers : varsfuncdef_0__getvalue -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__getvalue_body.
Inductive varsfuncdef_0__cell :=
| vardef_0__cell_row
| vardef_0__cell_cap
| vardef_0__cell_limit
| vardef_0__cell_weight
| vardef_0__cell_value
| vardef_0__cell_best
| vardef_0__cell_withItem.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__cell : EqDecision varsfuncdef_0__cell := ltac:(solve_decision).
Definition funcdef_0__cell_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell) withLocalVariablesReturnValue unit := (((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_row)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (arraydef_0__weights) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_weight) x) >>=
fun _ => ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_row)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (arraydef_0__values) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_value) x) >>=
fun _ => (((addInt 64 (multInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_row)) (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_limit)) (Done _ _ _ 1%Z))) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_cap))) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (arraydef_0__dp) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_best) x) >>=
fun _ => ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_cap)) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_weight)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
  ((addInt 64 ((addInt 64 (multInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_row)) (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_limit)) (Done _ _ _ 1%Z))) (subInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_cap)) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_weight)))) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (arraydef_0__dp) x) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_value))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_withItem) x) >>=
  fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_best)) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_withItem)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_withItem)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_best) x) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((addInt 64 (multInt 64 (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_row)) (Done _ _ _ 1%Z)) (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_limit)) (Done _ _ _ 1%Z))) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_cap))) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (vardef_0__cell_best)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__cell (arraydef_0__dp) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__cell (bools : varsfuncdef_0__cell -> bool) (numbers : varsfuncdef_0__cell -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__cell_body.
Inductive varsfuncdef_0__solve :=
| vardef_0__solve_limit.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__solve : EqDecision varsfuncdef_0__solve := ltac:(solve_decision).
Definition funcdef_0__solve_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__solve) withLocalVariablesReturnValue unit := ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__solve (arraydef_0__n) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__solve (vardef_0__solve_limit)) (Done _ _ _ 1%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun preset0 => binder_1 >>= fun preset1 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__solve (vardef_0__solve_limit)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__cell_row) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__cell_cap) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__cell_limit) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__cell y x))) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__solve (bools : varsfuncdef_0__solve -> bool) (numbers : varsfuncdef_0__solve -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__solve_body.
Inductive varsfuncdef_0__main :=
| vardef_0__main_count
| vardef_0__main_limit.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count) x) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__n) x y) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_limit) x) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count)) >>= fun size => grow arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__weights) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count)) >>= fun size => grow arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__values) size (0%Z)) >>=
fun _ => ((multInt 64 (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count)) (Done _ _ _ 1%Z)) (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_limit)) (Done _ _ _ 1%Z))) >>= fun size => grow arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__dp) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop (binder_0 >>= fun x => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__weights) x y)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop (binder_0 >>= fun x => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__values) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_limit)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_limit) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__solve y x)) >>=
fun _ => (((addInt 64 (multInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_count)) (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_limit)) (Done _ _ _ 1%Z))) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_limit))) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__dp) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main x) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__main_body.
