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
| arraydef_0__input
| arraydef_0__printBuffer
| arraydef_0__heap
| arraydef_0__heapSize.

Definition environment2 : Environment arrayIndex2 := {| arrayType := fun name => match name with | arraydef_0__input => Z | arraydef_0__printBuffer => Z | arraydef_0__heap => Z | arraydef_0__heapSize => Z end; arrays := fun name => match name with | arraydef_0__input => repeat (0%Z) 1 | arraydef_0__printBuffer => repeat (0%Z) 20 | arraydef_0__heap => repeat (0%Z) 1 | arraydef_0__heapSize => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable2 : EqDecision arrayIndex2 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable2 name : EqDecision (arrayType _ environment2 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__siftUp :=
| vardef_0__siftUp_index
| vardef_0__siftUp_currentIndex
| vardef_0__siftUp_parentIndex
| vardef_0__siftUp_temp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__siftUp : EqDecision varsfuncdef_0__siftUp := ltac:(solve_decision).
Definition funcdef_0__siftUp_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp) withLocalVariablesReturnValue unit := (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_index)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex) x) >>=
fun _ => ((Done _ _ _ 30%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (subInt 32 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex) x)) >>=
  fun _ => ((liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun a => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_temp) x)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftUp) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__siftUp (bools : varsfuncdef_0__siftUp -> bool) (numbers : varsfuncdef_0__siftUp -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__siftUp_body.
Inductive varsfuncdef_0__siftDown :=
| vardef_0__siftDown_index
| vardef_0__siftDown_currentIndex
| vardef_0__siftDown_leftChild
| vardef_0__siftDown_rightChild
| vardef_0__siftDown_smallestIndex
| vardef_0__siftDown_temp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__siftDown : EqDecision varsfuncdef_0__siftDown := ltac:(solve_decision).
Definition funcdef_0__siftDown_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown) withLocalVariablesReturnValue unit := (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_index)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex) x) >>=
fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heapSize) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((Done _ _ _ 30%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((addInt 32 (multInt 32 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild) x)) >>=
    fun _ => (liftToWithinLoop ((addInt 32 (multInt 32 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex) x)) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild)) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heapSize) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      ((liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun a => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild)) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heapSize) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      ((liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun a => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_temp) x)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__siftDown (bools : varsfuncdef_0__siftDown -> bool) (numbers : varsfuncdef_0__siftDown -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__siftDown_body.
Inductive varsfuncdef_0__insert :=
| vardef_0__insert_value
| vardef_0__insert_index.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__insert : EqDecision varsfuncdef_0__insert := ltac:(solve_decision).
Definition funcdef_0__insert_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert) withLocalVariablesReturnValue unit := (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (arraydef_0__heapSize) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (vardef_0__insert_value)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (arraydef_0__heap) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((addInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (arraydef_0__heapSize) x y) >>=
fun _ => ((subInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (vardef_0__insert_index) x) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__insert (vardef_0__insert_index)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__siftUp_index) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__siftUp y x)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__insert (bools : varsfuncdef_0__insert -> bool) (numbers : varsfuncdef_0__insert -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__insert_body.
Inductive varsfuncdef_0__pop :=
| vardef_0__pop_index
| vardef_0__pop_temp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__pop : EqDecision varsfuncdef_0__pop := ltac:(solve_decision).
Definition funcdef_0__pop_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop) withLocalVariablesReturnValue unit := (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heapSize) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((subInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (vardef_0__pop_index) x) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heap) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (vardef_0__pop_temp) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (vardef_0__pop_index)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heap) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heap) x y) >>=
  fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (vardef_0__pop_index)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (vardef_0__pop_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heap) x y) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((subInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__pop (arraydef_0__heapSize) x y) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__siftDown_index) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__siftDown y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__pop (bools : varsfuncdef_0__pop -> bool) (numbers : varsfuncdef_0__pop -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__pop_body.
Inductive varsfuncdef_0__main :=
| vardef_0__main_current
| vardef_0__main_sum
| vardef_0__main_n.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n) x) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__heap) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_current) x)) >>=
  fun _ => ((liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__heapSize) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
    ((liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__heap) x) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_current)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_sum)) ((subInt 32 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_current)) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__heap) x)) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_sum) x)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__pop y x))) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_current)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__insert_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__insert y x))) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_current)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__insert_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__insert y x))) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_sum)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main x) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__main_body.
