From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Coq.Strings.Ascii.
Open Scope type_scope.
Inductive arrayIndex0 :=
| arraydef_0__heap
| arraydef_0__heapSize.

Definition environment0 : Environment arrayIndex0 := {| arrayType := fun name => match name with | arraydef_0__heap => Z | arraydef_0__heapSize => Z end; arrays := fun name => match name with | arraydef_0__heap => repeat (0%Z) 100000 | arraydef_0__heapSize => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable0 : EqDecision arrayIndex0 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable0 name : EqDecision (arrayType _ environment0 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__siftUp :=
| vardef_0__siftUp_index
| vardef_0__siftUp_currentIndex
| vardef_0__siftUp_parentIndex
| vardef_0__siftUp_temp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__siftUp : EqDecision varsfuncdef_0__siftUp := ltac:(solve_decision).
Definition funcdef_0__siftUp (bools : varsfuncdef_0__siftUp -> bool) (numbers : varsfuncdef_0__siftUp -> Z) (addresses : varsfuncdef_0__siftUp -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_index)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex) x) >>=
fun _ => ((Done _ _ _ 30%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (subInt 32 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex) x)) >>=
  fun _ => ((liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun a => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_temp) x)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (arraydef_0__heap) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_parentIndex)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp (vardef_0__siftUp_currentIndex) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftUp) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__siftDown :=
| vardef_0__siftDown_index
| vardef_0__siftDown_currentIndex
| vardef_0__siftDown_leftChild
| vardef_0__siftDown_rightChild
| vardef_0__siftDown_smallestIndex
| vardef_0__siftDown_temp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__siftDown : EqDecision varsfuncdef_0__siftDown := ltac:(solve_decision).
Definition funcdef_0__siftDown (bools : varsfuncdef_0__siftDown -> bool) (numbers : varsfuncdef_0__siftDown -> Z) (addresses : varsfuncdef_0__siftDown -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_index)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex) x) >>=
fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heapSize) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((Done _ _ _ 30%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((addInt 32 (multInt 32 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild) x)) >>=
    fun _ => (liftToWithinLoop ((addInt 32 (multInt 32 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 2%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex) x)) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild)) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heapSize) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      ((liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun a => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_leftChild)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild)) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heapSize) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      ((liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun a => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_rightChild)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_temp) x)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (arraydef_0__heap) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_smallestIndex)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__siftDown (vardef_0__siftDown_currentIndex) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__insert :=
| vardef_0__insert_value
| vardef_0__insert_index.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__insert : EqDecision varsfuncdef_0__insert := ltac:(solve_decision).
Definition funcdef_0__insert (bools : varsfuncdef_0__insert -> bool) (numbers : varsfuncdef_0__insert -> Z) (addresses : varsfuncdef_0__insert -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (arraydef_0__heapSize) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (vardef_0__insert_value)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (arraydef_0__heap) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((addInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (arraydef_0__heapSize) x y) >>=
fun _ => ((subInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (vardef_0__insert_index) x) >>=
fun _ => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__insert (vardef_0__insert_index)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__siftUp_index) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__siftUp y x z)) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__pop :=
| vardef_0__pop_index
| vardef_0__pop_temp.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__pop : EqDecision varsfuncdef_0__pop := ltac:(solve_decision).
Definition funcdef_0__pop (bools : varsfuncdef_0__pop -> bool) (numbers : varsfuncdef_0__pop -> Z) (addresses : varsfuncdef_0__pop -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heapSize) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((subInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (vardef_0__pop_index) x) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heap) x) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (vardef_0__pop_temp) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (vardef_0__pop_index)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heap) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heap) x y) >>=
  fun _ => (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (vardef_0__pop_index)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (vardef_0__pop_temp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heap) x y) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((subInt 32 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heapSize) x) ((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0__pop (arraydef_0__heapSize) x y) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__siftDown_index) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__siftDown y x z)) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__main :=
| vardef_0__main_current
| vardef_0__main_sum.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) (addresses : varsfuncdef_0__main -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((divIntUnsigned (getCommunicationSize _ _ _) (Done _ _ _ 4%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 32 (addInt 32 (addInt 32 (multInt 32 (((multInt 64 binder_0 (Done _ _ _ 4%Z)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 32)) ((Done _ _ _ 16777216%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) (multInt 32 (((addInt 64 (multInt 64 binder_0 (Done _ _ _ 4%Z)) (Done _ _ _ 1%Z)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 32)) ((Done _ _ _ 65536%Z) >>= fun x => Done _ _ _ (coerceInt x 32)))) (multInt 32 (((addInt 64 (multInt 64 binder_0 (Done _ _ _ 4%Z)) (Done _ _ _ 2%Z)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 32)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 32)))) (((addInt 64 (multInt 64 binder_0 (Done _ _ _ 4%Z)) (Done _ _ _ 3%Z)) >>= fun x => readByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current) x)) >>=
  fun _ => ((liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__heapSize) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 32)) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
    ((liftToWithinLoop (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__heap) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
      (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_sum)) ((subInt 32 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (arraydef_0__heap) x)) >>= fun x => Done _ _ _ (coerceInt x 64))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_sum) x)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__pop y x z))) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__insert_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__insert y x z))) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__insert_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__insert y x z))) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) ((Done _ _ _ 16777216%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) ((Done _ _ _ 65536%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
fun _ => ((Done _ _ _ 2%Z) >>= fun x => ((modIntUnsigned (divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
fun _ => ((Done _ _ _ 3%Z) >>= fun x => ((modIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main (vardef_0__main_current)) ((Done _ _ _ 256%Z) >>= fun x => Done _ _ _ (coerceInt x 32))) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => setByte arrayIndex0 (arrayType _ environment0) varsfuncdef_0__main x y) >>=
fun _ => Done _ _ _ tt).
