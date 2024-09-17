From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers list strings.
Require Import Coq.Strings.Ascii.
Open Scope type_scope.
Inductive arrayIndex0 :=
| arraydef_0_ReadUnsignedInt64_resultArray.

Definition environment0 : Environment arrayIndex0 := {| arrayType := fun name => match name with | arraydef_0_ReadUnsignedInt64_resultArray => Z end; arrays := fun name => match name with | arraydef_0_ReadUnsignedInt64_resultArray => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable0 : EqDecision arrayIndex0 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable0 name : EqDecision (arrayType _ environment0 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0_ReadUnsignedInt64_ :=
| vardef_0_ReadUnsignedInt64__tmpChar
| vardef_0_ReadUnsignedInt64__result.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_ReadUnsignedInt64_ : EqDecision varsfuncdef_0_ReadUnsignedInt64_ := ltac:(solve_decision).
Definition funcdef_0_ReadUnsignedInt64_ (bools : varsfuncdef_0_ReadUnsignedInt64_ -> bool) (numbers : varsfuncdef_0_ReadUnsignedInt64_ -> Z) (addresses : varsfuncdef_0_ReadUnsignedInt64_ -> list Z): Action (WithArrays _ (arrayType _ environment0)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 48%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 58%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)))) >>= fun x => if x then (
    (continue arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result)) (Done _ _ _ 10%Z)) (subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) (Done _ _ _ 48%Z))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result) x)) >>=
  fun _ => (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 48%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) (((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) >>= fun a => (Done _ _ _ 58%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)))) >>= fun x => if x then (
    (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result)) (Done _ _ _ 10%Z)) (subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__tmpChar)) (Done _ _ _ 48%Z))) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (vardef_0_ReadUnsignedInt64__result)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0_ReadUnsignedInt64_ (arraydef_0_ReadUnsignedInt64_resultArray) x y) >>=
fun _ => Done _ _ _ tt).
Inductive arrayIndex1 :=
| arraydef_0_PrintInt64_buffer.

Definition environment1 : Environment arrayIndex1 := {| arrayType := fun name => match name with | arraydef_0_PrintInt64_buffer => Z end; arrays := fun name => match name with | arraydef_0_PrintInt64_buffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable1 : EqDecision arrayIndex1 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable1 name : EqDecision (arrayType _ environment1 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0_PrintInt64_unsigned :=
| vardef_0_PrintInt64_unsigned_num
| vardef_0_PrintInt64_unsigned_i
| vardef_0_PrintInt64_unsigned_tmpChar.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_PrintInt64_unsigned : EqDecision varsfuncdef_0_PrintInt64_unsigned := ltac:(solve_decision).
Definition funcdef_0_PrintInt64_unsigned (bools : varsfuncdef_0_PrintInt64_unsigned -> bool) (numbers : varsfuncdef_0_PrintInt64_unsigned -> Z) (addresses : varsfuncdef_0_PrintInt64_unsigned -> list Z): Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  (((Done _ _ _ 48%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned x) >>=
  fun _ => Done _ _ _ tt
) else (
  ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i) x) >>=
  fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop (((addInt 64 (modIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) (Done _ _ _ 10%Z)) (Done _ _ _ 48%Z)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_tmpChar) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_tmpChar)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (arraydef_0_PrintInt64_buffer) x y)) >>=
    fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) (Done _ _ _ 10%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num) x)) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned (arraydef_0_PrintInt64_buffer) x) >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0_PrintInt64_signed :=
| vardef_0_PrintInt64_signed_num.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_PrintInt64_signed : EqDecision varsfuncdef_0_PrintInt64_signed := ltac:(solve_decision).
Definition funcdef_0_PrintInt64_signed (bools : varsfuncdef_0_PrintInt64_signed -> bool) (numbers : varsfuncdef_0_PrintInt64_signed -> Z) (addresses : varsfuncdef_0_PrintInt64_signed -> list Z): Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun a => (Done _ _ _ 0%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64)))) >>= fun x => if x then (
  (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun x => Done _ _ _ (coerceInt (-x) 64)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num) x) >>=
  fun _ => (((Done _ _ _ 45%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_signed x) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_signed (vardef_0_PrintInt64_signed_num)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0_PrintInt64_unsigned y x z)) >>=
fun _ => Done _ _ _ tt).
Inductive arrayIndex2 :=
| arraydef_0__fenwick
| arraydef_0__resultArray
| arraydef_0__tempArray
| arraydef_0__idxArray
| arraydef_0__valueArray
| arraydef_0__sumArray
| arraydef_0__printBuffer
| arraydef_0__n
| arraydef_0__q.

Definition environment2 : Environment arrayIndex2 := {| arrayType := fun name => match name with | arraydef_0__fenwick => Z | arraydef_0__resultArray => Z | arraydef_0__tempArray => Z | arraydef_0__idxArray => Z | arraydef_0__valueArray => Z | arraydef_0__sumArray => Z | arraydef_0__printBuffer => Z | arraydef_0__n => Z | arraydef_0__q => Z end; arrays := fun name => match name with | arraydef_0__fenwick => repeat (0%Z) 200001 | arraydef_0__resultArray => repeat (0%Z) 1 | arraydef_0__tempArray => repeat (0%Z) 1 | arraydef_0__idxArray => repeat (0%Z) 1 | arraydef_0__valueArray => repeat (0%Z) 1 | arraydef_0__sumArray => repeat (0%Z) 1 | arraydef_0__printBuffer => repeat (0%Z) 20 | arraydef_0__n => repeat (0%Z) 1 | arraydef_0__q => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable2 : EqDecision arrayIndex2 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable2 name : EqDecision (arrayType _ environment2 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__increase :=
| vardef_0__increase_idx
| vardef_0__increase_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__increase : EqDecision varsfuncdef_0__increase := ltac:(solve_decision).
Definition funcdef_0__increase (bools : varsfuncdef_0__increase -> bool) (numbers : varsfuncdef_0__increase -> Z) (addresses : varsfuncdef_0__increase -> list Z): Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((Done _ _ _ 0%Z) >>= fun x => ((addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (vardef_0__increase_idx)) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (vardef_0__increase_value)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__valueArray) x y) >>=
fun _ => ((Done _ _ _ 30%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__n) x) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x) >>= fun x => ((addInt 64 (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__fenwick) x) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__valueArray) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__fenwick) x y)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x) (andBits ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x) (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x) >>= fun x => Done _ _ _ (coerceInt (-x) 64)))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__increase (arraydef_0__idxArray) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__query :=
| vardef_0__query_idx.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__query : EqDecision varsfuncdef_0__query := ltac:(solve_decision).
Definition funcdef_0__query (bools : varsfuncdef_0__query -> bool) (numbers : varsfuncdef_0__query -> Z) (addresses : varsfuncdef_0__query -> list Z): Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__sumArray) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (vardef_0__query_idx)) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x y) >>=
fun _ => ((Done _ _ _ 30%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x) >>= fun a => (Done _ _ _ 1%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__sumArray) x) (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__fenwick) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__sumArray) x y)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((subInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x) (andBits ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x) (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x) >>= fun x => Done _ _ _ (coerceInt (-x) 64)))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__idxArray) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__sumArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__resultArray) x y) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__rangeQuery :=
| vardef_0__rangeQuery_left
| vardef_0__rangeQuery_right.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__rangeQuery : EqDecision varsfuncdef_0__rangeQuery := ltac:(solve_decision).
Definition funcdef_0__rangeQuery (bools : varsfuncdef_0__rangeQuery -> bool) (numbers : varsfuncdef_0__rangeQuery -> Z) (addresses : varsfuncdef_0__rangeQuery -> list Z): Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (vardef_0__rangeQuery_right)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__query_idx) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__query y x z)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__tempArray) x y) >>=
fun _ => ((subInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (vardef_0__rangeQuery_left)) (Done _ _ _ 1%Z)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__query_idx) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__query y x z)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((subInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__tempArray) x) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__resultArray) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__tempArray) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__tempArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__rangeQuery (arraydef_0__resultArray) x y) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__update :=
| vardef_0__update_idx
| vardef_0__update_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__update : EqDecision varsfuncdef_0__update := ltac:(solve_decision).
Definition funcdef_0__update (bools : varsfuncdef_0__update -> bool) (numbers : varsfuncdef_0__update -> Z) (addresses : varsfuncdef_0__update -> list Z): Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (vardef_0__update_idx)) >>= fun preset0 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (vardef_0__update_idx)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rangeQuery_left) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rangeQuery_right) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__rangeQuery y x z)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (arraydef_0__tempArray) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((subInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (vardef_0__update_value)) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (arraydef_0__tempArray) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (arraydef_0__tempArray) x y) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (vardef_0__update_idx)) >>= fun preset0 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__update (arraydef_0__tempArray) x) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__increase_idx) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__increase_value) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__increase y x z)) >>=
fun _ => Done _ _ _ tt).
Inductive varsfuncdef_0__main : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) (addresses : varsfuncdef_0__main -> list Z): Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers addresses (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__n) x y) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__q) x y) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__n) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop (binder_0 >>= fun preset0 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__increase_idx) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__increase_value) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__increase y x z))) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__q) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__tempArray) x y)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__idxArray) x y)) >>=
  fun _ => ((liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__tempArray) x) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity))))) >>=
    fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__valueArray) x y)) >>=
    fun _ => (liftToWithinLoop ((subInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__idxArray) x) (Done _ _ _ 1%Z)) >>= fun preset0 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__valueArray) x) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__update_idx) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__update_value) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__update y x z))) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__resultArray end) (fun name => ltac:(destruct name; reflexivity))))) >>=
    fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__tempArray) x y)) >>=
    fun _ => (liftToWithinLoop ((subInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__idxArray) x) (Done _ _ _ 1%Z)) >>= fun preset0 => (subInt 64 ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__tempArray) x) (Done _ _ _ 1%Z)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rangeQuery_left) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rangeQuery_right) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (funcdef_0__rangeQuery y x z))) >>=
    fun _ => (liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__resultArray) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => (Done _ _ _ (fun x => repeat 0%Z 20)) >>= fun z => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x z) (arrayType _ environment2) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity))))) >>=
    fun _ => (liftToWithinLoop (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
