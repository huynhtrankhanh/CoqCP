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
| arraydef_0__input
| arraydef_0__reply
| arraydef_0__printBuffer.

Definition environment2 : Environment arrayIndex2 := {| arrayType := fun name => match name with | arraydef_0__input => Z | arraydef_0__reply => Z | arraydef_0__printBuffer => Z end; arrays := fun name => match name with | arraydef_0__input => repeat (0%Z) 1 | arraydef_0__reply => repeat (0%Z) 1 | arraydef_0__printBuffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable2 : EqDecision arrayIndex2 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable2 name : EqDecision (arrayType _ environment2 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__query :=
| vardef_0__query_country
| vardef_0__query_index
| vardef_0__query_n.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__query : EqDecision varsfuncdef_0__query := ltac:(solve_decision).
Definition funcdef_0__query_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query) withLocalVariablesReturnValue unit := ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (vardef_0__query_index)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 1000000001%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__reply) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (vardef_0__query_index)) >>= fun x => (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (vardef_0__query_n)) (Done _ _ _ 1%Z)) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__reply) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (vardef_0__query_country)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query x) >>=
    fun _ => (((Done _ _ _ 32%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query x) >>=
    fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (vardef_0__query_index)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
    fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query x) >>=
    fun _ => (flush arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query) >>=
    fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
    fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__input) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0__query (arraydef_0__reply) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__query (bools : varsfuncdef_0__query -> bool) (numbers : varsfuncdef_0__query -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__query_body.
Inductive varsfuncdef_0__main :=
| vardef_0__main_n
| vardef_0__main_k
| vardef_0__main_lo
| vardef_0__main_hi
| vardef_0__main_mid
| vardef_0__main_j
| vardef_0__main_f
| vardef_0__main_s
| vardef_0__main_answer.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n) x) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_k) x) >>=
fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_k)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((subInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_k)) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_lo) x) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_k)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_hi) x) >>=
fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_hi)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_hi) x) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((Done _ _ _ 17%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_lo)) >>= fun x => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_hi)) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_lo)) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_hi))) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_mid) x)) >>=
  fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_k)) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_mid))) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_j) x)) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 70%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun preset0 => (addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_mid)) (Done _ _ _ 1%Z)) >>= fun preset1 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__query_country) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__query_index) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__query_n) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__query y x))) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__reply) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_f) x)) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 83%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun preset0 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_j)) >>= fun preset1 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__query_country) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__query_index) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__query_n) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__query y x))) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__reply) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_s) x)) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_f)) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_s)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_mid)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_hi) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_mid)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_lo) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (((Done _ _ _ 70%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun preset0 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_lo)) >>= fun preset1 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__query_country) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__query_index) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__query_n) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__query y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__reply) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_f) x) >>=
fun _ => (((Done _ _ _ 83%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun preset0 => (subInt 64 (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_k)) (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_lo))) >>= fun preset1 => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_n)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__query_country) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__query_index) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__query_n) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__query y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (arraydef_0__reply) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_s) x) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_f)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_answer) x) >>=
fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_s)) >>= fun a => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_answer)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_s)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_answer) x) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (loopString ("! ") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main (vardef_0__main_answer)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment2) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main x) >>=
fun _ => (flush arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__main_body.
