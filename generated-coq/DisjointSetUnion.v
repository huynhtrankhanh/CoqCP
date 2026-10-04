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
| arraydef_0_DSU_dsu
| arraydef_0_DSU_hasBeenInitialized
| arraydef_0_DSU_result.

Definition environment2 : Environment arrayIndex2 := {| arrayType := fun name => match name with | arraydef_0_DSU_dsu => Z | arraydef_0_DSU_hasBeenInitialized => Z | arraydef_0_DSU_result => Z end; arrays := fun name => match name with | arraydef_0_DSU_dsu => repeat (0%Z) 100 | arraydef_0_DSU_hasBeenInitialized => repeat (0%Z) 1 | arraydef_0_DSU_result => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable2 : EqDecision arrayIndex2 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable2 name : EqDecision (arrayType _ environment2 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0_DSU_ancestor :=
| vardef_0_DSU_ancestor_vertex
| vardef_0_DSU_ancestor_work.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_DSU_ancestor : EqDecision varsfuncdef_0_DSU_ancestor := ltac:(solve_decision).
Definition funcdef_0_DSU_ancestor_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor) withLocalVariablesReturnValue unit := (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_vertex)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work) x) >>=
fun _ => ((Done _ _ _ 100%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_dsu) x) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 8) (toSigned b 8))))) >>= fun x => if x then (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_dsu) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_result) x y) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_vertex)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work) x) >>=
fun _ => ((Done _ _ _ 100%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_dsu) x) >>= fun a => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 8) (toSigned b 8))))) >>= fun x => if x then (
    (break arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_dsu) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_vertex) x)) >>=
  fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_result) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (arraydef_0_DSU_dsu) x y)) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_vertex)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_ancestor (vardef_0_DSU_ancestor_work) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0_DSU_ancestor (bools : varsfuncdef_0_DSU_ancestor -> bool) (numbers : varsfuncdef_0_DSU_ancestor -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0_DSU_ancestor_body.
Inductive varsfuncdef_0_DSU_unite :=
| vardef_0_DSU_unite_u
| vardef_0_DSU_unite_v
| vardef_0_DSU_unite_z.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_DSU_unite : EqDecision varsfuncdef_0_DSU_unite := ltac:(solve_decision).
Definition funcdef_0_DSU_unite_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite) withLocalVariablesReturnValue unit := (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_DSU_ancestor_vertex) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0_DSU_ancestor y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_result) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u) x) >>=
fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_DSU_ancestor_vertex) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0_DSU_ancestor y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_result) x) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v) x) >>=
fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u)) >>= fun x => (numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  (((((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_dsu) x) >>= fun a => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_dsu) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 8) (toSigned b 8)))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_z) x) >>=
    fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u) x) >>=
    fun _ => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_z)) >>= fun x => numberLocalSet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v) x) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((addInt 8 (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_dsu) x) (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_dsu) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_dsu) x y) >>=
  fun _ => (((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_u)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => ((numberLocalGet arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (vardef_0_DSU_unite_v)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_unite (arraydef_0_DSU_dsu) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0_DSU_unite (bools : varsfuncdef_0_DSU_unite -> bool) (numbers : varsfuncdef_0_DSU_unite -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0_DSU_unite_body.
Inductive varsfuncdef_0_DSU_initialize : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0_DSU_initialize : EqDecision varsfuncdef_0_DSU_initialize := ltac:(solve_decision).
Definition funcdef_0_DSU_initialize_body : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_initialize) withLocalVariablesReturnValue unit := (((Done _ _ _ 100%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_initialize) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt (-x) 64)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex2 (arrayType _ environment2) varsfuncdef_0_DSU_initialize (arraydef_0_DSU_dsu) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0_DSU_initialize (bools : varsfuncdef_0_DSU_initialize -> bool) (numbers : varsfuncdef_0_DSU_initialize -> Z) : Action (WithArrays _ (arrayType _ environment2)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0_DSU_initialize_body.
Inductive arrayIndex3 :=
| arraydef_0__input
| arraydef_0__printBuffer
| arraydef_0__dsu
| arraydef_0__hasBeenInitialized
| arraydef_0__result.

Definition environment3 : Environment arrayIndex3 := {| arrayType := fun name => match name with | arraydef_0__input => Z | arraydef_0__printBuffer => Z | arraydef_0__dsu => Z | arraydef_0__hasBeenInitialized => Z | arraydef_0__result => Z end; arrays := fun name => match name with | arraydef_0__input => repeat (0%Z) 1 | arraydef_0__printBuffer => repeat (0%Z) 20 | arraydef_0__dsu => repeat (0%Z) 100 | arraydef_0__hasBeenInitialized => repeat (0%Z) 1 | arraydef_0__result => repeat (0%Z) 1 end |}.

#[export] Instance arrayIndexEqualityDecidable3 : EqDecision arrayIndex3 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable3 name : EqDecision (arrayType _ environment3 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__main :=
| vardef_0__main_q
| vardef_0__main_u
| vardef_0__main_v.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main_body : Action (WithLocalVariables arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_DSU_initialize y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_DSU_dsu => arraydef_0__dsu | arraydef_0_DSU_hasBeenInitialized => arraydef_0__hasBeenInitialized | arraydef_0_DSU_result => arraydef_0__result end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => numberLocalSet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_q) x) >>=
fun _ => ((numberLocalGet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_q)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => numberLocalSet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_u) x)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_ReadUnsignedInt64_ y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (arraydef_0__input) x) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => numberLocalSet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_v) x)) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_u)) >>= fun preset0 => (numberLocalGet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_v)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_DSU_unite_u) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0_DSU_unite_v) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_DSU_unite y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_DSU_dsu => arraydef_0__dsu | arraydef_0_DSU_hasBeenInitialized => arraydef_0__hasBeenInitialized | arraydef_0_DSU_result => arraydef_0__result end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (vardef_0__main_u)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_DSU_ancestor_vertex) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_DSU_ancestor y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_DSU_dsu => arraydef_0__dsu | arraydef_0_DSU_hasBeenInitialized => arraydef_0__hasBeenInitialized | arraydef_0_DSU_result => arraydef_0__result end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop ((((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (arraydef_0__result) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => retrieve arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main (arraydef_0__dsu) x) >>= fun x => Done _ _ _ (coerceInt (-x) 8)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment3) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity))))) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex3 (arrayType _ environment3) varsfuncdef_0__main x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) : Action (WithArrays _ (arrayType _ environment3)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__main_body.
