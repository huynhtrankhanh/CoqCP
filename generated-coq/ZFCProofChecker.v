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
| arraydef_0__meta
| arraydef_0__sipState
| arraydef_0__formulaBuckets
| arraydef_0__formulaLinks
| arraydef_0__formulas
| arraydef_0__classes
| arraydef_0__theorems
| arraydef_0__frames
| arraydef_0__renameMemo
| arraydef_0__renameMemoScratch
| arraydef_0__bindings
| arraydef_0__schemaNodes
| arraydef_0__schemaValues
| arraydef_0__schemaMarks
| arraydef_0__schemaArguments
| arraydef_0__names
| arraydef_0__token
| arraydef_0__printBuffer.

Definition environment1 : Environment arrayIndex1 := {| arrayType := fun name => match name with | arraydef_0__meta => Z | arraydef_0__sipState => Z * Z * Z * Z | arraydef_0__formulaBuckets => Z | arraydef_0__formulaLinks => Z | arraydef_0__formulas => Z * Z * Z | arraydef_0__classes => Z * Z | arraydef_0__theorems => Z | arraydef_0__frames => Z * Z * Z * Z | arraydef_0__renameMemo => Z * Z * Z * Z | arraydef_0__renameMemoScratch => Z * Z * Z * Z | arraydef_0__bindings => Z * Z * Z * Z * Z | arraydef_0__schemaNodes => Z * Z * Z * Z * Z * Z * Z | arraydef_0__schemaValues => Z | arraydef_0__schemaMarks => Z | arraydef_0__schemaArguments => Z | arraydef_0__names => Z | arraydef_0__token => Z | arraydef_0__printBuffer => Z end; arrays := fun name => match name with | arraydef_0__meta => repeat (0%Z) 32 | arraydef_0__sipState => repeat (0%Z, 0%Z, 0%Z, 0%Z) 1 | arraydef_0__formulaBuckets => repeat (0%Z) 1024 | arraydef_0__formulaLinks => repeat (0%Z) 0 | arraydef_0__formulas => repeat (0%Z, 0%Z, 0%Z) 0 | arraydef_0__classes => repeat (0%Z, 0%Z) 0 | arraydef_0__theorems => repeat (0%Z) 0 | arraydef_0__frames => repeat (0%Z, 0%Z, 0%Z, 0%Z) 0 | arraydef_0__renameMemo => repeat (0%Z, 0%Z, 0%Z, 0%Z) 0 | arraydef_0__renameMemoScratch => repeat (0%Z, 0%Z, 0%Z, 0%Z) 0 | arraydef_0__bindings => repeat (0%Z, 0%Z, 0%Z, 0%Z, 0%Z) 0 | arraydef_0__schemaNodes => repeat (0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z) 0 | arraydef_0__schemaValues => repeat (0%Z) 0 | arraydef_0__schemaMarks => repeat (0%Z) 0 | arraydef_0__schemaArguments => repeat (0%Z) 0 | arraydef_0__names => repeat (0%Z) 0 | arraydef_0__token => repeat (0%Z) 1024 | arraydef_0__printBuffer => repeat (0%Z) 20 end |}.

#[export] Instance arrayIndexEqualityDecidable1 : EqDecision arrayIndex1 := ltac:(solve_decision).
#[export] Instance arrayTypeEqualityDecidable1 name : EqDecision (arrayType _ environment1 name).
Proof. simpl. repeat destruct name. all: solve_decision. Defined.
Inductive varsfuncdef_0__sipRound :=
| vardef_0__sipRound_v0
| vardef_0__sipRound_v1
| vardef_0__sipRound_v2
| vardef_0__sipRound_v3.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__sipRound : EqDecision varsfuncdef_0__sipRound := ltac:(solve_decision).
Definition funcdef_0__sipRound_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound) withLocalVariablesReturnValue unit := (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0) x) >>=
fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1) x) >>=
fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2) x) >>=
fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3) x) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0) x) >>=
fun _ => ((xorBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1)) (Done _ _ _ 13%Z)) (shiftRight 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1)) (Done _ _ _ 51%Z))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1) x) >>=
fun _ => ((orBits (shiftLeft 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0)) (Done _ _ _ 32%Z)) (shiftRight 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0)) (Done _ _ _ 32%Z))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0) x) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2) x) >>=
fun _ => ((xorBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3)) (Done _ _ _ 16%Z)) (shiftRight 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3)) (Done _ _ _ 48%Z))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3) x) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0) x) >>=
fun _ => ((xorBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3)) (Done _ _ _ 21%Z)) (shiftRight 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3)) (Done _ _ _ 43%Z))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3) x) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2) x) >>=
fun _ => ((xorBits (orBits (shiftLeft 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1)) (Done _ _ _ 17%Z)) (shiftRight 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1)) (Done _ _ _ 47%Z))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1) x) >>=
fun _ => ((orBits (shiftLeft 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2)) (Done _ _ _ 32%Z)) (shiftRight 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2)) (Done _ _ _ 32%Z))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2) x) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v0)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v1)) >>= fun tuple_element_1 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v2)) >>= fun tuple_element_2 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (vardef_0__sipRound_v3)) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipRound (arraydef_0__sipState) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__sipRound (bools : varsfuncdef_0__sipRound -> bool) (numbers : varsfuncdef_0__sipRound -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__sipRound_body.
Inductive varsfuncdef_0__sipWord :=
| vardef_0__sipWord_word.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__sipWord : EqDecision varsfuncdef_0__sipWord := ltac:(solve_decision).
Definition funcdef_0__sipWord_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun tuple_element_0 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun tuple_element_1 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun tuple_element_2 => ((xorBits (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (vardef_0__sipWord_word))) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x y) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipRound y x)) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipRound y x)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((xorBits (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (vardef_0__sipWord_word))) >>= fun tuple_element_0 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun tuple_element_1 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun tuple_element_2 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__sipWord (arraydef_0__sipState) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__sipWord (bools : varsfuncdef_0__sipWord -> bool) (numbers : varsfuncdef_0__sipWord -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__sipWord_body.
Inductive varsfuncdef_0__formulaHash :=
| vardef_0__formulaHash_tag
| vardef_0__formulaHash_a
| vardef_0__formulaHash_b
| vardef_0__formulaHash_hash.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__formulaHash : EqDecision varsfuncdef_0__formulaHash := ltac:(solve_decision).
Definition funcdef_0__formulaHash_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((xorBits (Done _ _ _ 8317987319222330741%Z) ((Done _ _ _ 26%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x)) >>= fun tuple_element_0 => ((xorBits (Done _ _ _ 7237128888997146477%Z) ((Done _ _ _ 27%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x)) >>= fun tuple_element_1 => ((xorBits (Done _ _ _ 7816392313619706465%Z) ((Done _ _ _ 26%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x)) >>= fun tuple_element_2 => ((xorBits (Done _ _ _ 8387220255154660723%Z) ((Done _ _ _ 27%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x)) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x y) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (vardef_0__formulaHash_tag)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__sipWord_word) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipWord y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (vardef_0__formulaHash_a)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__sipWord_word) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipWord y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (vardef_0__formulaHash_b)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__sipWord_word) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipWord y x)) >>=
fun _ => ((Done _ _ _ 1729382256910270464%Z) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__sipWord_word) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipWord y x)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun tuple_element_0 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun tuple_element_1 => ((xorBits (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) (Done _ _ _ 255%Z)) >>= fun tuple_element_2 => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x y) >>=
fun _ => ((Done _ _ _ 4%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__sipRound y x))) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((xorBits (xorBits (xorBits (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple)))))))) (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple))))))) (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__sipState) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (vardef_0__formulaHash_hash) x) >>=
fun _ => ((Done _ _ _ 28%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (vardef_0__formulaHash_hash)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 21%Z) >>= fun x => ((modIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (vardef_0__formulaHash_hash)) ((Done _ _ _ 20%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__formulaHash (arraydef_0__meta) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__formulaHash (bools : varsfuncdef_0__formulaHash -> bool) (numbers : varsfuncdef_0__formulaHash -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__formulaHash_body.
Inductive varsfuncdef_0__rehashFormulas :=
| vardef_0__rehashFormulas_size
| vardef_0__rehashFormulas_bucket.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__rehashFormulas : EqDecision varsfuncdef_0__rehashFormulas := ltac:(solve_decision).
Definition funcdef_0__rehashFormulas_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas) withLocalVariablesReturnValue unit := ((((Done _ _ _ 20%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size) x) >>=
fun _ => (((Done _ _ _ 9223372036854775807%Z) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulaBuckets) size (0%Z)) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulaBuckets) x y)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((Done _ _ _ 20%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_size)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__meta) x y) >>=
  fun _ => (((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__meta) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (element_tuple))))) >>= fun preset0 => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun preset1 => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__formulaHash y x))) >>=
    fun _ => (liftToWithinLoop (((Done _ _ _ 21%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_bucket) x)) >>=
    fun _ => (liftToWithinLoop (binder_0 >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_bucket)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulaBuckets) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulaLinks) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (vardef_0__rehashFormulas_bucket)) >>= fun x => ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rehashFormulas (arraydef_0__formulaBuckets) x y)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__rehashFormulas (bools : varsfuncdef_0__rehashFormulas -> bool) (numbers : varsfuncdef_0__rehashFormulas -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__rehashFormulas_body.
Inductive varsfuncdef_0__intern :=
| vardef_0__intern_tag
| vardef_0__intern_a
| vardef_0__intern_b
| vardef_0__intern_found
| vardef_0__intern_current
| vardef_0__intern_bucket.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__intern : EqDecision varsfuncdef_0__intern := ltac:(solve_decision).
Definition funcdef_0__intern_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_found) x) >>=
fun _ => ((((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => ((Done _ _ _ 20%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rehashFormulas y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_tag)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_b)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__formulaHash y x)) >>=
  fun _ => (((Done _ _ _ 21%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_bucket) x) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_bucket)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulaBuckets) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current) x) >>=
  fun _ => (((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current) x)) >>=
    fun _ => ((liftToWithinLoop (shortCircuitAnd (shortCircuitAnd ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (element_tuple))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_tag)) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_a)) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_b)) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
      (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x y)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_found) x)) >>=
      fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulaLinks) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_current) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_found)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x y) >>=
      fun _ => Done _ _ _ tt
    ) else (
      ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x y) >>=
      fun _ => ((addInt 64 ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulas) size (0%Z, 0%Z, 0%Z)) >>=
      fun _ => ((addInt 64 ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulaLinks) size (0%Z)) >>=
      fun _ => (((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_tag)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_a)) >>= fun tuple_element_1 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_b)) >>= fun tuple_element_2 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2)))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulas) x y) >>=
      fun _ => (((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_bucket)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulaBuckets) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulaLinks) x y) >>=
      fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (vardef_0__intern_bucket)) >>= fun x => ((addInt 64 ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__formulaBuckets) x y) >>=
      fun _ => ((Done _ _ _ 1%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern (arraydef_0__meta) x y) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__intern (bools : varsfuncdef_0__intern -> bool) (numbers : varsfuncdef_0__intern -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__intern_body.
Inductive varsfuncdef_0__push :=
| vardef_0__push_node
| vardef_0__push_depth.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__push : EqDecision varsfuncdef_0__push := ltac:(solve_decision).
Definition funcdef_0__push_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push) withLocalVariablesReturnValue unit := (((((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((addInt 64 ((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__frames) size (0%Z, 0%Z, 0%Z, 0%Z)) >>=
  fun _ => (((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__meta) x) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (vardef_0__push_node)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (vardef_0__push_depth)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__frames) x y) >>=
  fun _ => ((Done _ _ _ 10%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__push (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__push (bools : varsfuncdef_0__push -> bool) (numbers : varsfuncdef_0__push -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__push_body.
Inductive varsfuncdef_0__tokenByte :=
| vardef_0__tokenByte_ch.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__tokenByte : EqDecision varsfuncdef_0__tokenByte := ltac:(solve_decision).
Definition funcdef_0__tokenByte_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte) withLocalVariablesReturnValue unit := (((shortCircuitOr (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (vardef_0__tokenByte_ch)) >>= fun x => (Done _ _ _ 32%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (vardef_0__tokenByte_ch)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (vardef_0__tokenByte_ch)) >>= fun x => (Done _ _ _ 10%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (vardef_0__tokenByte_ch)) >>= fun x => (Done _ _ _ 13%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
    ((Done _ _ _ 17%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  ((((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 1024%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x) >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (vardef_0__tokenByte_ch)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__token) x y) >>=
    fun _ => ((Done _ _ _ 6%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__tokenByte (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__tokenByte (bools : varsfuncdef_0__tokenByte -> bool) (numbers : varsfuncdef_0__tokenByte -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__tokenByte_body.
Inductive varsfuncdef_0__readToken : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__readToken : EqDecision varsfuncdef_0__readToken := ltac:(solve_decision).
Definition funcdef_0__readToken_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken) withLocalVariablesReturnValue unit := (((Done _ _ _ 6%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 14%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 17%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x y) >>=
fun _ => ((((Done _ _ _ 15%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((subInt 64 ((Done _ _ _ 15%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__tokenByte_ch) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__tokenByte y x)) >>=
  fun _ => ((Done _ _ _ 15%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd (((Done _ _ _ 17%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  (tapeEnd (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
    (liftToWithinLoop ((binder_0 >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__tokenByte_ch) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__tokenByte y x))) >>=
    fun _ => ((liftToWithinLoop (shortCircuitOr (((Done _ _ _ 17%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((shortCircuitAnd (((Done _ _ _ 17%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((Done _ _ _ 7%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((Done _ _ _ 14%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__readToken (bools : varsfuncdef_0__readToken -> bool) (numbers : varsfuncdef_0__readToken -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__readToken_body.
Inductive varsfuncdef_0__readNat :=
| vardef_0__readNat_digit
| vardef_0__readNat_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__readNat : EqDecision varsfuncdef_0__readNat := ltac:(solve_decision).
Definition funcdef_0__readNat_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_value) x) >>=
fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (arraydef_0__meta) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (arraydef_0__token) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit) x)) >>=
    fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit)) >>= fun a => (Done _ _ _ 48%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((Done _ _ _ 57%Z) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))))) >>= fun x => if x then (
      (liftToWithinLoop ((Done _ _ _ 14%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (arraydef_0__meta) x y)) >>=
      fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit)) (Done _ _ _ 48%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit) x)) >>=
    fun _ => ((liftToWithinLoop ((divIntUnsigned (subInt 64 (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit))) (Done _ _ _ 10%Z)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_value)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      (liftToWithinLoop ((Done _ _ _ 14%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (arraydef_0__meta) x y)) >>=
      fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_value)) (Done _ _ _ 10%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_digit))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_value) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((Done _ _ _ 11%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (vardef_0__readNat_value)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat (arraydef_0__meta) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__readNat (bools : varsfuncdef_0__readNat -> bool) (numbers : varsfuncdef_0__readNat -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__readNat_body.
Inductive varsfuncdef_0__lookup :=
| vardef_0__lookup_equal.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__lookup : EqDecision varsfuncdef_0__lookup := ltac:(solve_decision).
Definition funcdef_0__lookup_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 18446744073709551615%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__meta) x y) >>=
fun _ => (((Done _ _ _ 4%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__meta) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (element_tuple)))))))) >>= fun x => ((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__meta) x) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (vardef_0__lookup_equal) x)) >>=
    fun _ => (liftToWithinLoop (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__meta) x) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
      ((liftToWithinLoop (((addInt 64 ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (fst (element_tuple))))))) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__names) x) >>= fun x => (binder_1 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__token) x) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
        (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (vardef_0__lookup_equal) x)) >>=
        fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ))))) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (vardef_0__lookup_equal)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
      (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => (binder_0 >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup (arraydef_0__meta) x y)) >>=
      fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__lookup (bools : varsfuncdef_0__lookup -> bool) (numbers : varsfuncdef_0__lookup -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__lookup_body.
Inductive varsfuncdef_0__ok :=
| vardef_0__ok_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__ok : EqDecision varsfuncdef_0__ok := ltac:(solve_decision).
Definition funcdef_0__ok_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok) withLocalVariablesReturnValue unit := ((loopString ("OK ") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok (vardef_0__ok_value)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment1) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok x) >>=
fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__ok (bools : varsfuncdef_0__ok -> bool) (numbers : varsfuncdef_0__ok -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__ok_body.
Inductive varsfuncdef_0__no : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__no : EqDecision varsfuncdef_0__no := ltac:(solve_decision).
Definition funcdef_0__no_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__no) withLocalVariablesReturnValue unit := ((loopString ("NO
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__no) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__no x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__no) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__no (bools : varsfuncdef_0__no -> bool) (numbers : varsfuncdef_0__no -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__no_body.
Inductive varsfuncdef_0__bindName :=
| vardef_0__bindName_value
| vardef_0__bindName_kind.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__bindName : EqDecision varsfuncdef_0__bindName := ltac:(solve_decision).
Definition funcdef_0__bindName_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  ((shortCircuitOr (((Done _ _ _ 4%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((subInt 64 (Done _ _ _ 18446744073709551615%Z) ((Done _ _ _ 5%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x)) >>= fun a => ((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((addInt 64 ((Done _ _ _ 5%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) ((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__names) size (0%Z)) >>=
    fun _ => (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
      (liftToWithinLoop ((addInt 64 ((Done _ _ _ 5%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) binder_0) >>= fun x => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__token) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__names) x y)) >>=
      fun _ => Done _ _ _ tt
    )))) >>=
    fun _ => ((addInt 64 ((Done _ _ _ 4%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__bindings) size (0%Z, 0%Z, 0%Z, 0%Z, 0%Z)) >>=
    fun _ => (((Done _ _ _ 4%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun x => (((Done _ _ _ 5%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun tuple_element_0 => (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) >>= fun tuple_element_1 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (vardef_0__bindName_value)) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (vardef_0__bindName_kind)) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__bindings) x y) >>=
    fun _ => ((Done _ _ _ 5%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 5%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) ((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x y) >>=
    fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (vardef_0__bindName_value)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
    fun _ => ((Done _ _ _ 4%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 4%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__bindName (bools : varsfuncdef_0__bindName -> bool) (numbers : varsfuncdef_0__bindName -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__bindName_body.
Inductive varsfuncdef_0__appendTheorem :=
| vardef_0__appendTheorem_node.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__appendTheorem : EqDecision varsfuncdef_0__appendTheorem := ltac:(solve_decision).
Definition funcdef_0__appendTheorem_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem) withLocalVariablesReturnValue unit := (((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((addInt 64 ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__theorems) size (0%Z)) >>=
    fun _ => (((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (vardef_0__appendTheorem_node)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__theorems) x y) >>=
    fun _ => (((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
    fun _ => ((Done _ _ _ 3%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__appendTheorem (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__appendTheorem (bools : varsfuncdef_0__appendTheorem -> bool) (numbers : varsfuncdef_0__appendTheorem -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__appendTheorem_body.
Inductive varsfuncdef_0__modusPonens :=
| vardef_0__modusPonens_implication
| vardef_0__modusPonens_antecedent
| vardef_0__modusPonens_node.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__modusPonens : EqDecision varsfuncdef_0__modusPonens := ltac:(solve_decision).
Definition funcdef_0__modusPonens_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens) withLocalVariablesReturnValue unit := ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (vardef_0__modusPonens_implication)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (arraydef_0__theorems) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (vardef_0__modusPonens_node) x) >>=
fun _ => ((shortCircuitAnd ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (vardef_0__modusPonens_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (element_tuple))))) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (vardef_0__modusPonens_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (vardef_0__modusPonens_antecedent)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (arraydef_0__theorems) x) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (vardef_0__modusPonens_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__modusPonens (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__appendTheorem_node) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__appendTheorem y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__modusPonens (bools : varsfuncdef_0__modusPonens -> bool) (numbers : varsfuncdef_0__modusPonens -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__modusPonens_body.
Inductive varsfuncdef_0__generalize :=
| vardef_0__generalize_theorem.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__generalize : EqDecision varsfuncdef_0__generalize := ltac:(solve_decision).
Definition funcdef_0__generalize_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__generalize) withLocalVariablesReturnValue unit := (((Done _ _ _ 4%Z) >>= fun preset0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__generalize (vardef_0__generalize_theorem)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__generalize (arraydef_0__theorems) x) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__generalize (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__appendTheorem_node) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__appendTheorem y x)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__generalize (bools : varsfuncdef_0__generalize -> bool) (numbers : varsfuncdef_0__generalize -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__generalize_body.
Inductive varsfuncdef_0__renameIndex :=
| vardef_0__renameIndex_index
| vardef_0__renameIndex_depth
| vardef_0__renameIndex_mode
| vardef_0__renameIndex_shift
| vardef_0__renameIndex_arg
| vardef_0__renameIndex_root
| vardef_0__renameIndex_mapped.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__renameIndex : EqDecision varsfuncdef_0__renameIndex := ltac:(solve_decision).
Definition funcdef_0__renameIndex_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_index)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
fun _ => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_index)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_depth)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
  ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_index)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_depth))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    (((subInt 64 (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_shift)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
      ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_shift))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_arg)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    ) else (
      ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
    (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
      ((Done _ _ _ 2%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun a => (Done _ _ _ 2%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
      (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mode)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_arg)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    ) else (
      (((subInt 64 (Done _ _ _ 18446744073709551615%Z) (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) (Done _ _ _ 1%Z))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_shift)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => ((addInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_root)) (Done _ _ _ 1%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_shift))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped) x) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (((subInt 64 (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_depth)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_mapped)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (vardef_0__renameIndex_depth))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameIndex (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__renameIndex (bools : varsfuncdef_0__renameIndex -> bool) (numbers : varsfuncdef_0__renameIndex -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__renameIndex_body.
Inductive varsfuncdef_0__renameCacheGet :=
| vardef_0__renameCacheGet_node
| vardef_0__renameCacheGet_depth
| vardef_0__renameCacheGet_slot
| vardef_0__renameCacheGet_size.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGet : EqDecision varsfuncdef_0__renameCacheGet := ltac:(solve_decision).
Definition funcdef_0__renameCacheGet_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet) withLocalVariablesReturnValue unit := (((Done _ _ _ 31%Z) >>= fun x => ((Done _ _ _ 18446744073709551615%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__meta) x y) >>=
fun _ => (((Done _ _ _ 29%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_size) x) >>=
fun _ => ((Done _ _ _ 5%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_node)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_depth)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__formulaHash y x)) >>=
fun _ => ((modIntUnsigned ((Done _ _ _ 28%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__meta) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_size))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot) x) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop (shortCircuitAnd ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_node)) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_depth)) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
    (liftToWithinLoop ((Done _ _ _ 31%Z) >>= fun x => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (arraydef_0__meta) x y)) >>=
    fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot)) (Done _ _ _ 1%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_size))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGet (vardef_0__renameCacheGet_slot) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__renameCacheGet (bools : varsfuncdef_0__renameCacheGet -> bool) (numbers : varsfuncdef_0__renameCacheGet -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__renameCacheGet_body.
Inductive varsfuncdef_0__renameCacheGrow :=
| vardef_0__renameCacheGrow_oldSize
| vardef_0__renameCacheGrow_size
| vardef_0__renameCacheGrow_slot
| vardef_0__renameCacheGrow_placed.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGrow : EqDecision varsfuncdef_0__renameCacheGrow := ltac:(solve_decision).
Definition funcdef_0__renameCacheGrow_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow) withLocalVariablesReturnValue unit := ((((Done _ _ _ 29%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_oldSize) x) >>=
fun _ => (((Done _ _ _ 9223372036854775807%Z) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_oldSize)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_oldSize)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) size (0%Z, 0%Z, 0%Z, 0%Z)) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => ((Done _ _ _ 0%Z) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x y)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_oldSize)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
      (liftToWithinLoop ((Done _ _ _ 5%Z) >>= fun preset0 => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun preset1 => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__formulaHash y x))) >>=
      fun _ => (liftToWithinLoop ((modIntUnsigned ((Done _ _ _ 28%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__meta) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_slot) x)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_placed) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
        ((liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_slot)) >>= fun x => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun tuple_element_0 => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun tuple_element_1 => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun tuple_element_2 => ((Done _ _ _ 1%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x y)) >>=
          fun _ => (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_placed) x)) >>=
          fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => (liftToWithinLoop ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_slot)) (Done _ _ _ 1%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_slot) x)) >>=
        fun _ => Done _ _ _ tt
      ))))) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_placed)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
        (liftToWithinLoop ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__meta) x y)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) size (0%Z, 0%Z, 0%Z, 0%Z)) >>=
    fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
      (liftToWithinLoop (binder_0 >>= fun x => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun tuple_element_0 => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun tuple_element_1 => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun tuple_element_2 => (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemoScratch) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__renameMemo) x y)) >>=
      fun _ => Done _ _ _ tt
    )))) >>=
    fun _ => ((Done _ _ _ 29%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (vardef_0__renameCacheGrow_size)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__renameCacheGrow (bools : varsfuncdef_0__renameCacheGrow -> bool) (numbers : varsfuncdef_0__renameCacheGrow -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__renameCacheGrow_body.
Inductive varsfuncdef_0__renameCachePut :=
| vardef_0__renameCachePut_node
| vardef_0__renameCachePut_depth
| vardef_0__renameCachePut_value
| vardef_0__renameCachePut_size
| vardef_0__renameCachePut_slot
| vardef_0__renameCachePut_placed.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__renameCachePut : EqDecision varsfuncdef_0__renameCachePut := ltac:(solve_decision).
Definition funcdef_0__renameCachePut_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut) withLocalVariablesReturnValue unit := ((((((Done _ _ _ 30%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x) >>= fun a => (divIntUnsigned ((Done _ _ _ 29%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x) (Done _ _ _ 2%Z)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
  ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameCacheGrow y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  (((Done _ _ _ 29%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_size) x) >>=
  fun _ => ((Done _ _ _ 5%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_node)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_depth)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__formulaHash_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__formulaHash y x)) >>=
  fun _ => ((modIntUnsigned ((Done _ _ _ 28%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_size))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_placed) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_node)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_depth)) >>= fun tuple_element_1 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_value)) >>= fun tuple_element_2 => ((Done _ _ _ 1%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__renameMemo) x y)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 30%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 30%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x y)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_placed) x)) >>=
      fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((liftToWithinLoop (shortCircuitAnd ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_node)) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__renameMemo) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_depth)) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_node)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_depth)) >>= fun tuple_element_1 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_value)) >>= fun tuple_element_2 => ((Done _ _ _ 1%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__renameMemo) x y)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_placed) x)) >>=
      fun _ => (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot)) (Done _ _ _ 1%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_size))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_slot) x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (vardef_0__renameCachePut_placed)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCachePut (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__renameCachePut (bools : varsfuncdef_0__renameCachePut -> bool) (numbers : varsfuncdef_0__renameCachePut -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__renameCachePut_body.
Inductive varsfuncdef_0__rename :=
| vardef_0__rename_node
| vardef_0__rename_width
| vardef_0__rename_pairs
| vardef_0__rename_budget
| vardef_0__rename_mode
| vardef_0__rename_shift
| vardef_0__rename_arg
| vardef_0__rename_initialDepth
| vardef_0__rename_top
| vardef_0__rename_current
| vardef_0__rename_depth
| vardef_0__rename_phase
| vardef_0__rename_tag
| vardef_0__rename_a
| vardef_0__rename_b
| vardef_0__rename_left
| vardef_0__rename_result.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__rename : EqDecision varsfuncdef_0__rename := ltac:(solve_decision).
Definition funcdef_0__rename_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename) withLocalVariablesReturnValue unit := (((Done _ _ _ 10%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 29%Z) >>= fun x => ((Done _ _ _ 16%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 30%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 16%Z) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__renameMemo) size (0%Z, 0%Z, 0%Z, 0%Z)) >>=
fun _ => ((Done _ _ _ 16%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => ((Done _ _ _ 0%Z) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__renameMemo) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_node)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_node)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_width) x) >>=
  fun _ => (((divIntUnsigned (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_width))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_width)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_width)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_width))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_pairs) x) >>=
    fun _ => (((divIntUnsigned (Done _ _ _ 18446744073709551614%Z) (Done _ _ _ 5%Z)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_pairs)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
      ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
      fun _ => Done _ _ _ tt
    ) else (
      ((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_pairs)) (Done _ _ _ 5%Z)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_budget) x) >>=
      fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_node)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_initialDepth)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__push_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__push_depth) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__push y x)) >>=
      fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_budget)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
        ((liftToWithinLoop (shortCircuitOr (((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
          (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => (liftToWithinLoop ((subInt 64 ((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_phase) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_left) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_a) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_b) x)) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_phase)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCacheGet_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCacheGet_depth) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameCacheGet y x))) >>=
          fun _ => ((liftToWithinLoop (((Done _ _ _ 31%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
            (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 31%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
            fun _ => (liftToWithinLoop ((Done _ _ _ 10%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
              (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
              fun _ => (liftToWithinLoop ((Done _ _ _ 10%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
              fun _ => ((liftToWithinLoop (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
                (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_value) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameCachePut y x))) >>=
                fun _ => Done _ _ _ tt
              ) else (
                Done _ _ _ tt
              )) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
              (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_a)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_mode)) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_shift)) >>= fun preset3 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_arg)) >>= fun preset4 => ((((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_index) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_mode) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_shift) preset3)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_arg) preset4)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameIndex y x))) >>=
              fun _ => (liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_a) x)) >>=
              fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_b)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_mode)) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_shift)) >>= fun preset3 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_arg)) >>= fun preset4 => ((((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_index) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_mode) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_shift) preset3)) >>= fun x => Done _ _ _ (update x (vardef_0__renameIndex_arg) preset4)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameIndex y x))) >>=
              fun _ => (liftToWithinLoop (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_b) x)) >>=
              fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_b)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x))) >>=
              fun _ => (liftToWithinLoop ((Done _ _ _ 10%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
              fun _ => ((liftToWithinLoop (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
                (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_value) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameCachePut y x))) >>=
                fun _ => Done _ _ _ tt
              ) else (
                Done _ _ _ tt
              )) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
              (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun tuple_element_1 => ((Done _ _ _ 1%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x y)) >>=
              fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_a)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__push_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__push_depth) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__push y x))) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_tag)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
              ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
                (liftToWithinLoop ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
                fun _ => Done _ _ _ tt
              ) else (
                (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun tuple_element_1 => ((Done _ _ _ 3%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x y)) >>=
                fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_a)) >>= fun preset0 => (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) (Done _ _ _ 1%Z)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__push_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__push_depth) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__push y x))) >>=
                fun _ => Done _ _ _ tt
              )) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_phase)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun tuple_element_1 => ((Done _ _ _ 2%Z) >>= fun tuple_element_2 => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun tuple_element_3 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__frames) x y)) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_b)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__push_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__push_depth) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__push y x))) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_phase)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_left)) >>= fun preset1 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x))) >>=
          fun _ => (liftToWithinLoop ((Done _ _ _ 10%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
          fun _ => ((liftToWithinLoop (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_value) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameCachePut y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_phase)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((Done _ _ _ 4%Z) >>= fun preset0 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x))) >>=
          fun _ => (liftToWithinLoop ((Done _ _ _ 10%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_top)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y)) >>=
          fun _ => ((liftToWithinLoop (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_current)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (vardef_0__rename_depth)) >>= fun preset1 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__renameCachePut_value) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__renameCachePut y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      )))) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => ((((Done _ _ _ 10%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__rename (bools : varsfuncdef_0__rename -> bool) (numbers : varsfuncdef_0__rename -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__rename_body.
Inductive varsfuncdef_0__predicate :=
| vardef_0__predicate_cls
| vardef_0__predicate_shift
| vardef_0__predicate_arg
| vardef_0__predicate_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__predicate : EqDecision varsfuncdef_0__predicate := ltac:(solve_decision).
Definition funcdef_0__predicate_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate) withLocalVariablesReturnValue unit := ((((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ (fst (element_tuple)))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_value) x) >>=
  fun _ => (((subInt 64 (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_value))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_shift)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 2%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_arg)) >>= fun preset1 => (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_value)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_shift))) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset0 => (Done _ _ _ 6%Z) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_shift)) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate (vardef_0__predicate_arg)) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__predicate (bools : varsfuncdef_0__predicate -> bool) (numbers : varsfuncdef_0__predicate -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__predicate_body.
Inductive varsfuncdef_0__classEqual :=
| vardef_0__classEqual_a
| vardef_0__classEqual_b
| vardef_0__classEqual_left
| vardef_0__classEqual_right
| vardef_0__classEqual_t0
| vardef_0__classEqual_t1
| vardef_0__classEqual_t2
| vardef_0__classEqual_t3
| vardef_0__classEqual_t4
| vardef_0__classEqual_t5.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__classEqual : EqDecision varsfuncdef_0__classEqual := ltac:(solve_decision).
Definition funcdef_0__classEqual_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual) withLocalVariablesReturnValue unit := (((shortCircuitAnd ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ (fst (element_tuple)))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_b)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ (fst (element_tuple)))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun preset0 => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset1 => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_b)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_a)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_shift) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_arg) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__predicate y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_left) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_b)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_shift) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_arg) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__predicate y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_right) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_left)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_right)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_right)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_left)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t2)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t3)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t4) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t5) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (vardef_0__classEqual_t5)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__classEqual (bools : varsfuncdef_0__classEqual -> bool) (numbers : varsfuncdef_0__classEqual -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__classEqual_body.
Inductive varsfuncdef_0__classMember :=
| vardef_0__classMember_a
| vardef_0__classMember_b
| vardef_0__classMember_left
| vardef_0__classMember_right
| vardef_0__classMember_t0
| vardef_0__classMember_t1
| vardef_0__classMember_t2
| vardef_0__classMember_t3
| vardef_0__classMember_t4
| vardef_0__classMember_t5
| vardef_0__classMember_t6
| vardef_0__classMember_t7
| vardef_0__classMember_t8
| vardef_0__classMember_t9
| vardef_0__classMember_t10
| vardef_0__classMember_t11
| vardef_0__classMember_t12.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__classMember : EqDecision varsfuncdef_0__classMember := ltac:(solve_decision).
Definition funcdef_0__classMember_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember) withLocalVariablesReturnValue unit := ((((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ (fst (element_tuple)))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_b)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_shift) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_arg) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__predicate y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_a)) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_shift) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_arg) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__predicate y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_left) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_b)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_shift) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_arg) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__predicate y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_right) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_left)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_left)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t5) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t6) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_right)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t6)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t7)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t8)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t9) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t9)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t10) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t10)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t11) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t11)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t12) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (vardef_0__classMember_t12)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__classMember (bools : varsfuncdef_0__classMember -> bool) (numbers : varsfuncdef_0__classMember -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__classMember_body.
Inductive varsfuncdef_0__setness :=
| vardef_0__setness_cls
| vardef_0__setness_index
| vardef_0__setness_body
| vardef_0__setness_t0
| vardef_0__setness_t1
| vardef_0__setness_t2
| vardef_0__setness_t3
| vardef_0__setness_t4
| vardef_0__setness_t5
| vardef_0__setness_t6
| vardef_0__setness_t7
| vardef_0__setness_t8
| vardef_0__setness_t9.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__setness : EqDecision varsfuncdef_0__setness := ltac:(solve_decision).
Definition funcdef_0__setness_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness) withLocalVariablesReturnValue unit := ((((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ (fst (element_tuple)))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_index) x) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_index)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 1%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_index)) (Done _ _ _ 1%Z)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
    fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t0) x) >>=
    fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t0)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
    fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t1) x) >>=
    fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
    fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t2) x) >>=
    fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
    fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t3) x) >>=
    fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t3)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_cls)) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_shift) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__predicate_arg) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__predicate y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_body) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_body)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_body)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t5) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t6) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t7) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t7)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t8)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t9) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (vardef_0__setness_t9)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__setness (bools : varsfuncdef_0__setness -> bool) (numbers : varsfuncdef_0__setness -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__setness_body.
Inductive varsfuncdef_0__axiom :=
| vardef_0__axiom_tag
| vardef_0__axiom_p
| vardef_0__axiom_q
| vardef_0__axiom_r
| vardef_0__axiom_t0
| vardef_0__axiom_t1
| vardef_0__axiom_t2
| vardef_0__axiom_t3
| vardef_0__axiom_t4
| vardef_0__axiom_t5
| vardef_0__axiom_t6
| vardef_0__axiom_t7
| vardef_0__axiom_t8
| vardef_0__axiom_t9
| vardef_0__axiom_t10
| vardef_0__axiom_t11
| vardef_0__axiom_t12
| vardef_0__axiom_t13
| vardef_0__axiom_t14
| vardef_0__axiom_t15
| vardef_0__axiom_t16
| vardef_0__axiom_t17
| vardef_0__axiom_t18
| vardef_0__axiom_t19
| vardef_0__axiom_t20
| vardef_0__axiom_t21
| vardef_0__axiom_t22
| vardef_0__axiom_t23
| vardef_0__axiom_t24
| vardef_0__axiom_t25
| vardef_0__axiom_t26
| vardef_0__axiom_t27
| vardef_0__axiom_t28
| vardef_0__axiom_t29
| vardef_0__axiom_t30
| vardef_0__axiom_t31
| vardef_0__axiom_t32
| vardef_0__axiom_t33
| vardef_0__axiom_t34
| vardef_0__axiom_t35
| vardef_0__axiom_t36
| vardef_0__axiom_t37
| vardef_0__axiom_t38
| vardef_0__axiom_t39
| vardef_0__axiom_t40
| vardef_0__axiom_t41.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__axiom : EqDecision varsfuncdef_0__axiom := ltac:(solve_decision).
Definition funcdef_0__axiom_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom) withLocalVariablesReturnValue unit := (((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
fun _ => ((shortCircuitAnd (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd (shortCircuitAnd (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => (Done _ _ _ 0%Z) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 7%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 8%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_q)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_r)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 10%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 11%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 12%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 3%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 13%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 3%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 14%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t15) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t15)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t16) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t16)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t17) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t17)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t18) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t18)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t19) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t19)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t20) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t20)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t21) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t21)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t22) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t22)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t23) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t23)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t24) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t24)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t25) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t25)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t26) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t26)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t27) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t27)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t28) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t28)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t29) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t29)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t30) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t30)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t31) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t31)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t32) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t32)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 15%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => (Done _ _ _ 0%Z) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 16%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset0 => (Done _ _ _ 3%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => (Done _ _ _ 0%Z) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset0 => (Done _ _ _ 4%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => (Done _ _ _ 0%Z) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 3%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_p)) >>= fun preset0 => (Done _ _ _ 5%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => (Done _ _ _ 0%Z) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_arg) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t15) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t15)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t16) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t16)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t17) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t17)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t18) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t18)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t19) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t19)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t20) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t20)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t21) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t21)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t22) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t22)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t23) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t23)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_tag)) >>= fun x => (Done _ _ _ 17%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (Done _ _ _ true)) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t2)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t3)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t4)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 2%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t1)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t8)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t9)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t10)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t11)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t12)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t13)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t14)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t15) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t6)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t15)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t16) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t16)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t17) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t17)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t18) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t18)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t19) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t5)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t19)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t20) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t20)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t21) x) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 3%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t22) x) >>=
  fun _ => ((Done _ _ _ 1%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 1%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t23) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t22)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t23)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t24) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t24)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t25) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t25)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t26) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t26)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t27) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t27)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t28) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t28)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t29) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t29)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t30) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t0)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t30)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t31) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t31)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t32) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t32)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t33) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t33)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t34) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t34)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t35) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t7)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t35)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t36) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t36)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t37) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t37)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t38) x) >>=
  fun _ => ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t38)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t39) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t39)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t40) x) >>=
  fun _ => ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t21)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t40)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t41) x) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (vardef_0__axiom_t41)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 13%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__axiom (bools : varsfuncdef_0__axiom -> bool) (numbers : varsfuncdef_0__axiom -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__axiom_body.
Inductive varsfuncdef_0__schemaCheck :=
| vardef_0__schemaCheck_node
| vardef_0__schemaCheck_type.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__schemaCheck : EqDecision varsfuncdef_0__schemaCheck := ltac:(solve_decision).
Definition funcdef_0__schemaCheck_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck) withLocalVariablesReturnValue unit := (((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (vardef_0__schemaCheck_node)) >>= fun a => ((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
  ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  (((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (vardef_0__schemaCheck_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (vardef_0__schemaCheck_type)) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
    ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((((Done _ _ _ 19%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__meta) x) >>= fun a => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (vardef_0__schemaCheck_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((Done _ _ _ 19%Z) >>= fun x => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (vardef_0__schemaCheck_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__schemaCheck (bools : varsfuncdef_0__schemaCheck -> bool) (numbers : varsfuncdef_0__schemaCheck -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__schemaCheck_body.
Inductive varsfuncdef_0__schemaNode :=
| vardef_0__schemaNode_kind
| vardef_0__schemaNode_a
| vardef_0__schemaNode_b
| vardef_0__schemaNode_c
| vardef_0__schemaNode_d
| vardef_0__schemaNode_type.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__schemaNode : EqDecision varsfuncdef_0__schemaNode := ltac:(solve_decision).
Definition funcdef_0__schemaNode_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode) withLocalVariablesReturnValue unit := (((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 19%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
fun _ => (((Done _ _ _ 11%Z) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((Done _ _ _ 19%Z) >>= fun x => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
  ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
  fun _ => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
    ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_b)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 7%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_b)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 8%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
  fun _ => (((Done _ _ _ 17%Z) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 15%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 16%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_b)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_c)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_d)) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 10%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
  fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_b)) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaCheck_type) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaCheck y x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun x => (Done _ _ _ 11%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 2%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type) x) >>=
  fun _ => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
    ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__theorems) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a) x) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => ((((Done _ _ _ 18%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
  fun _ => Done _ _ _ tt
) else (
  ((((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((addInt 64 ((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__schemaNodes) size (0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z)) >>=
    fun _ => (((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_kind)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_a)) >>= fun tuple_element_1 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_b)) >>= fun tuple_element_2 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_c)) >>= fun tuple_element_3 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_d)) >>= fun tuple_element_4 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (vardef_0__schemaNode_type)) >>= fun tuple_element_5 => (((Done _ _ _ 19%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun tuple_element_6 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4, tuple_element_5, tuple_element_6)))))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__schemaNodes) x y) >>=
    fun _ => (((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
    fun _ => ((Done _ _ _ 16%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaNode (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__schemaNode (bools : varsfuncdef_0__schemaNode -> bool) (numbers : varsfuncdef_0__schemaNode -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__schemaNode_body.
Inductive varsfuncdef_0__schemaClass :=
| vardef_0__schemaClass_kind
| vardef_0__schemaClass_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__schemaClass : EqDecision varsfuncdef_0__schemaClass := ltac:(solve_decision).
Definition funcdef_0__schemaClass_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass) withLocalVariablesReturnValue unit := (((((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((addInt 64 ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__classes) size (0%Z, 0%Z)) >>=
  fun _ => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (vardef_0__schemaClass_kind)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (vardef_0__schemaClass_value)) >>= fun tuple_element_1 => Done _ _ _ (tuple_element_0, tuple_element_1))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__classes) x y) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 2%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaClass (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__schemaClass (bools : varsfuncdef_0__schemaClass -> bool) (numbers : varsfuncdef_0__schemaClass -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__schemaClass_body.
Inductive varsfuncdef_0__schemaShiftClass :=
| vardef_0__schemaShiftClass_cls
| vardef_0__schemaShiftClass_depth
| vardef_0__schemaShiftClass_value.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__schemaShiftClass : EqDecision varsfuncdef_0__schemaShiftClass := ltac:(solve_decision).
Definition funcdef_0__schemaShiftClass_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_cls)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (arraydef_0__meta) x y) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_depth)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_value) x) >>=
  fun _ => (((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_cls)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (arraydef_0__classes) x) >>= (fun element_tuple => Done _ _ _ (fst (element_tuple)))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    (((subInt 64 (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_value))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_depth)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
      ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (arraydef_0__meta) x y) >>=
      fun _ => Done _ _ _ tt
    ) else (
      ((Done _ _ _ 0%Z) >>= fun preset0 => (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_value)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_depth))) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaClass_kind) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaClass_value) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaClass y x)) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_value)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (vardef_0__schemaShiftClass_depth)) >>= fun preset2 => (Done _ _ _ 1%Z) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_mode) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_shift) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__rename_initialDepth) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__rename y x)) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ 1%Z) >>= fun preset0 => ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaShiftClass (arraydef_0__meta) x) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaClass_kind) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaClass_value) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaClass y x)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__schemaShiftClass (bools : varsfuncdef_0__schemaShiftClass -> bool) (numbers : varsfuncdef_0__schemaShiftClass -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__schemaShiftClass_body.
Inductive varsfuncdef_0__schemaMark :=
| vardef_0__schemaMark_node
| vardef_0__schemaMark_depth
| vardef_0__schemaMark_width.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__schemaMark : EqDecision varsfuncdef_0__schemaMark := ltac:(solve_decision).
Definition funcdef_0__schemaMark_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaMark) withLocalVariablesReturnValue unit := (((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaMark (vardef_0__schemaMark_node)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaMark (vardef_0__schemaMark_width))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaMark (vardef_0__schemaMark_depth))) >>= fun x => (((Done _ _ _ 1%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaMark (arraydef_0__schemaMarks) x y) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__schemaMark (bools : varsfuncdef_0__schemaMark -> bool) (numbers : varsfuncdef_0__schemaMark -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__schemaMark_body.
Inductive varsfuncdef_0__schemaInstance :=
| vardef_0__schemaInstance_root
| vardef_0__schemaInstance_width
| vardef_0__schemaInstance_size
| vardef_0__schemaInstance_node
| vardef_0__schemaInstance_depth
| vardef_0__schemaInstance_key
| vardef_0__schemaInstance_kind
| vardef_0__schemaInstance_a
| vardef_0__schemaInstance_b
| vardef_0__schemaInstance_c
| vardef_0__schemaInstance_d
| vardef_0__schemaInstance_va
| vardef_0__schemaInstance_vb
| vardef_0__schemaInstance_vc.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__schemaInstance : EqDecision varsfuncdef_0__schemaInstance := ltac:(solve_decision).
Definition funcdef_0__schemaInstance_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue unit := (((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_root)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width) x) >>=
fun _ => (((divIntUnsigned (Done _ _ _ 18446744073709551615%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_size) x) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaMarks) size (0%Z)) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) size (0%Z)) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_size)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaMarks) x y)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_root)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x)) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_root)) binder_0) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
      (liftToWithinLoop ((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_key) x)) >>=
      fun _ => ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_key)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaMarks) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
        (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (fst (fst (fst (element_tuple))))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (fst (fst (element_tuple)))))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (fst (element_tuple))))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (element_tuple)))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_c) x)) >>=
        fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_d) x)) >>=
        fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 7%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 10%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun preset0 => (addInt 64 binder_1 (Done _ _ _ 1%Z)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x))) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun preset0 => binder_1 >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x))) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b)) >>= fun preset0 => binder_1 >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x))) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 8%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          ((liftToWithinLoop (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 15%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 16%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b)) >>= fun preset0 => binder_1 >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_c)) >>= fun preset0 => binder_1 >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_d)) >>= fun preset0 => binder_1 >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_node) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_depth) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaMark_width) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaMark y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ))))) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop (shortCircuitOr (((Done _ _ _ 18%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
      ((liftToWithinLoop (shortCircuitOr (((Done _ _ _ 18%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
        (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (multInt 64 binder_0 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_key) x)) >>=
      fun _ => ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_key)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaMarks) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
        (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (fst (fst (fst (element_tuple))))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind) x)) >>=
        fun _ => (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (fst (fst (element_tuple)))))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a) x)) >>=
        fun _ => (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (fst (element_tuple))))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b) x)) >>=
        fun _ => (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (element_tuple)))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_c) x)) >>=
        fun _ => (liftToWithinLoop (((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_d) x)) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaArguments) x) >>= fun preset0 => binder_1 >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaShiftClass_cls) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaShiftClass_depth) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaShiftClass y x))) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 11%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
          (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x y)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun preset0 => ((addInt 64 (addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaClass_kind) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaClass_value) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaClass y x))) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
          (liftToWithinLoop (((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va) x)) >>=
          fun _ => (liftToWithinLoop (((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb) x)) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__classEqual_a) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__classEqual_b) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__classEqual y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__classMember_a) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__classMember_b) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__classMember y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x))) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            ((liftToWithinLoop (shortCircuitAnd ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (element_tuple))))) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb)) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
              (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__formulas) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x y)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              (liftToWithinLoop ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x y)) >>=
              fun _ => Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 7%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 10%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
          (liftToWithinLoop ((Done _ _ _ 4%Z) >>= fun preset0 => ((addInt 64 (addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x))) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_kind)) >>= fun x => (Done _ _ _ 8%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va) x)) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_c)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb) x)) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_d)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vc) x)) >>=
          fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 15%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 16%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
            (liftToWithinLoop (((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_b)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va) x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop (shortCircuitOr (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))))) >>= fun x => if x then (
            (liftToWithinLoop (((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_c)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb) x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop (((addInt 64 (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_d)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vc) x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_a)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_va)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vb)) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_vc)) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_p) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_q) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_r) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__axiom y x))) >>=
          fun _ => ((liftToWithinLoop (((Done _ _ _ 13%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            (liftToWithinLoop ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x y)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_key)) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x y)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ))))) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => ((shortCircuitAnd (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 18%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
    ((Done _ _ _ 0%Z) >>= fun x => (((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_root)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (vardef_0__schemaInstance_width))) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__schemaValues) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaInstance (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__schemaInstance (bools : varsfuncdef_0__schemaInstance -> bool) (numbers : varsfuncdef_0__schemaInstance -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__schemaInstance_body.
Inductive varsfuncdef_0__command :=
| vardef_0__command_op
| vardef_0__command_a
| vardef_0__command_b
| vardef_0__command_c
| vardef_0__command_tag
| vardef_0__command_node
| vardef_0__command_binding.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__command : EqDecision varsfuncdef_0__command := ltac:(solve_decision).
Definition funcdef_0__command_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue unit := (((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op) x) >>=
fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((shortCircuitAnd (shortCircuitAnd (((Done _ _ _ 7%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) (((Done _ _ _ 6%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((Done _ _ _ 9%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
) else (
  (((Done _ _ _ 26%Z) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ 9%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => (loopString ("BYE
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
          (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
          fun _ => Done _ _ _ tt
        )))) >>=
        fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ 1%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ 2%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 3%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        ((Done _ _ _ 3%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 4%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
        ((Done _ _ _ 4%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 5%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          ((addInt 64 ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__classes) size (0%Z, 0%Z)) >>=
          fun _ => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun tuple_element_1 => Done _ _ _ (tuple_element_0, tuple_element_1))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__classes) x y) >>=
          fun _ => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => ((Done _ _ _ 2%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 6%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
        ((((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          ((addInt 64 ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__classes) size (0%Z, 0%Z)) >>=
          fun _ => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun tuple_element_1 => Done _ _ _ (tuple_element_0, tuple_element_1))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__classes) x y) >>=
          fun _ => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => ((Done _ _ _ 2%Z) >>= fun x => ((addInt 64 ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 7%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__classEqual_a) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__classEqual_b) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__classEqual y x)) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 8%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__classMember_a) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__classMember_b) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__classMember y x)) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 9%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x)) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__bindName_value) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__bindName_kind) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__bindName y x)) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 10%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => ((shortCircuitOr (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 11%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_tag) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_c) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_tag)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_c)) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_p) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_q) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__axiom_r) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__axiom y x)) >>=
        fun _ => ((((Done _ _ _ 13%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__appendTheorem_node) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__appendTheorem y x)) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 12%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__modusPonens_implication) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__modusPonens_antecedent) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__modusPonens y x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 13%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
        ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__generalize_theorem) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__generalize y x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 14%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding) x) >>=
          fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
            fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
            fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
              ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
            ((shortCircuitAnd (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
              ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__setness_cls) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__setness y x)) >>=
              fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
                ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__theorems) x) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
                  ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (fst (element_tuple))))))) >>= fun tuple_element_0 => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (element_tuple)))))))) >>= fun tuple_element_1 => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun tuple_element_2 => ((Done _ _ _ 1%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x y) >>=
                  fun _ => ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
                  fun _ => Done _ _ _ tt
                ) else (
                  ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
                  fun _ => Done _ _ _ tt
                )) >>=
                fun _ => Done _ _ _ tt
              ) else (
                Done _ _ _ tt
              )) >>=
              fun _ => Done _ _ _ tt
            ) else (
              ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
              fun _ => Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 15%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => ((shortCircuitOr (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
              (loopString ("SET
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
                (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
                fun _ => Done _ _ _ tt
              )))) >>=
              fun _ => Done _ _ _ tt
            ) else (
              (loopString ("CLASS
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
                (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
                fun _ => Done _ _ _ tt
              )))) >>=
              fun _ => Done _ _ _ tt
            )) >>=
            fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 16%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          ((Done _ _ _ 3%Z) >>= fun x => ((subInt 64 ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => (((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 17%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ 3%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => ((Done _ _ _ 0%Z) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 18%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun a => ((Done _ _ _ 1%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__theorems) x) >>= fun x => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__appendTheorem_node) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__appendTheorem y x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 19%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
        (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__theorems) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 20%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 3%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => if x then (
            (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__theorems) x) >>= fun preset0 => (Done _ _ _ 1%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__bindName_value) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__bindName_kind) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__bindName y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 21%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => ((shortCircuitOr (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            (((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__appendTheorem_node) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__appendTheorem y x)) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 22%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_tag) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_c) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_node) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_tag)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset1 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_c)) >>= fun preset3 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_node)) >>= fun preset4 => ((((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaNode_kind) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaNode_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaNode_b) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaNode_c) preset3)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaNode_d) preset4)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaNode y x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 23%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
      fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
      fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
        ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun a => ((Done _ _ _ 16%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
            ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun preset0 => (Done _ _ _ 2%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__bindName_value) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__bindName_kind) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__bindName y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 24%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding) x) >>=
          fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
            fun _ => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a) x) >>=
            fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
              ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
            ((liftToWithinLoop (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
              (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x))) >>=
              fun _ => (liftToWithinLoop (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b) x)) >>=
              fun _ => ((liftToWithinLoop (((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
                (liftToWithinLoop ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y)) >>=
                fun _ => Done _ _ _ tt
              ) else (
                Done _ _ _ tt
              )) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((liftToWithinLoop (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
              (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun a => ((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
              (liftToWithinLoop ((Done _ _ _ 18%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => (liftToWithinLoop ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__schemaArguments) size (0%Z))) >>=
            fun _ => (liftToWithinLoop (binder_0 >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_b)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__schemaArguments) x y)) >>=
            fun _ => Done _ _ _ tt
          )))) >>=
          fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
            ((shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
              ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_binding)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_node) x) >>=
              fun _ => ((shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_a)) >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_node)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun y => Done _ _ _ (bool_decide (x <> y))) (((Done _ _ _ 18%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
                ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
                fun _ => Done _ _ _ tt
              ) else (
                ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_node)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__schemaInstance_root) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__schemaInstance y x)) >>=
                fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
                  ((((Done _ _ _ 18%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
                    ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
                    fun _ => Done _ _ _ tt
                  ) else (
                    (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__appendTheorem_node) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__appendTheorem y x)) >>=
                    fun _ => Done _ _ _ tt
                  )) >>=
                  fun _ => Done _ _ _ tt
                ) else (
                  Done _ _ _ tt
                )) >>=
                fun _ => Done _ _ _ tt
              )) >>=
              fun _ => Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          ) else (
            Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 25%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
              (loopString ("CLASS
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
                (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
                fun _ => Done _ _ _ tt
              )))) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
              (loopString ("THEOREM
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
                (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
                fun _ => Done _ _ _ tt
              )))) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => ((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
              (loopString ("SCHEMA
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
                (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
                fun _ => Done _ _ _ tt
              )))) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (vardef_0__command_op)) >>= fun x => (Done _ _ _ 26%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) (((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
      ((Done _ _ _ true) >>= fun x => if x then (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readToken y x)) >>=
        fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
          ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__lookup y x)) >>=
          fun _ => ((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 18446744073709551615%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
            ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
            fun _ => Done _ _ _ tt
          ) else (
            ((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => (Done _ _ _ 2%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
              ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              (((((((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__bindings) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__schemaNodes) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__ok_value) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__ok y x)) >>=
              fun _ => Done _ _ _ tt
            )) >>=
            fun _ => Done _ _ _ tt
          )) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      ) else (
        ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__no y x)) >>=
        fun _ => Done _ _ _ tt
      )) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  (loopString ("ERR
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) >>=
  fun _ => ((Done _ _ _ 9%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__command (bools : varsfuncdef_0__command -> bool) (numbers : varsfuncdef_0__command -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__command_body.
Inductive varsfuncdef_0__main : Type :=.
#[export] Instance variableIndexEqualityDecidablevarsfuncdef_0__main : EqDecision varsfuncdef_0__main := ltac:(solve_decision).
Definition funcdef_0__main_body : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue unit := ((loopString ("SEED
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
  ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x y) >>=
  fun _ => Done _ _ _ tt
) else (
  ((Done _ _ _ 26%Z) >>= fun x => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__readNat y x)) >>=
  fun _ => ((((Done _ _ _ 14%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) >>= fun x => if x then (
    ((Done _ _ _ 8%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((Done _ _ _ 27%Z) >>= fun x => (((Done _ _ _ 11%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x y) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => ((((Done _ _ _ 8%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) >>= fun x => if x then (
  (loopString ("ERR
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
  fun _ => Done _ _ _ tt
) else (
  ((Done _ _ _ 20%Z) >>= fun x => ((Done _ _ _ 1024%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x y) >>=
  fun _ => ((Done _ _ _ 0%Z) >>= fun preset0 => (Done _ _ _ 0%Z) >>= fun preset1 => (Done _ _ _ 0%Z) >>= fun preset2 => ((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_tag) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_a) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__intern_b) preset2)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__intern y x)) >>=
  fun _ => (loopString ("READY
") (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
    (liftToWithinLoop (binder_0 >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main x)) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => (flush arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
  fun _ => (tapeEnd (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ binder_0_intermediate in dropWithinLoop ((
    (liftToWithinLoop ((Done _ _ _ 15%Z) >>= fun x => ((addInt 64 (binder_0 >>= fun x => Done _ _ _ (coerceInt x 64)) (Done _ _ _ 1%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x y)) >>=
    fun _ => (liftToWithinLoop ((Done _ _ _ (fun x => 0%Z)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__command y x))) >>=
    fun _ => ((liftToWithinLoop (((Done _ _ _ 9%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__meta) x) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y)))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )))) >>=
  fun _ => Done _ _ _ tt
)) >>=
fun _ => Done _ _ _ tt).
Definition funcdef_0__main (bools : varsfuncdef_0__main -> bool) (numbers : varsfuncdef_0__main -> Z) : Action (WithArrays _ (arrayType _ environment1)) withArraysReturnValue unit := eliminateLocalVariables bools numbers funcdef_0__main_body.
