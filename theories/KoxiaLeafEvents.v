From CoqCP Require Import Options Imperative Execution KoxiaPolynomial KoxiaModular KoxiaIntegers
  KoxiaArrays KoxiaTables KoxiaTableLoops KoxiaArrayLoops KoxiaPolynomialBuffers KoxiaLeaf SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition leafEventBody (x : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
        (liftToWithinLoop ((subInt 64 ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) binder_1) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x) ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag) x)) >>=
        fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous) x)) >>=
        fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => loop (Z.to_nat x) (ordinaryCoefficientBody x))) >>=
          fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
          fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => loop (Z.to_nat x) (specialCoefficientBody x))) >>=
          fun _ => Done _ _ _ tt
        )) >>=
        fun _ => Done _ _ _ tt
      )).

Definition ordinaryEventAction len nums :=
  ordinaryAction len len (update nums vardef_0__solve_previous 0) >>= fun final =>
  tableWrite arraydef_0__poly (final vardef_0__solve_length) (final vardef_0__solve_previous) >>= fun _ =>
  Done _ _ _ (update final vardef_0__solve_length (coerceInt (final vardef_0__solve_length+1) 64)).
Definition specialEventAction len nums := specialAction len len (update nums vardef_0__solve_previous 0).
Definition leafEventAction start index len nums :=
  tableRead arraydef_0__prefix (Z.of_nat (start+index+1)) >>= fun next =>
  tableRead arraydef_0__prefix (Z.of_nat (start+index)) >>= fun previous =>
  let flagged := update nums vardef_0__solve_flag (coerceInt (next-previous) 64) in
  if bool_decide (coerceInt (next-previous) 64=0) then ordinaryEventAction len flagged else specialEventAction len flagged.
Lemma leafEventNormalized b nums total remaining start len continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_length=Z.of_nat len ->
  (remaining<total)%nat -> Z.of_nat (start+total+1)<18446744073709551616 -> Z.of_nat len<koxiaModulus ->
  eliminateLocalVariables b nums (leafEventBody (Z.of_nat total) remaining >>= continuation)=
  leafEventAction start (total-remaining-1) len nums >>= fun final =>
    eliminateLocalVariables b final (continuation KeepGoing).
Proof.
  intros leftEq lengthEq bound addressesFit lengthBound.
  unfold leafEventBody,numberLocalGet,numberLocalSet,retrieve,store,addInt,subInt,modIntUnsigned.
  normalize_table_loop. rewrite leftEq.
  assert (indexId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite indexId.
  assert (leftIndex : coerceInt (Z.of_nat start+Z.of_nat (total-remaining-1)) 64=Z.of_nat (start+(total-remaining-1))).
  { rewrite coerce64_small by lia. lia. }
  rewrite leftIndex.
  assert (rightIndex : coerceInt (Z.of_nat (start+(total-remaining-1))+1) 64=Z.of_nat (start+(total-remaining-1)+1)).
  { rewrite coerce64_small by lia. lia. }
  rewrite rightIndex. unfold leafEventAction,tableRead. cbn [bind].
  apply f_equal. apply functional_extensionality. intro next. normalize_table_loop. rewrite leftEq,leftIndex.
  apply f_equal. apply functional_extensionality. intro previous. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite lookupSame.
  cbn [withLocalVariablesReturnValue withArraysReturnValue] in *.
  destruct (bool_decide (coerceInt (next-previous) 64=0)) eqn:ordinary.
  - rewrite ?ordinary. normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite lengthEq,Nat2Z.id.
    rewrite ordinaryLoopNormalized by lia. unfold ordinaryEventAction. rewrite <-bindAssoc.
    apply f_equal. apply functional_extensionality. intro final.
    normalize_table_loop.
    reflexivity.
  - rewrite ?ordinary. normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite lengthEq,Nat2Z.id.
    rewrite specialLoopNormalized by (try rewrite !lookupDifferent by congruence; try assumption; lia).
    unfold specialEventAction. reflexivity.
Qed.

Theorem ordinaryEventAction_execution len nums state values :
  nums vardef_0__solve_length=Z.of_nat len -> (S len<=length values)%nat -> Z.of_nat len<koxiaModulus -> tableCanonical values ->
  exists final,
    exec (ordinaryEventAction len nums) (withArray state arraydef_0__poly values)=
      Some (final,withArray state arraydef_0__poly (ordinaryBuffer values len)) /\
    final vardef_0__solve_length=Z.of_nat (S len) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous -> name<>vardef_0__solve_length -> final name=nums name).
Proof.
  intros lengthEq room lenBound canonical. unfold ordinaryEventAction. rewrite exec_bind.
  destruct (ordinaryAction_execution len 0 len state values (update nums vardef_0__solve_previous 0) eq_refl ltac:(lia)
    canonical ltac:(rewrite lookupSame; reflexivity)) as [finished [execution [previousEq others]]].
  cbn [fillValues] in execution. rewrite execution. cbn [optionBind fst snd].
  assert (finishedLength : finished vardef_0__solve_length=Z.of_nat len).
  { rewrite others by congruence. rewrite lookupDifferent by congruence. exact lengthEq. }
  rewrite finishedLength,previousEq. rewrite exec_bind.
  pose proof (integerWrite_execution arraydef_0__poly state (fillValues len values 0 (ordinaryValue values)) len
    (previousValue values len) ltac:(congruence) ltac:(rewrite fillValues_length; lia)) as appended.
  cbn [intValue intValues] in appended. rewrite appended. cbn [optionBind fst snd exec].
  assert (increment : coerceInt (Z.of_nat len+1) 64=Z.of_nat (S len)).
  { rewrite coerce64_small by (unfold koxiaModulus in lenBound; lia). lia. }
  rewrite increment. exists (update finished vardef_0__solve_length (Z.of_nat (S len))).
  split; [reflexivity|]. split; [apply lookupSame|]. intros name notValue notPrevious notLength.
  rewrite lookupDifferent by congruence. rewrite others by assumption. rewrite lookupDifferent by congruence. reflexivity.
Qed.
Theorem specialEventAction_execution len nums state values :
  nums vardef_0__solve_length=Z.of_nat len -> (len<=length values)%nat -> tableCanonical values ->
  exists final,
    exec (specialEventAction len nums) (withArray state arraydef_0__poly values)=
      Some (final,withArray state arraydef_0__poly (specialBuffer values len)) /\
    final vardef_0__solve_length=Z.of_nat len /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous -> final name=nums name).
Proof.
  intros lengthEq room canonical. unfold specialEventAction.
  destruct (specialAction_execution len 0 len state values (update nums vardef_0__solve_previous 0) eq_refl room canonical)
    as [final [execution others]]. cbn [fillValues] in execution.
  exists final. split; [exact execution|]. split.
  - rewrite others by congruence. rewrite lookupDifferent by congruence. exact lengthEq.
  - intros name notValue notPrevious. rewrite others by exact notValue. rewrite lookupDifferent by congruence. reflexivity.
Qed.
Definition eventBuffer (event : bool) values len := if event then specialBuffer values len else ordinaryBuffer values len.
Definition eventLength (event : bool) len := if event then len else S len.
Theorem leafEventAction_execution start index len nums state values (event : bool) :
  nums vardef_0__solve_length=Z.of_nat len ->
  (start+index+1<length (memory state arraydef_0__prefix))%nat ->
  nth (start+index+1) (memory state arraydef_0__prefix) 0-nth (start+index) (memory state arraydef_0__prefix) 0=(if event then 1 else 0) ->
  (S len<=length values)%nat -> Z.of_nat len<koxiaModulus -> tableCanonical values ->
  exists final,
    exec (leafEventAction start index len nums) (withArray state arraydef_0__poly values)=
      Some (final,withArray state arraydef_0__poly (eventBuffer event values len)) /\
    final vardef_0__solve_length=Z.of_nat (eventLength event len) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous -> name<>vardef_0__solve_length -> name<>vardef_0__solve_flag -> final name=nums name).
Proof.
  intros lengthEq prefixRoom flagEq room lenBound canonical.
  unfold leafEventAction,tableRead. cbn [bind].
  assert (nextRoom : (start+index+1<length (memory (withArray state arraydef_0__poly values) arraydef_0__prefix))%nat)
    by (rewrite withArray_preserve_other by congruence; exact prefixRoom).
  assert (currentRoom : (start+index<length (memory (withArray state arraydef_0__poly values) arraydef_0__prefix))%nat)
    by (rewrite withArray_preserve_other by congruence; lia).
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    (withArray state arraydef_0__poly values) arraydef_0__prefix (start+index+1) 0) by exact nextRoom.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    (withArray state arraydef_0__poly values) arraydef_0__prefix (start+index) 0) by exact currentRoom.
  rewrite !withArray_preserve_other by congruence. cbn [arrayType environment1] in *. rewrite flagEq.
  destruct event; cbn [eventBuffer eventLength].
  - rewrite coerce64_small by lia. rewrite bool_decide_false by lia.
    destruct (specialEventAction_execution len (update nums vardef_0__solve_flag 1) state values
      ltac:(rewrite lookupDifferent by congruence; exact lengthEq) ltac:(lia) canonical) as [final [execution [finalLength others]]].
    exists final. split; [exact execution|]. split; [exact finalLength|].
    intros name notValue notPrevious notLength notFlag. rewrite others by assumption. rewrite lookupDifferent by congruence. reflexivity.
  - rewrite coerce64_small by lia. rewrite bool_decide_true by lia.
    destruct (ordinaryEventAction_execution len (update nums vardef_0__solve_flag 0) state values
      ltac:(rewrite lookupDifferent by congruence; exact lengthEq) room lenBound canonical) as [final [execution [finalLength others]]].
    exists final. split; [exact execution|]. split; [exact finalLength|].
    intros name notValue notPrevious notLength notFlag. rewrite others by assumption. rewrite lookupDifferent by congruence. reflexivity.
Qed.
