From CoqCP Require Import Options Imperative Execution KoxiaPolynomial KoxiaModular KoxiaIntegers
  KoxiaPolynomialBuffers KoxiaArrays KoxiaTables KoxiaTableLoops KoxiaArrayLoops SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.

Definition ordinaryCoefficientBody (x : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
            (liftToWithinLoop ((binder_2 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
            fun _ => (liftToWithinLoop (binder_2 >>= fun x => ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
            fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_previous) x)) >>=
            fun _ => Done _ _ _ tt
          )).

Definition specialCoefficientBody (x : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
            (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
            fun _ => ((liftToWithinLoop ((addInt 64 binder_2 (Done _ _ _ 1%Z)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
              (liftToWithinLoop (((addInt 64 binder_2 (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
              fun _ => Done _ _ _ tt
            ) else (
              Done _ _ _ tt
            )) >>=
            fun _ => (liftToWithinLoop (binder_2 >>= fun x => ((modIntUnsigned (addInt 64 (binder_2 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
            fun _ => Done _ _ _ tt
          )).

Definition ordinaryNums (nums : varsfuncdef_0__solve -> Z) value := update (update nums vardef_0__solve_value value) vardef_0__solve_previous value.
Definition ordinaryStep index previous :=
  tableRead arraydef_0__poly (Z.of_nat index) >>= fun value =>
  tableWrite arraydef_0__poly (Z.of_nat index) (coerceInt (value+previous) 64 mod koxiaModulus) >>= fun _ =>
  Done _ _ _ value.
Fixpoint ordinaryAction fuel total nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__solve -> Z) :=
  match fuel with O => Done _ _ _ nums | S fuel =>
    ordinaryStep (total-fuel-1) (nums vardef_0__solve_previous) >>= fun value =>
    ordinaryAction fuel total (ordinaryNums nums value)
  end.
Lemma ordinaryCoefficientNormalized b nums total remaining continuation : (remaining<total)%nat ->
  eliminateLocalVariables b nums (ordinaryCoefficientBody (Z.of_nat total) remaining >>= continuation)=
  ordinaryStep (total-remaining-1) (nums vardef_0__solve_previous) >>= fun value =>
  eliminateLocalVariables b (ordinaryNums nums value) (continuation KeepGoing).
Proof.
  intro bound. unfold ordinaryCoefficientBody,numberLocalGet,numberLocalSet,retrieve,store,addInt,modIntUnsigned.
  normalize_table_loop.
  assert (indexId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite indexId. unfold ordinaryStep,tableRead,tableWrite. cbn [bind].
  apply f_equal. apply functional_extensionality. intro value. normalize_table_loop.
  rewrite lookupSame. rewrite lookupDifferent by congruence.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  reflexivity.
Qed.
Theorem ordinaryLoopNormalized b nums fuel total continuation : (fuel<=total)%nat ->
  eliminateLocalVariables b nums (loop fuel (ordinaryCoefficientBody (Z.of_nat total)) >>= continuation)=
  ordinaryAction fuel total nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|]. intro bound.
  rewrite loop_S,<-bindAssoc,ordinaryCoefficientNormalized by lia. cbn [ordinaryAction].
  rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intro value. apply IH. lia.
Qed.
Lemma ordinaryStep_execution state values index previous : (index<length values)%nat ->
  0<=nth index values 0<koxiaModulus -> 0<=previous<koxiaModulus ->
  exec (ordinaryStep index previous) (withArray state arraydef_0__poly values)=
  Some (nth index values 0,withArray state arraydef_0__poly
    (<[index:=(nth index values 0+previous) mod koxiaModulus]>values)).
Proof.
  intros room currentRange previousRange. unfold ordinaryStep,tableRead,tableWrite. cbn [bind].
  rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state arraydef_0__poly values index 0) by exact room.
  rewrite residue_sum_coerce by assumption. rewrite execStoreArray by exact room. reflexivity.
Qed.
Lemma previousValue_canonical values count : (count<=length values)%nat -> tableCanonical values ->
  0<=previousValue values count<koxiaModulus.
Proof.
  intros room canonical. destruct count as [|count]; cbn [previousValue].
  - pose proof modulus_positive; lia.
  - apply tableCanonical_nth; [exact canonical|lia].
Qed.
Lemma ordinaryNums_other nums value name : name<>vardef_0__solve_value -> name<>vardef_0__solve_previous ->
  ordinaryNums nums value name=nums name.
Proof. intros. unfold ordinaryNums. rewrite !lookupDifferent by congruence. reflexivity. Qed.
Theorem ordinaryAction_execution fuel count total state values nums :
  (count+fuel=total)%nat -> (total<=length values)%nat -> tableCanonical values ->
  nums vardef_0__solve_previous=previousValue values count ->
  exists final,
    exec (ordinaryAction fuel total nums)
      (withArray state arraydef_0__poly (fillValues count values 0 (ordinaryValue values)))=
    Some (final,withArray state arraydef_0__poly (fillValues total values 0 (ordinaryValue values))) /\
    final vardef_0__solve_previous=previousValue values total /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in count,nums |- *.
  - intros countFuel room canonical previousEq. assert (count=total) by lia. subst count.
    exists nums. split; [reflexivity|]. split; [exact previousEq|intros; reflexivity].
  - intros countFuel room canonical previousEq. cbn [ordinaryAction].
    replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,ordinaryStep_execution.
    2: rewrite fillValues_length; lia.
    2: apply tableCanonical_nth; [apply fillValues_canonical; [exact canonical|intros; unfold ordinaryValue; apply residue_bounds]|rewrite fillValues_length; lia].
    2: rewrite previousEq; apply previousValue_canonical; [lia|exact canonical].
    cbn [optionBind fst snd]. rewrite fillValues_lookup,bool_decide_false by lia.
    assert (valueEq : nth count values 0+nums vardef_0__solve_previous=
      nth count values 0+(if Nat.eqb count 0 then 0 else nth (count-1) values 0)).
    { rewrite previousEq. destruct count as [|count]; cbn [previousValue Nat.eqb].
      - reflexivity.
      - replace (S count-1)%nat with count by lia. reflexivity. }
    rewrite valueEq. fold (ordinaryValue values count).
    destruct (IH (S count) (ordinaryNums nums (nth count values 0)) ltac:(lia) room canonical
      ltac:(unfold ordinaryNums; rewrite lookupSame; reflexivity)) as [final [execution [finalPrevious others]]].
    exists final. split.
    + cbn [fillValues Nat.add] in execution. exact execution.
    + split; [exact finalPrevious|]. intros name notValue notPrevious.
      rewrite others by assumption. apply ordinaryNums_other; assumption.
Qed.

Definition specialStep index len :=
  (if bool_decide ((S index<len)%nat) then tableRead arraydef_0__poly (Z.of_nat (S index)) else Done _ _ _ 0) >>= fun next =>
  tableRead arraydef_0__poly (Z.of_nat index) >>= fun value =>
  tableWrite arraydef_0__poly (Z.of_nat index) (coerceInt (value+next) 64 mod koxiaModulus) >>= fun _ =>
  Done _ _ _ next.
Fixpoint specialAction fuel total nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__solve -> Z) :=
  match fuel with O => Done _ _ _ nums | S fuel =>
    specialStep (total-fuel-1) total >>= fun value =>
    specialAction fuel total (update nums vardef_0__solve_value value)
  end.
Lemma specialCoefficientNormalized b nums total remaining continuation :
  nums vardef_0__solve_length=Z.of_nat total -> (remaining<total)%nat -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (specialCoefficientBody (Z.of_nat total) remaining >>= continuation)=
  specialStep (total-remaining-1) total >>= fun value =>
  eliminateLocalVariables b (update nums vardef_0__solve_value value) (continuation KeepGoing).
Proof.
  intros lengthEq bound totalBound. unfold koxiaModulus in totalBound.
  unfold specialCoefficientBody,numberLocalGet,numberLocalSet,retrieve,store,addInt,modIntUnsigned.
  normalize_table_loop.
  assert (indexId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite indexId. rewrite lookupDifferent by congruence. rewrite lengthEq.
  rewrite (coerce64_small (Z.of_nat (total-remaining-1)+1)) by lia.
  replace (Z.of_nat (total-remaining-1)+1) with (Z.of_nat (S (total-remaining-1))) by lia.
  assert (guard : bool_decide (Z.of_nat (S (total-remaining-1))<Z.of_nat total)=
    bool_decide ((S (total-remaining-1)<total)%nat)).
  { apply bool_decide_ext. lia. }
  rewrite guard. unfold specialStep,tableRead,tableWrite. cbn [bind].
  destruct (bool_decide ((S (total-remaining-1)<total)%nat)) eqn:next.
  - normalize_table_loop.
    apply f_equal. apply functional_extensionality. intro value. normalize_table_loop.
    apply f_equal. apply functional_extensionality. intro current. normalize_table_loop.
    rewrite lookupSame. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
    rewrite updateSame. reflexivity.
  - normalize_table_loop. apply f_equal. apply functional_extensionality. intro current. normalize_table_loop.
    rewrite lookupSame. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop. reflexivity.
Qed.
Theorem specialLoopNormalized b nums fuel total continuation :
  nums vardef_0__solve_length=Z.of_nat total -> (fuel<=total)%nat -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (loop fuel (specialCoefficientBody (Z.of_nat total)) >>= continuation)=
  specialAction fuel total nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|]. intros lengthEq fuelBound totalBound.
  rewrite loop_S,<-bindAssoc,specialCoefficientNormalized by (try assumption; lia). cbn [specialAction].
  rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intro value.
  apply IH; [rewrite lookupDifferent by congruence; exact lengthEq|lia|exact totalBound].
Qed.

Definition specialNext values total index := if bool_decide ((S index<total)%nat) then nth (S index) values 0 else 0.
Lemma specialStep_execution state values index total : (index<total<=length values)%nat -> tableCanonical values ->
  exec (specialStep index total) (withArray state arraydef_0__poly values)=
  Some (specialNext values total index,withArray state arraydef_0__poly (<[index:=specialValue values total index]>values)).
Proof.
  intros room canonical. assert (currentRoom : (index<length values)%nat) by lia.
  unfold specialStep,specialNext,specialValue,tableRead,tableWrite. cbn [bind].
  destruct (bool_decide ((S index<total)%nat)) eqn:next.
  - apply bool_decide_eq_true in next. cbn [bind].
    assert (nextRoom : (S index<length values)%nat) by lia.
    rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state arraydef_0__poly values (S index) 0) by exact nextRoom.
    rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state arraydef_0__poly values index 0) by exact currentRoom.
    cbn [arrayType environment1] in *.
    pose proof (tableCanonical_nth values index canonical currentRoom) as currentRange.
    pose proof (tableCanonical_nth values (S index) canonical nextRoom) as nextRange.
    rewrite (residue_sum_coerce _ _ currentRange nextRange).
    rewrite execStoreArray by exact currentRoom. reflexivity.
  - cbn [bind].
    rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state arraydef_0__poly values index 0) by exact currentRoom.
    cbn [arrayType environment1] in *.
    rewrite residue_sum_coerce.
    2: apply tableCanonical_nth; [exact canonical|exact currentRoom].
    2: pose proof modulus_positive; lia.
    rewrite execStoreArray by exact currentRoom. reflexivity.
Qed.
Lemma specialValue_future count values total index : (count<=index)%nat -> (count<=length values)%nat ->
  specialValue (fillValues count values 0 (specialValue values total)) total index=specialValue values total index.
Proof.
  intros outside room. unfold specialValue at 1 3.
  destruct (bool_decide ((S index<total)%nat)); rewrite !fillValues_lookup,!bool_decide_false by lia; reflexivity.
Qed.
Theorem specialAction_execution fuel count total state values nums :
  (count+fuel=total)%nat -> (total<=length values)%nat -> tableCanonical values ->
  exists final,
    exec (specialAction fuel total nums)
      (withArray state arraydef_0__poly (fillValues count values 0 (specialValue values total)))=
    Some (final,withArray state arraydef_0__poly (fillValues total values 0 (specialValue values total))) /\
    (forall name, name<>vardef_0__solve_value -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in count,nums |- *.
  - intros countFuel room canonical. assert (count=total) by lia. subst count.
    exists nums. split; [reflexivity|intros; reflexivity].
  - intros countFuel room canonical. cbn [specialAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,specialStep_execution.
    2: rewrite fillValues_length; lia.
    2: apply fillValues_canonical; [exact canonical|intros; unfold specialValue; apply residue_bounds].
    cbn [optionBind fst snd]. rewrite specialValue_future by lia.
    destruct (IH (S count) (update nums vardef_0__solve_value
      (specialNext (fillValues count values 0 (specialValue values total)) total count))
      ltac:(lia) room canonical) as [final [execution others]].
    exists final. split.
    + cbn [fillValues Nat.add] in execution. exact execution.
    + intros name notValue. rewrite others by exact notValue. rewrite lookupDifferent by congruence. reflexivity.
Qed.
