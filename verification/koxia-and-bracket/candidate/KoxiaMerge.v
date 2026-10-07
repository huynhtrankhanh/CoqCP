From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaPolynomial KoxiaModular KoxiaIntegers KoxiaArrays KoxiaTables KoxiaTableLoops KoxiaArrayLoops KoxiaPolynomialBuffers KoxiaBufferSplit.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition mergeCoefficientBody (x : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
        (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
        fun _ => ((liftToWithinLoop (binder_1 >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
          (liftToWithinLoop ((binder_1 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => ((liftToWithinLoop (binder_1 >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
          (liftToWithinLoop ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__arena) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value) x)) >>=
          fun _ => Done _ _ _ tt
        ) else (
          Done _ _ _ tt
        )) >>=
        fun _ => (liftToWithinLoop (binder_1 >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_value)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y)) >>=
        fun _ => Done _ _ _ tt
      )).

Definition mergeStep index len base savedLen :=
  (if bool_decide ((index<len)%nat) then tableRead arraydef_0__poly (Z.of_nat index) else Done _ _ _ 0) >>= fun lowValue =>
  (if bool_decide ((index<savedLen)%nat) then
    tableRead arraydef_0__arena (Z.of_nat (base+index)) >>= fun highValue =>
    Done _ _ _ (coerceInt (lowValue+highValue) 64 mod koxiaModulus)
   else Done _ _ _ lowValue) >>= fun value =>
  tableWrite arraydef_0__poly (Z.of_nat index) value >>= fun _ => Done _ _ _ value.
Fixpoint mergeAction fuel total len base savedLen nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__solve -> Z) :=
  match fuel with O => Done _ _ _ nums | S fuel =>
    mergeStep (total-fuel-1) len base savedLen >>= fun value =>
    mergeAction fuel total len base savedLen (update nums vardef_0__solve_value value)
  end.
Lemma mergeCoefficientNormalized b nums total remaining len base savedLen continuation :
  nums vardef_0__solve_length=Z.of_nat len -> nums vardef_0__solve_base=Z.of_nat base ->
  nums vardef_0__solve_saved=Z.of_nat savedLen -> (remaining<total)%nat ->
  Z.of_nat (base+total)<18446744073709551616 ->
  eliminateLocalVariables b nums (mergeCoefficientBody (Z.of_nat total) remaining >>= continuation)=
  mergeStep (total-remaining-1) len base savedLen >>= fun value =>
    eliminateLocalVariables b (update nums vardef_0__solve_value value) (continuation KeepGoing).
Proof.
  intros lenEq baseEq savedEq indexBound addressFit.
  unfold mergeCoefficientBody,numberLocalGet,numberLocalSet,retrieve,store,addInt,modIntUnsigned.
  normalize_table_loop.
  assert (indexId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite indexId,lookupDifferent by congruence. rewrite lenEq.
  assert (lowGuard : bool_decide (Z.of_nat (total-remaining-1)<Z.of_nat len)=
    bool_decide ((total-remaining-1<len)%nat)) by (apply bool_decide_ext; lia).
  rewrite lowGuard. unfold mergeStep,tableRead,tableWrite. cbn [bind].
  cbn [withLocalVariablesReturnValue withArraysReturnValue] in *.
  destruct (bool_decide ((total-remaining-1<len)%nat)) eqn:lowPresent.
  - normalize_table_loop. apply f_equal. apply functional_extensionality. intro lowValue.
    normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite savedEq.
    assert (highGuard : bool_decide (Z.of_nat (total-remaining-1)<Z.of_nat savedLen)=
      bool_decide ((total-remaining-1<savedLen)%nat)) by (apply bool_decide_ext; lia).
    rewrite highGuard. destruct (bool_decide ((total-remaining-1<savedLen)%nat)) eqn:highPresent.
    + normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite baseEq.
      rewrite (coerce64_small (Z.of_nat base+Z.of_nat (total-remaining-1))) by lia.
      replace (Z.of_nat base+Z.of_nat (total-remaining-1)) with (Z.of_nat (base+(total-remaining-1))) by lia.
      apply f_equal. apply functional_extensionality. intro highValue. normalize_table_loop.
      rewrite !lookupSame. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
      rewrite !updateSame. reflexivity.
    + normalize_table_loop. rewrite lookupSame. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop. rewrite ?updateSame. reflexivity.
  - normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite savedEq.
    assert (highGuard : bool_decide (Z.of_nat (total-remaining-1)<Z.of_nat savedLen)=
      bool_decide ((total-remaining-1<savedLen)%nat)) by (apply bool_decide_ext; lia).
    rewrite highGuard. destruct (bool_decide ((total-remaining-1<savedLen)%nat)) eqn:highPresent.
    + normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite baseEq.
      rewrite (coerce64_small (Z.of_nat base+Z.of_nat (total-remaining-1))) by lia.
      replace (Z.of_nat base+Z.of_nat (total-remaining-1)) with (Z.of_nat (base+(total-remaining-1))) by lia.
      apply f_equal. apply functional_extensionality. intro highValue. normalize_table_loop.
      rewrite !lookupSame. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
      rewrite !updateSame. reflexivity.
    + normalize_table_loop. rewrite lookupSame. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop. rewrite ?updateSame. reflexivity.
Qed.
Theorem mergeLoopNormalized b nums fuel total len base savedLen continuation :
  nums vardef_0__solve_length=Z.of_nat len -> nums vardef_0__solve_base=Z.of_nat base ->
  nums vardef_0__solve_saved=Z.of_nat savedLen -> (fuel<=total)%nat ->
  Z.of_nat (base+total)<18446744073709551616 ->
  eliminateLocalVariables b nums (loop fuel (mergeCoefficientBody (Z.of_nat total)) >>= continuation)=
  mergeAction fuel total len base savedLen nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|].
  intros lenEq baseEq savedEq fuelBound addressFit.
  rewrite loop_S,<-bindAssoc,mergeCoefficientNormalized with (len:=len) (base:=base) (savedLen:=savedLen) by (try assumption; lia).
  cbn [mergeAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intro value.
  apply IH; try rewrite lookupDifferent by congruence; try assumption; lia.
Qed.

Lemma mergeValue_range values len saved savedLen index :
  0<=mergeValue values len saved savedLen index<koxiaModulus.
Proof. unfold mergeValue. apply residue_bounds. Qed.
Lemma activeCoefficient_canonical values len j : (len<=length values)%nat -> tableCanonical values ->
  0<=activeCoefficient values len j<koxiaModulus.
Proof.
  intros room canonical. unfold activeCoefficient. destruct (bool_decide (0<=j<Z.of_nat len)) eqn:inside.
  - apply bool_decide_eq_true in inside. apply tableCanonical_nth; [exact canonical|lia].
  - pose proof modulus_positive; lia.
Qed.
Lemma skipn_nth_Z (values : list Z) base index : nth index (skipn base values) 0=nth (base+index) values 0.
Proof.
  induction base as [|base IH] in values |- *; [reflexivity|].
  destruct values as [|value values]; cbn [skipn]; [destruct index; reflexivity|].
  cbn [Nat.add nth]. apply IH.
Qed.
Lemma mergeStep_execution state values index len base savedLen :
  (index<length values)%nat -> (len<=length values)%nat ->
  (base+savedLen<=length (memory state arraydef_0__arena))%nat ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__arena) ->
  exec (mergeStep index len base savedLen) (withArray state arraydef_0__poly values)=
  Some (mergeValue values len (skipn base (memory state arraydef_0__arena)) savedLen index,
    withArray state arraydef_0__poly
      (<[index:=mergeValue values len (skipn base (memory state arraydef_0__arena)) savedLen index]>values)).
Proof.
  intros indexRoom lenRoom arenaRoom canonical arenaCanonical.
  assert (arenaUnchanged : memory (withArray state arraydef_0__poly values) arraydef_0__arena=memory state arraydef_0__arena)
    by (apply withArray_preserve_other; congruence).
  unfold mergeStep,tableRead,tableWrite. cbn [bind].
  unfold mergeValue. rewrite !activeCoefficient_nat.
  destruct (bool_decide ((index<len)%nat)) eqn:lowPresent.
  - apply bool_decide_eq_true in lowPresent. cbn [bind].
    rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state arraydef_0__poly values index 0) by exact indexRoom.
    cbn [arrayType environment1] in *.
    destruct (bool_decide ((index<savedLen)%nat)) eqn:highPresent.
    + apply bool_decide_eq_true in highPresent. cbn [bind].
      assert (arenaIndexRoom : (base+index<length (memory state arraydef_0__arena))%nat) by lia.
      rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
        (withArray state arraydef_0__poly values) arraydef_0__arena (base+index) 0)
        by (rewrite withArray_preserve_other by congruence; exact arenaIndexRoom).
      rewrite withArray_preserve_other by congruence. rewrite skipn_nth_Z,residue_sum_coerce.
      2: apply tableCanonical_nth; assumption.
      2: apply tableCanonical_nth; [exact arenaCanonical|exact arenaIndexRoom].
      rewrite execStoreArray by exact indexRoom. reflexivity.
    + cbn [bind]. rewrite Z.add_0_r,Z.mod_small by (apply tableCanonical_nth; assumption).
      rewrite execStoreArray by exact indexRoom. reflexivity.
  - cbn [bind]. destruct (bool_decide ((index<savedLen)%nat)) eqn:highPresent.
    + apply bool_decide_eq_true in highPresent. cbn [bind].
      assert (arenaIndexRoom : (base+index<length (memory state arraydef_0__arena))%nat) by lia.
      rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
        (withArray state arraydef_0__poly values) arraydef_0__arena (base+index) 0)
        by (rewrite withArray_preserve_other by congruence; exact arenaIndexRoom).
      cbn [arrayType environment1] in *. rewrite withArray_preserve_other by congruence. rewrite skipn_nth_Z,residue_sum_coerce.
      2: pose proof modulus_positive; lia.
      2: apply tableCanonical_nth; [exact arenaCanonical|exact arenaIndexRoom].
      rewrite execStoreArray by exact indexRoom. reflexivity.
    + cbn [bind]. rewrite Z.add_0_l,Z.mod_0_l by (pose proof modulus_positive; lia).
      rewrite execStoreArray by exact indexRoom. reflexivity.
Qed.
Lemma mergeValue_future count values len saved savedLen index : (count<=index)%nat -> (count<=length values)%nat ->
  mergeValue (fillValues count values 0 (mergeValue values len saved savedLen)) len saved savedLen index=
  mergeValue values len saved savedLen index.
Proof.
  intros outside room. unfold mergeValue. rewrite !activeCoefficient_nat.
  destruct (bool_decide ((index<len)%nat)); [rewrite fillValues_lookup,bool_decide_false by lia|]; reflexivity.
Qed.
Theorem mergeAction_execution fuel count total len base savedLen state values nums :
  (count+fuel=total)%nat -> (total<=length values)%nat -> (len<=total)%nat ->
  (base+savedLen<=length (memory state arraydef_0__arena))%nat ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__arena) ->
  exists final,
    exec (mergeAction fuel total len base savedLen nums)
      (withArray state arraydef_0__poly
        (fillValues count values 0 (mergeValue values len (skipn base (memory state arraydef_0__arena)) savedLen)))=
    Some (final,withArray state arraydef_0__poly
      (fillValues total values 0 (mergeValue values len (skipn base (memory state arraydef_0__arena)) savedLen))) /\
    (forall name, name<>vardef_0__solve_value -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in count,nums |- *.
  - intros countFuel room lenBound arenaRoom canonical arenaCanonical.
    assert (count=total) by lia. subst count. exists nums. split; [reflexivity|intros; reflexivity].
  - intros countFuel room lenBound arenaRoom canonical arenaCanonical.
    cbn [mergeAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,mergeStep_execution.
    2,3: rewrite fillValues_length; lia.
    2: exact arenaRoom.
    2: apply fillValues_canonical; [exact canonical|intros; apply mergeValue_range].
    2: exact arenaCanonical.
    cbn [optionBind fst snd]. rewrite mergeValue_future by lia.
    destruct (IH (S count) (update nums vardef_0__solve_value
      (mergeValue values len (skipn base (memory state arraydef_0__arena)) savedLen count))
      ltac:(lia) room lenBound arenaRoom canonical arenaCanonical) as [final [execution others]].
    exists final. split.
    + cbn [fillValues Nat.add] in execution. exact execution.
    + intros name notValue. rewrite others by exact notValue. rewrite lookupDifferent by congruence. reflexivity.
Qed.

Theorem generated_merge_loop_execution b nums len base savedLen state values continuation :
  nums vardef_0__solve_length=Z.of_nat len -> nums vardef_0__solve_base=Z.of_nat base ->
  nums vardef_0__solve_saved=Z.of_nat savedLen ->
  (Nat.max len savedLen<=length values)%nat ->
  (base+savedLen<=length (memory state arraydef_0__arena))%nat ->
  Z.of_nat (base+Nat.max len savedLen)<18446744073709551616 ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__arena) ->
  exists final,
    exec (eliminateLocalVariables b nums (loop (Nat.max len savedLen)
      (mergeCoefficientBody (Z.of_nat (Nat.max len savedLen))) >>= continuation))
      (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation tt))
      (withArray state arraydef_0__poly
        (mergeBuffer values len (skipn base (memory state arraydef_0__arena)) savedLen)) /\
    (forall name, name<>vardef_0__solve_value -> final name=nums name).
Proof.
  intros lenEq baseEq savedEq room arenaRoom addressFit canonical arenaCanonical.
  rewrite mergeLoopNormalized with (len:=len) (base:=base) (savedLen:=savedLen) by (try assumption; lia).
  rewrite exec_bind.
  destruct (mergeAction_execution (Nat.max len savedLen) 0 (Nat.max len savedLen) len base savedLen state values nums
    ltac:(lia) room ltac:(lia) arenaRoom canonical arenaCanonical) as [final [execution others]].
  cbn [fillValues] in execution. rewrite execution. cbn [optionBind fst snd].
  exists final. split; [reflexivity|exact others].
Qed.
