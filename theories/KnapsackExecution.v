From CoqCP Require Import Options Imperative Execution Knapsack KnapsackCode KnapsackTable.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
From Coq Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.
Create HintDb local_maps.
#[local] Hint Rewrite @lookupSame @lookupDifferent using discriminate : local_maps.

Definition cellLocals row cap limit :=
  update (update (update (fun _ : varsfuncdef_0__cell => 0%Z) vardef_0__cell_row row)
    vardef_0__cell_cap cap) vardef_0__cell_limit limit.
Definition solveAction count limit :=
  arrayLoop (Z.to_nat count) (fun row =>
    arrayLoop (Z.to_nat (coerceInt (limit + 1) 64)) (fun cap =>
      funcdef_0__cell (fun _ => false)
        (cellLocals (count - Z.of_nat row - 1) (coerceInt (limit + 1) 64 - Z.of_nat cap - 1) limit))).

Lemma solveNormalized b nums :
  funcdef_0__solve b nums =
  Dispatch _ _ _ (Retrieve _ _ arraydef_0__n 0)
    (fun count => solveAction count (nums vardef_0__solve_limit)).
Proof.
  unfold funcdef_0__solve, funcdef_0__solve_body.
  cbn [bind retrieve]. rewrite pushDispatch. f_equal.
  apply functional_extensionality. intro count.
  unfold solveAction.
  match goal with |- _ = arrayLoop _ ?code =>
    transitivity (arrayLoop (Z.to_nat count) code >>= fun _ => Done _ _ _ tt);
    [eapply (eliminate_arrayLoop b nums _ _ code _ (fun _ => Done _ _ _ tt)) | apply bind_unit_identity]
  end.
  Unshelve.
  intros row continuation. cbn beta.
    rewrite dropWithinLoopLiftToWithinLoop.
    rewrite <- !bindAssoc.
    unfold addInt, numberLocalGet.
    cbn [bind]. rewrite pushNumberGet.
    cbn [bind].
    match goal with |- _ = arrayLoop ?n ?code >>= ?next =>
      transitivity (arrayLoop n code >>= fun _ => eliminateLocalVariables b nums ((Done _ _ _ KeepGoing) >>= continuation));
      [eapply (eliminate_arrayLoop b nums _ _ code _ (fun _ => Done _ _ _ KeepGoing >>= continuation)) | reflexivity]
    end.
    Unshelve.
    intros cap next. cbn beta.
      rewrite dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc.
      cbn [bind]. unfold numberLocalGet.
      rewrite pushNumberGet.
      cbn [bind]. rewrite eliminateLift.
      cbn [bind]. reflexivity.
Qed.

Definition readArray name index :=
  Dispatch (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue _
    (Retrieve _ _ name index) (fun value => Done _ _ _ value).
Definition writeArray name index value :=
  Dispatch (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue _
    (Store _ _ name index value) (fun _ => Done _ _ _ tt).
Definition previousIndex row cap limit := coerceInt (coerceInt (row * coerceInt (limit + 1) 64) 64 + cap) 64.
Definition nextIndex row cap limit := previousIndex (coerceInt (row + 1) 64) cap limit.
Definition cellAction row cap limit :=
  readArray arraydef_0__weights row >>= fun w =>
  readArray arraydef_0__values row >>= fun v =>
  readArray arraydef_0__dp (previousIndex row cap limit) >>= fun best =>
  if negb (bool_decide (cap < coerceInt w 64)) then
    readArray arraydef_0__dp (previousIndex row (coerceInt (cap - coerceInt w 64) 64) limit) >>= fun previous =>
    let withItem := coerceInt (previous + coerceInt v 64) 64 in
    writeArray arraydef_0__dp (nextIndex row cap limit)
      (if bool_decide (best < withItem) then withItem else best)
  else writeArray arraydef_0__dp (nextIndex row cap limit) best.

Lemma cellNormalized row cap limit :
  funcdef_0__cell (fun _ => false) (cellLocals row cap limit) = cellAction row cap limit.
Proof.
  unfold funcdef_0__cell, funcdef_0__cell_body, cellLocals, cellAction, previousIndex, nextIndex,
    readArray, writeArray, addInt, subInt, multInt, retrieve, store,
    numberLocalGet, numberLocalSet.
  cbn [bind].
  repeat progress (autorewrite with advance_program local_maps; simpl).
  f_equal. apply functional_extensionality. intro weight.
  repeat progress (autorewrite with advance_program local_maps; simpl).
  f_equal. apply functional_extensionality. intro value.
  repeat progress (autorewrite with advance_program local_maps; simpl).
  f_equal. apply functional_extensionality. intro best.
  repeat progress (autorewrite with advance_program local_maps; simpl).
  destruct (bool_decide (cap < coerceInt weight 64)); simpl.
  - repeat progress (autorewrite with advance_program local_maps; simpl).
    reflexivity.
  - repeat progress (autorewrite with advance_program local_maps; simpl).
    f_equal. apply functional_extensionality. intro previous.
    repeat progress (autorewrite with advance_program local_maps; simpl).
    destruct (bool_decide (best < coerceInt (previous + coerceInt value 64) 64));
      repeat progress (autorewrite with advance_program local_maps; simpl); reflexivity.
Qed.

Lemma coerce_nat64 value (h : (value < 2^64)%nat) : coerceInt (Z.of_nat value) 64 = Z.of_nat value.
Proof.
  unfold coerceInt. apply Z.mod_small. split; [lia |].
  assert (power : Z.of_nat (2^64)%nat = (2^64)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  rewrite <- power. lia.
Qed.

Lemma previousIndex_nat row cap limit
  (hSize : ((row + 1) * (limit + 1) < 2^64)%nat)
  (hCap : (cap <= limit)%nat) :
  previousIndex (Z.of_nat row) (Z.of_nat cap) (Z.of_nat limit) = Z.of_nat (row * (limit + 1) + cap).
Proof.
  unfold previousIndex.
  replace (Z.of_nat limit + 1)%Z with (Z.of_nat (limit + 1)) by lia.
  rewrite coerce_nat64; [| nia].
  rewrite <- Nat2Z.inj_mul. rewrite coerce_nat64; [| nia].
  rewrite <- Nat2Z.inj_add. apply coerce_nat64. nia.
Qed.

Lemma nextIndex_nat row cap limit
  (hSize : ((row + 2) * (limit + 1) < 2^64)%nat)
  (hCap : (cap <= limit)%nat) :
  nextIndex (Z.of_nat row) (Z.of_nat cap) (Z.of_nat limit) = Z.of_nat (S row * (limit + 1) + cap).
Proof.
  unfold nextIndex. replace (Z.of_nat row + 1)%Z with (Z.of_nat (row + 1)) by lia.
  rewrite coerce_nat64; [| nia]. rewrite Nat.add_1_r. apply previousIndex_nat; nia.
Qed.

Definition tableMachine items limit top message input buffer :=
  {| memory := knapsackArrays items (table items limit top) message input buffer;
     stdin := []; stdout := [] |}.


Lemma execRead {R} name index zero
  (next : arrayType _ environment2 name -> Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue R)
  s (h : (index < length (memory s name))%nat) :
  exec (readArray name (Z.of_nat index) >>= next) s =
  exec (next (nth index (memory s name) zero)) s.
Proof.
  unfold readArray. cbn [bind exec step optionBind]. rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length (memory s name)))) as [bound | bad]; [| lia].
  rewrite (nth_lt_default _ _ _ zero). reflexivity.
Qed.
Lemma execWrite name index value s
  (h : (index < length (memory s name))%nat) :
  exec (writeArray name (Z.of_nat index) value) s =
  Some (tt, withMemory s (modifyArray (memory s) name index value)).
Proof.
  unfold writeArray. cbn [bind exec step optionBind]. rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length (memory s name)))) as [bound | bad]; [reflexivity | lia].
Qed.

Lemma modify_knapsack_dp items dp message input buffer index value :
  modifyArray (knapsackArrays items dp message input buffer) arraydef_0__dp index value =
  knapsackArrays items (<[index := value]> dp) message input buffer.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.

Lemma writeTable items limit row cap message input buffer
  (hRow : (row < length items)%nat) (hCap : (cap <= limit)%nat) :
  exec (writeArray arraydef_0__dp (Z.of_nat (S row * (limit + 1) + cap))
    (Z.of_nat (knapsack (reverse (take (S row) items)) cap)))
    (tableMachine items limit (S row * (limit + 1) + cap) message input buffer) =
  Some (tt, tableMachine items limit (S (S row * (limit + 1) + cap)) message input buffer).
Proof.
  rewrite execWrite; [| cbn [tableMachine memory knapsackArrays]; rewrite table_length; unfold tableSize; nia].
  unfold tableMachine, withMemory. cbn [memory stdin stdout].
  rewrite modify_knapsack_dp, table_insert; [reflexivity | exact hRow | exact hCap].
Qed.

Lemma cellExecution items limit row cap message input buffer
  (hSize : (tableSize items limit < 2^64)%nat)
  (hRow : (row < length items)%nat) (hCap : (cap <= limit)%nat)
  (hWeights : forall item, In item items -> (fst item < 2^32)%nat)
  (hValues : forall item, In item items -> (snd item < 2^32)%nat)
  (hSum : (list_sum (map snd items) < 2^64)%nat) :
  exec (funcdef_0__cell (fun _ => false) (cellLocals (Z.of_nat row) (Z.of_nat cap) (Z.of_nat limit)))
    (tableMachine items limit (S row * (limit + 1) + cap) message input buffer) =
  Some (tt, tableMachine items limit (S (S row * (limit + 1) + cap)) message input buffer).
Proof.
  assert (inItem : In (nth row items (0%nat, 0%nat)) items) by (apply nth_In; lia).
  pose proof hWeights _ inItem as hw. pose proof hValues _ inItem as hv.
  assert (hWidth : ((row + 2) * (limit + 1) < 2^64)%nat) by (unfold tableSize in hSize; nia).
  rewrite cellNormalized. unfold cellAction, readArray, writeArray.
  rewrite previousIndex_nat; [| nia | exact hCap].
  rewrite nextIndex_nat; [| exact hWidth | exact hCap].
  rewrite (execRead arraydef_0__weights row 0%Z); [| cbn [tableMachine memory knapsackArrays]; rewrite length_map; lia].
  cbn [tableMachine memory knapsackArrays].
  change (nth row (map (fun item => Z.of_nat (fst item)) items) 0%Z) with
    (nth row (map (fun item => Z.of_nat (fst item)) items) (Z.of_nat (fst (0%nat, 0%nat)))).
  rewrite (map_nth (fun item : nat * nat => Z.of_nat (fst item)) items (0%nat, 0%nat) row).
  rewrite (execRead arraydef_0__values row 0%Z); [| cbn [tableMachine memory knapsackArrays]; rewrite length_map; lia].
  cbn [tableMachine memory knapsackArrays].
  change (nth row (map (fun item => Z.of_nat (snd item)) items) 0%Z) with
    (nth row (map (fun item => Z.of_nat (snd item)) items) (Z.of_nat (snd (0%nat, 0%nat)))).
  rewrite (map_nth (fun item : nat * nat => Z.of_nat (snd item)) items (0%nat, 0%nat) row).
  rewrite (execRead arraydef_0__dp (row * (limit + 1) + cap) 0%Z); [| cbn [tableMachine memory knapsackArrays]; rewrite table_length; unfold tableSize; nia].
  cbn [tableMachine memory knapsackArrays].
  rewrite table_read; [| exact hCap | nia].
  assert (powerOrder : (2^32 < 2^64)%nat) by (apply Nat.pow_lt_mono_r; lia).
  rewrite !coerce_nat64; [| lia | lia].
  destruct (bool_decide (Z.of_nat cap < Z.of_nat (fst (nth row items (0%nat, 0%nat))))) eqn:hFit.
  - apply bool_decide_eq_true in hFit. cbn [negb].
    assert (expected : knapsack (reverse (take (S row) items)) cap = knapsack (reverse (take row items)) cap).
    { rewrite (@prefix_step items row hRow).
      destruct (nth row items (0%nat, 0%nat)) as [weight value]. cbn [knapsack fst] in *.
      destruct (decide (cap < weight)%nat); [reflexivity | lia]. }
    fold writeArray. rewrite <- expected. apply writeTable; assumption.
  - apply bool_decide_eq_false in hFit. cbn [negb].
    rewrite <- Nat2Z.inj_sub; [| lia].
    rewrite coerce_nat64; [| nia].
    rewrite previousIndex_nat; [| nia | lia].
    fold readArray writeArray.
    rewrite (execRead arraydef_0__dp (row * (limit + 1) + (cap - fst (nth row items (0%nat, 0%nat)))) 0%Z);
      [| cbn [tableMachine memory knapsackArrays]; rewrite table_length; unfold tableSize; nia].
    cbn [tableMachine memory knapsackArrays].
    rewrite table_read; [| lia | nia].
    rewrite <- Nat2Z.inj_add.
    assert (candidateBound : (knapsack (reverse (take row items)) (cap - fst (nth row items (0%nat, 0%nat))) + snd (nth row items (0%nat, 0%nat)) < 2^64)%nat).
    { pose proof knapsack_sum (reverse (take row items)) (cap - fst (nth row items (0%nat, 0%nat))) as bound.
      rewrite sum_reverse in bound.
      pose proof sum_take items (S row) as sumBound.
      rewrite <- sum_reverse, (@prefix_step items row hRow) in sumBound.
      change (snd (nth row items (0%nat, 0%nat)) + list_sum (map snd (reverse (take row items))) <= list_sum (map snd items))%nat in sumBound.
      rewrite sum_reverse in sumBound. lia. }
    rewrite coerce_nat64; [| exact candidateBound].
    assert (storedEq :
      (if bool_decide (Z.of_nat (knapsack (reverse (take row items)) cap) <
        Z.of_nat (knapsack (reverse (take row items)) (cap - fst (nth row items (0%nat, 0%nat))) + snd (nth row items (0%nat, 0%nat))))
       then Z.of_nat (knapsack (reverse (take row items)) (cap - fst (nth row items (0%nat, 0%nat))) + snd (nth row items (0%nat, 0%nat)))
       else Z.of_nat (knapsack (reverse (take row items)) cap)) =
      Z.of_nat (knapsack (reverse (take (S row) items)) cap)).
    { rewrite (@prefix_step items row hRow).
      destruct (nth row items (0%nat, 0%nat)) as [weight value]. cbn [knapsack fst snd] in *.
      destruct (decide (cap < weight)%nat); [lia |].
      destruct (bool_decide (Z.of_nat (knapsack (reverse (take row items)) cap) <
        Z.of_nat (knapsack (reverse (take row items)) (cap - weight) + value))) eqn:hBest.
      - apply bool_decide_eq_true in hBest. rewrite Nat.max_r; [lia | lia].
      - apply bool_decide_eq_false in hBest. rewrite Nat.max_l; [reflexivity | lia]. }
    match goal with |- exec (Dispatch _ _ _ (Store _ _ ?name ?index ?value) _) ?state = ?expected =>
      change (exec (writeArray name index value) state = expected)
    end.
    match goal with |- exec (writeArray _ _ ?value) _ = _ =>
      assert (valueEq : value = Z.of_nat (knapsack (reverse (take (S row) items)) cap)) by exact storedEq
    end.
    rewrite valueEq. apply writeTable; assumption.
Qed.

Definition capsAction row limit count :=
  arrayLoop count (fun remaining => funcdef_0__cell (fun _ => false)
    (cellLocals (Z.of_nat row) (Z.of_nat (limit - remaining)) (Z.of_nat limit))).

Lemma capsExecution items limit row count message input buffer
  (hSize : (tableSize items limit < 2^64)%nat)
  (hRow : (row < length items)%nat) (hCount : (count <= limit + 1)%nat)
  (hWeights : forall item, In item items -> (fst item < 2^32)%nat)
  (hValues : forall item, In item items -> (snd item < 2^32)%nat)
  (hSum : (list_sum (map snd items) < 2^64)%nat) :
  exec (capsAction row limit count)
    (tableMachine items limit (S row * (limit + 1) + (limit + 1 - count)) message input buffer) =
  Some (tt, tableMachine items limit ((row + 2) * (limit + 1)) message input buffer).
Proof.
  unfold capsAction. induction count as [| count IH].
  - cbn [arrayLoop exec]. f_equal. f_equal. f_equal. lia.
  - cbn [arrayLoop]. rewrite exec_bind.
    replace (S row * (limit + 1) + (limit + 1 - S count))%nat with
      (S row * (limit + 1) + (limit - count))%nat by lia.
    rewrite cellExecution; try assumption; [| lia].
    cbn [optionBind fst snd].
    replace (S (S row * (limit + 1) + (limit - count))) with
      (S row * (limit + 1) + (limit + 1 - count))%nat by lia.
    apply IH. lia.
Qed.

Lemma solveActionExecution items limit message input buffer
  (hSize : (tableSize items limit < 2^64)%nat)
  (hWeights : forall item, In item items -> (fst item < 2^32)%nat)
  (hValues : forall item, In item items -> (snd item < 2^32)%nat)
  (hSum : (list_sum (map snd items) < 2^64)%nat) :
  exec (solveAction (Z.of_nat (length items)) (Z.of_nat limit))
    (tableMachine items limit (limit + 1) message input buffer) =
  Some (tt, tableMachine items limit (tableSize items limit) message input buffer).
Proof.
  unfold solveAction. replace (Z.of_nat limit + 1)%Z with (Z.of_nat (limit + 1)) by lia.
  rewrite coerce_nat64; [| unfold tableSize in hSize; nia].
  rewrite !Nat2Z.id.
  assert (loopProof : forall count, (count <= length items)%nat ->
    exec (arrayLoop count (fun row => arrayLoop (limit + 1) (fun cap =>
      funcdef_0__cell (fun _ => false)
        (cellLocals (Z.of_nat (length items) - Z.of_nat row - 1)
          (Z.of_nat (limit + 1) - Z.of_nat cap - 1) (Z.of_nat limit)))))
      (tableMachine items limit ((length items + 1 - count) * (limit + 1)) message input buffer) =
    Some (tt, tableMachine items limit (tableSize items limit) message input buffer)).
  { intros count bound. induction count as [| count IH].
    - cbn [arrayLoop exec]. unfold tableSize. rewrite Nat.sub_0_r. reflexivity.
    - cbn [arrayLoop]. rewrite exec_bind.
      replace (Z.of_nat (length items) - Z.of_nat count - 1)%Z with (Z.of_nat (length items - S count)) by lia.
      assert (capsEqual : arrayLoop (limit + 1) (fun cap =>
        funcdef_0__cell (fun _ => false)
          (cellLocals (Z.of_nat (length items - S count)) (Z.of_nat (limit + 1) - Z.of_nat cap - 1) (Z.of_nat limit))) =
        capsAction (length items - S count) limit (limit + 1)).
      { unfold capsAction. apply arrayLoop_ext. intros cap capBound.
        replace (Z.of_nat (limit + 1) - Z.of_nat cap - 1)%Z with (Z.of_nat (limit - cap)) by lia. reflexivity. }
      rewrite capsEqual.
      replace ((length items + 1 - S count) * (limit + 1))%nat with
        (S (length items - S count) * (limit + 1) + (limit + 1 - (limit + 1)))%nat by nia.
      rewrite capsExecution; try assumption; [| lia | lia].
      cbn [optionBind fst snd].
      replace ((length items - S count + 2) * (limit + 1))%nat with
        ((length items + 1 - count) * (limit + 1))%nat by nia.
      apply IH. lia. }
  specialize (loopProof (length items) ltac:(lia)).
  replace ((length items + 1 - length items) * (limit + 1))%nat with (limit + 1)%nat in loopProof by nia.
  exact loopProof.
Qed.
