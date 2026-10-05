From CoqCP Require Import Options Imperative Execution KthHighestScore.
From Generated Require Import KthHighestScore.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia Logic.FunctionalExtensionality.
Open Scope Z_scope.

Definition QueryProcedure :=
  (varsfuncdef_0__query -> bool) -> (varsfuncdef_0__query -> Z) ->
  Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.

(* Abstract only the query procedure in the actual compiler output. *)
Definition mainWithQuery : QueryProcedure ->
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  let code := eval pattern funcdef_0__query in code in
  lazymatch code with ?f funcdef_0__query => exact f end).
Lemma mainWithQuery_original : mainWithQuery funcdef_0__query = funcdef_0__main_body.
Proof. reflexivity. Qed.

(* Extract the actual 17-round loop; no hand-written replacement loop. *)
Definition generatedSearchLoop (query : QueryProcedure) :
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue unit := ltac:(
  let code := eval cbv beta delta [mainWithQuery] in (mainWithQuery query) in
  lazymatch code with context [(Done _ _ _ 17%Z >>= ?cont)] =>
    let body := eval cbn [bind] in (Done _ _ _ 17%Z >>= cont) in exact body
  end).

Definition oracleQuery (F S : nat -> nat) : QueryProcedure :=
  fun _ nums => Dispatch _ _ _
    (Store _ _ arraydef_0__reply 0
      (Z.of_nat ((if bool_decide (nums vardef_0__query_country = 70) then F else S)
        (Z.to_nat (nums vardef_0__query_index)))))
    (fun _ => Done _ _ _ tt).

Definition kernelArrays (reply : Z) : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__input => [0]
  | arraydef_0__reply => [reply]
  | arraydef_0__printBuffer => repeat 0 20
  end.
Definition kernelMachine reply : Machine :=
  {| memory := kernelArrays reply; stdin := []; stdout := [] |}.

Lemma kernel_modify reply value :
  modifyArray (kernelArrays reply) arraydef_0__reply 0 value = kernelArrays value.
Proof.
  apply functional_extensionality_dep. intro name. destruct name; reflexivity.
Qed.
Lemma kernel_store reply value :
  step (Store arrayIndex2 (arrayType _ environment2) arraydef_0__reply 0 value)
    (kernelMachine reply) = Some (tt, kernelMachine value).
Proof.
  change (Some (tt, withMemory (kernelMachine reply)
    (modifyArray (kernelArrays reply) arraydef_0__reply 0 value)) = Some (tt, kernelMachine value)).
  rewrite kernel_modify. reflexivity.
Qed.
Lemma kernel_read reply :
  step (Retrieve arrayIndex2 (arrayType _ environment2) arraydef_0__reply 0)
    (kernelMachine reply) = Some (reply, kernelMachine reply).
Proof. reflexivity. Qed.

Definition mainNums (n k lo hi mid j f s a : nat) : varsfuncdef_0__main -> Z :=
  fun name => Z.of_nat (match name with
  | vardef_0__main_n => n | vardef_0__main_k => k
  | vardef_0__main_lo => lo | vardef_0__main_hi => hi
  | vardef_0__main_mid => mid | vardef_0__main_j => j
  | vardef_0__main_f => f | vardef_0__main_s => s | vardef_0__main_answer => a
  end).

Definition kernelBody (query : QueryProcedure) : nat ->
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue LoopOutcome := ltac:(
  let code := eval unfold generatedSearchLoop in (generatedSearchLoop query) in
  lazymatch code with loop _ ?body => exact body end).
Lemma kernelLoop_exact query : generatedSearchLoop query = loop 17 (kernelBody query).
Proof. reflexivity. Qed.

Lemma small_coerce value (h : 0 <= value <= 200001) : coerceInt value 64 = value.
Proof. unfold coerceInt. apply Z.mod_small. split; [lia |].
  assert (200001 < 2^64) by (vm_compute; reflexivity). lia.
Qed.

Lemma compare_nat x y : bool_decide (Z.of_nat x < Z.of_nat y) = (x <? y)%nat.
Proof.
  destruct (Nat.ltb_spec0 x y).
  - rewrite bool_decide_true by lia. reflexivity.
  - rewrite bool_decide_false by lia. reflexivity.
Qed.
Ltac advance_kernel :=
  repeat progress (rewrite ?dropWithinLoop_2, ?dropWithinLoop_1;
    cbn [bind liftToWithinLoop liftToWithLocalVariables retrieve
      numberLocalSet execLocal localStep optionBind fst snd setNum setMachine machine nums bools];
    rewrite ?kernel_read;
    repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate]).

Lemma generated_step n k lo hi mid j f s a b reply round F S
  (hBounds : (lo <= hi /\ hi <= n /\ hi <= k /\ n <= 100000 /\ k <= 2*n)%nat) :
  execLocal (kernelBody (oracleQuery F S) round)
    {| machine := kernelMachine reply; bools := b; nums := mainNums n k lo hi mid j f s a |} =
  if Nat.eq_dec lo hi then
    Some (Stop, {| machine := kernelMachine reply; bools := b;
                    nums := mainNums n k lo hi mid j f s a |})
  else
    let m := ((lo+hi)/2)%nat in
    let fv := F (Datatypes.S m) in
    let sv := S (k-m)%nat in
    Some (KeepGoing,
      {| machine := kernelMachine (Z.of_nat sv); bools := b;
         nums := if (fv <? sv)%nat then mainNums n k lo m m (k-m) fv sv a
                 else mainNums n k (Datatypes.S m) hi m (k-m) fv sv a |}).
Proof.
  assert (hN : Z.of_nat n <= 100000).
  { destruct hBounds as [_ [_ [_ [hn _]]]]. apply Nat2Z.inj_le in hn. exact hn. }
  unfold kernelBody.
  repeat progress (rewrite ?dropWithinLoop_2, ?dropWithinLoop_1;
  cbn [oracleQuery dropWithinLoop liftToWithinLoop liftToWithLocalVariables
    numberLocalGet numberLocalSet addInt subInt divIntUnsigned bind
    execLocal localStep optionBind fst snd setNum setMachine machine nums bools mainNums kernelMachine]).
  cbv beta iota zeta delta [mainNums].
  destruct (Nat.eq_dec lo hi) as [heq | hne].
  - subst hi. rewrite bool_decide_true by reflexivity.
    rewrite <- !bindAssoc, dropWithinLoop_break. reflexivity.
  - rewrite bool_decide_false by (intro h; apply hne; lia).
    repeat progress (rewrite ?dropWithinLoop_2, ?dropWithinLoop_1;
      cbn [bind dropWithinLoop liftToWithinLoop liftToWithLocalVariables
        execLocal localStep optionBind fst snd setNum setMachine machine nums bools]).
    rewrite decide_False by lia.
    rewrite small_coerce by lia.
    rewrite <- Nat2Z.inj_add.
    replace (Z.of_nat (lo+hi) / 2) with (Z.of_nat ((lo+hi)/2)%nat)
      by (rewrite Nat2Z.inj_div; reflexivity).
    repeat progress (rewrite ?dropWithinLoop_2, ?dropWithinLoop_1;
      cbn [bind dropWithinLoop liftToWithinLoop liftToWithLocalVariables
        numberLocalSet execLocal localStep optionBind fst snd setNum setMachine machine nums bools];
      repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate]).
    repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate].
    pose proof (midpoint_bounds lo hi ltac:(lia)) as hm.
    rewrite !small_coerce by lia.
    replace (coerceInt 70 8) with 70 by reflexivity.
    rewrite bool_decide_true by reflexivity.
    replace (Z.of_nat ((lo+hi)/2)%nat + 1)
      with (Z.of_nat (Datatypes.S ((lo+hi)/2)%nat)) by lia.
    rewrite Nat2Z.id.
    rewrite kernel_store.
    repeat progress (rewrite ?dropWithinLoop_2, ?dropWithinLoop_1;
      cbn [bind liftToWithinLoop liftToWithLocalVariables retrieve
        numberLocalSet execLocal localStep optionBind fst snd setNum setMachine machine nums bools];
      rewrite ?kernel_read;
      repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate]).
    replace (coerceInt 83 8) with 83 by reflexivity.
    rewrite bool_decide_false by lia.
    rewrite <- Nat2Z.inj_sub by lia. rewrite Nat2Z.id, kernel_store.
    advance_kernel. rewrite compare_nat.
    destruct ((F (Datatypes.S ((lo+hi)/2)) <? S (k-(lo+hi)/2))%nat).
    + advance_kernel.
      cbv beta iota zeta delta [setNum setMachine machine nums bools].
      f_equal. f_equal. f_equal.
      apply functional_extensionality. intro name. destruct name;
        repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate]; reflexivity.
    + advance_kernel. rewrite small_coerce by lia.
      cbv beta iota zeta delta [setNum setMachine machine nums bools].
      f_equal. f_equal. f_equal.
      apply functional_extensionality. intro name. destruct name;
        repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate]; try reflexivity.
      lia.
Qed.

Lemma generated_loop_refines fuel n k lo hi mid j f s a b reply F S
  (hBounds : (lo <= hi /\ hi <= n /\ hi <= k /\ n <= 100000 /\ k <= 2*n)%nat) :
  exists lo' hi' mid' j' f' s' reply',
    execLocal (loop fuel (kernelBody (oracleQuery F S)))
      {| machine := kernelMachine reply; bools := b; nums := mainNums n k lo hi mid j f s a |} =
    Some (tt, {| machine := kernelMachine reply'; bools := b;
                 nums := mainNums n k lo' hi' mid' j' f' s' a |}) /\
    lo' = search fuel (crossing k F S) lo hi.
Proof.
  induction fuel as [| fuel IH] in lo, hi, mid, j, f, s, reply, hBounds |- *.
  - exists lo, hi, mid, j, f, s, reply. split; reflexivity.
  - rewrite loop_S, execLocal_bind, generated_step by exact hBounds.
    destruct (Nat.eq_dec lo hi) as [heq | hne].
    + cbn [optionBind fst snd execLocal]. exists lo, hi, mid, j, f, s, reply.
      split; [reflexivity |]. cbn [search].
      assert (hTest : (lo <? hi)%nat = false) by (apply Nat.ltb_ge; lia).
      rewrite hTest. reflexivity.
    + pose proof (midpoint_bounds lo hi ltac:(lia)) as hm.
      assert (hTest : (lo <? hi)%nat = true) by (apply Nat.ltb_lt; lia).
      cbn [optionBind fst snd].
      destruct ((F (Datatypes.S ((lo+hi)/2)) <? S (k-(lo+hi)/2))%nat) eqn:hCross.
      * destruct (IH lo ((lo+hi)/2)%nat ((lo+hi)/2)%nat (k-(lo+hi)/2)%nat
          (F (Datatypes.S ((lo+hi)/2))) (S (k-(lo+hi)/2)%nat)
          (Z.of_nat (S (k-(lo+hi)/2)%nat)) ltac:(lia))
          as (lo' & hi' & mid' & j' & f' & s' & reply' & executed & result).
        exists lo', hi', mid', j', f', s', reply'. split.
        -- exact executed.
        -- cbn [search]. rewrite hTest. unfold crossing. rewrite hCross. exact result.
      * destruct (IH (Datatypes.S ((lo+hi)/2)%nat) hi ((lo+hi)/2)%nat (k-(lo+hi)/2)%nat
          (F (Datatypes.S ((lo+hi)/2))) (S (k-(lo+hi)/2)%nat)
          (Z.of_nat (S (k-(lo+hi)/2)%nat)) ltac:(lia))
          as (lo' & hi' & mid' & j' & f' & s' & reply' & executed & result).
        exists lo', hi', mid', j', f', s', reply'. split.
        -- exact executed.
        -- cbn [search]. rewrite hTest. unfold crossing. rewrite hCross. exact result.
Qed.

Local Opaque search.

Theorem generated_search_correct n k F S
  (hn : (1 <= n)%nat) (hk : (1 <= k <= 2*n)%nat) (hSize : (n <= 100000)%nat)
  (hF : country_valid n F) (hS : country_valid n S)
  (hDistinct : forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> F i <> S j) :
  exists final,
    execLocal (generatedSearchLoop (oracleQuery F S))
      {| machine := kernelMachine 0; bools := fun _ => false;
         nums := mainNums n k (low n k) (high n k) 0 0 0 0 0 |} = Some (tt, final) /\
    kth_highest n k F S
      (Nat.min (F (Z.to_nat (nums final vardef_0__main_lo)))
        (S (k - Z.to_nat (nums final vardef_0__main_lo))%nat)).
Proof.
  pose proof (feasible_bounds n k hn hk) as hb.
  rewrite kernelLoop_exact.
  destruct (generated_loop_refines 17 n k (low n k) (high n k) 0 0 0 0 0
    (fun _ => false) 0 F S ltac:(lia))
    as (lo' & hi' & mid' & j' & f' & s' & reply' & executed & result).
  eexists. split; [exact executed |].
  cbn [nums]. change (kth_highest n k F S
    (Nat.min (F (Z.to_nat (Z.of_nat lo'))) (S (k-Z.to_nat (Z.of_nat lo'))%nat))).
  rewrite Nat2Z.id, result.
  pose proof (answer_correct n k F S hn hk hF hS hDistinct hSize) as correct.
  unfold answer, partition in correct. exact correct.
Qed.
Print Assumptions generated_search_correct.
