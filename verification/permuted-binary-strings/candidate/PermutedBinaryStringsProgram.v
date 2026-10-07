(* Equalities to the actual generated bodies; normalized actions are not replacement programs. *)
From CoqCP Require Import Options Imperative Execution DecimalEncoding ArrayExecution.
From Submission Require Import PermutedBinaryStrings PermutedBinaryStringsCode PermutedBinaryStringsIO PermutedBinaryStringsPrinter.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia Logic.FunctionalExtensionality.
Open Scope Z_scope.
Create Rewrite HintDb pbs_maps.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 @dropWithinLoop_break @dropWithinLoop_continue @eliminateLift : pbs_maps.
#[local] Hint Rewrite @lookupSame @lookupDifferent using discriminate : pbs_maps.
Ltac normalize_pbs := repeat progress (autorewrite with advance_program pbs_maps; try rewrite <- !bindAssoc; cbn [bind]).

Definition flushAction : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit :=
  Dispatch _ _ _ (DoBasicEffect _ _ Flush) (fun _ => Done _ _ _ tt).
Definition queryCall index weight := funcdef_0__queryBit (fun _ => false) (queryNums index weight).
Definition recordCall index weight digit := funcdef_0__recordBit (fun _ => false) (recordNums index weight digit).
Definition bitReader := funcdef_0__readBit (fun _ => false) (fun _ => 0).
Definition roundNums n weight : varsfuncdef_0__round -> Z :=
  fun name => match name with
  | vardef_0__round_n => n | vardef_0__round_weight => weight end.
Definition roundCall n weight := funcdef_0__round (fun _ => false) (roundNums n weight).
Definition queryLoop n count weight := arrayLoop count
  (fun remaining => queryCall (n - Z.of_nat remaining - 1) weight).
Definition receiveLoop n count weight := arrayLoop count (fun remaining =>
  bitReader >>= fun _ => readArray arraydef_0__input 0 >>= fun digit =>
  recordCall (n - Z.of_nat remaining - 1) weight digit).
Definition roundAction n weight :=
  outputChar 63 >>= fun _ => outputChar 32 >>= fun _ =>
  queryLoop n (Z.to_nat n) weight >>= fun _ =>
  outputChar 10 >>= fun _ => flushAction >>= fun _ =>
  receiveLoop n (Z.to_nat n) weight >>= fun _ => charAction >>= fun _ => Done _ _ _ tt.

Lemma roundNormalized n weight : roundCall n weight = roundAction n weight.
Proof.
  unfold roundCall, funcdef_0__round, funcdef_0__round_body.
  unfold writeChar, numberLocalGet, retrieve. normalize_pbs.
  unfold roundAction, outputChar. cbn [bind].
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  unfold queryLoop.
  match goal with |- eliminateLocalVariables ?b ?nums (loop ?n ?body >>= ?continuation) = arrayLoop _ ?code >>= _ =>
    assert (queryBody : forall index next,
      eliminateLocalVariables b nums (body index >>= next) =
      code index >>= fun _ => eliminateLocalVariables b nums (next KeepGoing))
  end.
  { intros index next. cbn beta. normalize_pbs. unfold queryCall.
    replace (update (update (fun _ : varsfuncdef_0__queryBit => 0) vardef_0__queryBit_index (n-Z.of_nat index-1))
      vardef_0__queryBit_weight weight) with (queryNums (n-Z.of_nat index-1) weight).
    2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
    normalize_pbs. reflexivity. }
  rewrite (eliminate_arrayLoop _ _ _ _ _ queryBody).
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  unfold flush, flushAction. normalize_pbs.
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  unfold receiveLoop.
  match goal with |- eliminateLocalVariables ?b ?nums (loop ?n ?body >>= ?continuation) = arrayLoop _ ?code >>= _ =>
    assert (receiveBody : forall index next,
      eliminateLocalVariables b nums (body index >>= next) =
      code index >>= fun _ => eliminateLocalVariables b nums (next KeepGoing))
  end.
  { intros index next. cbn beta. normalize_pbs.
    unfold bitReader, readArray, recordCall. normalize_pbs. reflexivity. }
  rewrite (eliminate_arrayLoop _ _ _ _ _ receiveBody). reflexivity.
Qed.

Definition binaryChar c := bool_decide (c = 48) || bool_decide (c = 49).
Fixpoint readBinary fuel previous : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue Z :=
  match fuel with
  | O => Done _ _ _ previous
  | S fuel => charAction >>= fun c => if binaryChar c then Done _ _ _ c else readBinary fuel c
  end.
Definition bitBody : nat -> Action
  (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__readBit)
  withLocalVariablesReturnValue LoopOutcome := ltac:(
  let code := eval cbn [funcdef_0__readBit_body bind] in funcdef_0__readBit_body in
  lazymatch code with (loop _ ?body >>= _) => exact body end).
Lemma bitStep b previous index next :
  eliminateLocalVariables b (fun _ => previous) (bitBody index >>= next) =
  charAction >>= fun c => eliminateLocalVariables b (fun _ => c)
    (next (if binaryChar c then Stop else KeepGoing)).
Proof.
  unfold bitBody. normalize_pbs. unfold readChar, numberLocalSet, charAction. normalize_pbs.
  f_equal. apply functional_extensionality. intro c.
  rewrite pushNumberSet.
  match goal with |- eliminateLocalVariables _ ?nums _ = _ =>
    assert (numEq : nums = (fun _ : varsfuncdef_0__readBit => c))
      by (apply functional_extensionality; intro name; destruct name; reflexivity)
  end. rewrite numEq.
  unfold shortCircuitOr, numberLocalGet. normalize_pbs.
  unfold binaryChar. destruct (decide (c = 48)) as [h48 | h48].
  - rewrite !bool_decide_true by exact h48. cbn [orb bind]. normalize_pbs. reflexivity.
  - rewrite !bool_decide_false by exact h48. cbn [orb bind]. normalize_pbs.
    destruct (decide (c = 49)) as [h49 | h49].
    + rewrite !bool_decide_true by exact h49. cbn [orb bind]. normalize_pbs. reflexivity.
    + rewrite !bool_decide_false by exact h49. cbn [orb bind]. normalize_pbs. reflexivity.
Qed.
Lemma bitLoop b fuel previous next :
  eliminateLocalVariables b (fun _ => previous) (loop fuel bitBody >>= next) =
  readBinary fuel previous >>= fun c => eliminateLocalVariables b (fun _ => c) (next tt).
Proof.
  induction fuel as [| fuel IH] in previous |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, bitStep.
  cbn [readBinary]. rewrite <- bindAssoc. unfold charAction. cbn [bind].
  f_equal. apply functional_extensionality. intro c.
  destruct (binaryChar c); cbn [bind]; [reflexivity | apply IH].
Qed.
Lemma bitReaderNormalized : bitReader = readBinary 20 0 >>= writeArray arraydef_0__input 0.
Proof.
  unfold bitReader, funcdef_0__readBit, funcdef_0__readBit_body.
  cbn [bind]. fold bitBody. rewrite bitLoop.
  unfold writeArray, numberLocalGet, store. normalize_pbs. reflexivity.
Qed.

Definition printCall n := funcdef_0__printAnswer (fun _ => false) (fun _ => n).
Definition printLoop n count := arrayLoop count (fun remaining =>
  outputChar 32 >>= fun _ => readArray arraydef_0__answer (n-Z.of_nat remaining-1) >>= fun value =>
  mappedPrinter (coerceInt (value+1) 64)).
Definition printAction n := outputChar 33 >>= fun _ => printLoop n (Z.to_nat n) >>= fun _ =>
  outputChar 10 >>= fun _ => flushAction.
Lemma printNormalized n : printCall n = printAction n.
Proof.
  unfold printCall, funcdef_0__printAnswer, funcdef_0__printAnswer_body.
  unfold numberLocalGet, writeChar, retrieve, addInt. normalize_pbs.
  unfold printAction, outputChar. cbn [bind].
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  unfold printLoop.
  match goal with |- eliminateLocalVariables ?b ?nums (loop ?n ?body >>= ?continuation) = arrayLoop _ ?code >>= _ =>
    assert (printBody : forall index next,
      eliminateLocalVariables b nums (body index >>= next) =
      code index >>= fun _ => eliminateLocalVariables b nums (next KeepGoing))
  end.
  { intros index next. cbn beta. normalize_pbs.
    unfold outputChar, readArray, mappedPrinter. cbn [bind].
    f_equal. apply functional_extensionality. intros []. normalize_pbs.
    f_equal. apply functional_extensionality. intro value. normalize_pbs. reflexivity. }
  rewrite (eliminate_arrayLoop _ _ _ _ _ printBody). reflexivity.
Qed.

Definition mainNums n weight : varsfuncdef_0__main -> Z :=
  fun name => match name with vardef_0__main_n => n | vardef_0__main_weight => weight end.
Fixpoint roundsAction fuel n weight :=
  match fuel with
  | O => Done (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit tt
  | S fuel => roundCall n weight >>= fun _ => roundsAction fuel n (coerceInt (2*weight) 64)
  end.
Definition mainAction := mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun n =>
  roundsAction 10 n 1 >>= fun _ => printCall n.
Definition mainRoundBody : nat -> Action
  (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  lazymatch code with context [(Done _ _ _ 10%Z >>= ?cont)] =>
    let code := eval cbn [bind] in (Done _ _ _ 10%Z >>= cont) in
    lazymatch code with loop _ ?body => exact body end
  end).
Lemma mainRoundStep b n weight index next :
  eliminateLocalVariables b (mainNums n weight) (mainRoundBody index >>= next) =
  roundCall n weight >>= fun _ => eliminateLocalVariables b (mainNums n (coerceInt (2*weight) 64)) (next KeepGoing).
Proof.
  unfold mainRoundBody, numberLocalGet, numberLocalSet, multInt. normalize_pbs.
  unfold roundCall.
  replace (update (update (fun _ : varsfuncdef_0__round => 0) vardef_0__round_n n) vardef_0__round_weight weight)
    with (roundNums n weight).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  normalize_pbs. f_equal. apply functional_extensionality. intros []. normalize_pbs.
  replace (update (mainNums n weight) vardef_0__main_weight (coerceInt (2*weight) 64))
    with (mainNums n (coerceInt (2*weight) 64)).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  reflexivity.
Qed.
Lemma mainRounds b fuel n weight next :
  eliminateLocalVariables b (mainNums n weight) (loop fuel mainRoundBody >>= next) =
  roundsAction fuel n weight >>= fun _ => eliminateLocalVariables b (mainNums n (Nat.iter fuel (fun w => coerceInt (2*w) 64) weight)) (next tt).
Proof.
  induction fuel as [| fuel IH] in weight |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, mainRoundStep.
  cbn [roundsAction]. rewrite <- bindAssoc.
  f_equal. apply functional_extensionality. intros []. rewrite IH.
  rewrite Nat.iter_succ_r. reflexivity.
Qed.
Lemma mainRoundsFor b body
  (step : forall n weight index next,
    eliminateLocalVariables b (mainNums n weight) (body index >>= next) =
    roundCall n weight >>= fun _ => eliminateLocalVariables b (mainNums n (coerceInt (2*weight) 64)) (next KeepGoing))
  fuel n weight next :
  eliminateLocalVariables b (mainNums n weight) (loop fuel body >>= next) =
  roundsAction fuel n weight >>= fun _ => eliminateLocalVariables b (mainNums n (Nat.iter fuel (fun w => coerceInt (2*w) 64) weight)) (next tt).
Proof.
  induction fuel as [| fuel IH] in weight |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, step.
  cbn [roundsAction]. rewrite <- bindAssoc.
  f_equal. apply functional_extensionality. intros []. rewrite IH.
  rewrite Nat.iter_succ_r. reflexivity.
Qed.

Lemma mainNormalized : funcdef_0__main (fun _ => false) (fun _ => 0) = mainAction.
Proof.
  unfold funcdef_0__main, funcdef_0__main_body. cbn [bind]. fold mappedReader.
  unfold numberLocalGet, numberLocalSet, retrieve. normalize_pbs.
  unfold mainAction. f_equal. apply functional_extensionality. intros []. normalize_pbs.
  unfold readArray. cbn [bind].
  f_equal. apply functional_extensionality. intro n. normalize_pbs.
  replace (update (update (fun _ : varsfuncdef_0__main => 0) vardef_0__main_n n) vardef_0__main_weight 1)
    with (mainNums n 1).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  match goal with |- eliminateLocalVariables ?b _ (loop _ ?body >>= _) = _ =>
    assert (actualStep : forall n' weight index next,
      eliminateLocalVariables b (mainNums n' weight) (body index >>= next) =
      roundCall n' weight >>= fun _ => eliminateLocalVariables b (mainNums n' (coerceInt (2*weight) 64)) (next KeepGoing))
  end.
  { intros n' weight index next. cbn beta. unfold multInt. normalize_pbs.
    unfold roundCall.
    replace (update (update (fun _ : varsfuncdef_0__round => 0) vardef_0__round_n n') vardef_0__round_weight weight)
      with (roundNums n' weight).
    2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
    normalize_pbs. f_equal. apply functional_extensionality. intros []. normalize_pbs.
    replace (update (mainNums n' weight) vardef_0__main_weight (coerceInt (2*weight) 64))
      with (mainNums n' (coerceInt (2*weight) 64)).
    2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
    reflexivity. }
  rewrite (mainRoundsFor _ _ actualStep).
  f_equal. apply functional_extensionality. intros []. normalize_pbs.
  unfold printCall.
  replace (update (fun _ : varsfuncdef_0__printAnswer => 0) vardef_0__printAnswer_n n)
    with (fun _ : varsfuncdef_0__printAnswer => n).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  cbn [eliminateLocalVariables]. apply bind_unit_identity.
Qed.
