From CoqCP Require Import Options Imperative Execution ArrayExecution.
From Submission Require Import KthHighestScoreCode KthHighestScoreIO KthHighestScorePrinter.
From Generated Require Import KthHighestScore.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Open Scope Z_scope.

Definition queryCall country index n := funcdef_0__query (fun _ => false)
  (update (update (update (fun _ => 0) vardef_0__query_country country)
    vardef_0__query_index index) vardef_0__query_n n).
Definition flushAction : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit :=
  Dispatch _ _ _ (DoBasicEffect _ _ Flush) (fun _ => Done _ _ _ tt).
Fixpoint searchAction fuel n k lo hi : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue Z :=
  match fuel with
  | O => Done _ _ _ lo
  | S fuel => if bool_decide (lo = hi) then Done _ _ _ lo else
      let mid := coerceInt (lo+hi) 64 / 2 in
      queryCall 70 (coerceInt (mid+1) 64) n >>= fun _ =>
      readArray arraydef_0__reply 0 >>= fun fv =>
      queryCall 83 (coerceInt (k-mid) 64) n >>= fun _ =>
      readArray arraydef_0__reply 0 >>= fun sv =>
      if bool_decide (fv < sv) then searchAction fuel n k lo mid
      else searchAction fuel n k (coerceInt (mid+1) 64) hi
  end.
Definition finalAction n k lo :=
  queryCall 70 lo n >>= fun _ => readArray arraydef_0__reply 0 >>= fun fv =>
  queryCall 83 (coerceInt (k-lo) 64) n >>= fun _ => readArray arraydef_0__reply 0 >>= fun sv =>
  outputChar 33 >>= fun _ => outputChar 32 >>= fun _ =>
  mappedPrinter (if bool_decide (sv < fv) then sv else fv) >>= fun _ =>
  outputChar 10 >>= fun _ => flushAction.
Definition mainAction :=
  mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun n =>
  mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun k =>
  searchAction 17 n k (if bool_decide (n < k) then coerceInt (k-n) 64 else 0)
    (if bool_decide (n < k) then n else k) >>= finalAction n k.

Create Rewrite HintDb kth_maps.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1
  @dropWithinLoop_2 @dropWithinLoop_break @eliminateLift : kth_maps.
#[local] Hint Rewrite @pushNumberGet @pushNumberGet2 @pushNumberSet @pushNumberSet2
  @pushDispatch @pushDispatch2 : kth_maps.
#[local] Hint Rewrite @lookupSame @lookupDifferent using discriminate : kth_maps.
Ltac normalize_kth := repeat progress (
  repeat rewrite <- bindAssoc;
  rewrite ?dropWithinLoopLiftToWithinLoop, ?dropWithinLoop_1, ?dropWithinLoop_2,
    ?dropWithinLoop_break, ?eliminateLift, ?pushNumberGet, ?pushNumberGet2,
    ?pushNumberSet, ?pushNumberSet2, ?pushDispatch, ?pushDispatch2;
  cbn [bind withLocalVariablesReturnValue]; repeat first [rewrite lookupSame | rewrite lookupDifferent by discriminate]).
Lemma eliminate_lift_unit b regs (code : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit) :
  @eliminateLocalVariables _ _ varsfuncdef_0__main _ b regs (liftToWithLocalVariables code) = code.
Proof.
  induction code as [value | effect cont IH]; [destruct value; reflexivity |].
  cbn [liftToWithLocalVariables eliminateLocalVariables Action_rect].
  f_equal. apply functional_extensionality. apply IH.
Qed.
Definition afterSearch (next : Z -> Z -> Z -> Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit) :=
  numberLocalGet _ _ _ vardef_0__main_n >>= fun n =>
  numberLocalGet _ _ _ vardef_0__main_k >>= fun k =>
  numberLocalGet _ _ _ vardef_0__main_lo >>= fun lo =>
  liftToWithLocalVariables (next n k lo).
Lemma searchNormalized fuel b regs next :
  eliminateLocalVariables b regs
    (loop fuel kernelBody >>= fun _ => afterSearch next) =
  searchAction fuel (regs vardef_0__main_n) (regs vardef_0__main_k)
    (regs vardef_0__main_lo) (regs vardef_0__main_hi) >>=
    next (regs vardef_0__main_n) (regs vardef_0__main_k).
Proof.
  induction fuel as [| fuel IH] in regs |- *.
  - unfold afterSearch, numberLocalGet. cbn [loop searchAction bind].
    normalize_kth. apply eliminate_lift_unit.
  - rewrite loop_S, <- bindAssoc. unfold kernelBody at 1.
    unfold numberLocalGet, numberLocalSet, addInt, subInt, divIntUnsigned, retrieve.
    normalize_kth.
    destruct (bool_decide (regs vardef_0__main_lo = regs vardef_0__main_hi)) eqn:heq.
    + normalize_kth. unfold afterSearch, numberLocalGet. normalize_kth.
      cbn [searchAction]. rewrite heq. cbn [bind]. apply eliminate_lift_unit.
    + normalize_kth. rewrite decide_False by lia. normalize_kth.
      cbn [searchAction]. rewrite heq. cbn [bind].
      replace (coerceInt 70 8) with 70 by reflexivity.
      replace (coerceInt 83 8) with 83 by reflexivity.
      fold queryCall. unfold readArray. normalize_kth.
      f_equal. apply functional_extensionality. intros []. normalize_kth.
      f_equal. apply functional_extensionality. intro fv. normalize_kth.
      f_equal. apply functional_extensionality. intros []. normalize_kth.
      f_equal. apply functional_extensionality. intro sv. normalize_kth.
      destruct (bool_decide (fv < sv)); normalize_kth; rewrite IH; normalize_kth; reflexivity.
Qed.

Definition generatedTail : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  lazymatch code with context [((Done _ _ _ 17%Z >>= ?body) >>= ?next)] => exact (next tt) end).
Lemma tailNormalized b regs : eliminateLocalVariables b regs generatedTail =
  finalAction (regs vardef_0__main_n) (regs vardef_0__main_k) (regs vardef_0__main_lo).
Proof.
  unfold generatedTail, finalAction, numberLocalGet, numberLocalSet, subInt, retrieve, writeChar, flush.
  normalize_kth.
  replace (coerceInt 70 8) with 70 by reflexivity.
  replace (coerceInt 83 8) with 83 by reflexivity.
  fold queryCall. unfold readArray. normalize_kth.
  f_equal. apply functional_extensionality. intros []. normalize_kth.
  f_equal. apply functional_extensionality. intro fv. normalize_kth.
  f_equal. apply functional_extensionality. intros []. normalize_kth.
  f_equal. apply functional_extensionality. intro sv. normalize_kth.
  destruct (bool_decide (sv < fv)); normalize_kth;
    cbn [loopString bind]; normalize_kth;
    unfold outputChar; cbn [bind]; normalize_kth;
    fold mappedPrinter; unfold flushAction; normalize_kth; reflexivity.
Qed.
Lemma eliminate_cont {R} b regs
  (code : Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue R)
  (left right : R -> Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main) withLocalVariablesReturnValue unit)
  (h : forall b regs value, eliminateLocalVariables b regs (left value) = eliminateLocalVariables b regs (right value)) :
  eliminateLocalVariables b regs (code >>= left) = eliminateLocalVariables b regs (code >>= right).
Proof.
  induction code as [value | effect cont IH] in b, regs |- *; [apply h |].
  destruct effect; cbn [bind eliminateLocalVariables Action_rect]; try apply IH.
  f_equal. apply functional_extensionality. intro response. apply IH.
Qed.
Lemma mainNormalized : funcdef_0__main (fun _ => false) (fun _ => 0) = mainAction.
Proof.
  unfold funcdef_0__main, funcdef_0__main_body, mainAction.
  cbn [bind]. fold mappedReader.
  unfold numberLocalGet, numberLocalSet, subInt, retrieve.
  normalize_kth. unfold readArray. cbn [bind].
  f_equal. apply functional_extensionality. intros []. normalize_kth.
  f_equal. apply functional_extensionality. intro n. normalize_kth.
  f_equal. apply functional_extensionality. intros []. normalize_kth.
  f_equal. apply functional_extensionality. intro k. normalize_kth.
  cbn [withArraysReturnValue] in n, k |- *.
  destruct (bool_decide (n < k)) eqn:hTest; normalize_kth;
    try rewrite hTest; normalize_kth.
  all: match goal with |- eliminateLocalVariables ?b ?regs (loop ?count ?body >>= ?tail) = ?rhs =>
    change (eliminateLocalVariables b regs (loop 17 kernelBody >>= fun _ => generatedTail) = rhs);
    transitivity (eliminateLocalVariables b regs (loop 17 kernelBody >>= fun _ => afterSearch finalAction))
  end.
  all: try solve [apply eliminate_cont; intros; rewrite tailNormalized; unfold afterSearch, numberLocalGet;
       normalize_kth; symmetry; apply eliminate_lift_unit].
  all: rewrite searchNormalized; normalize_kth; reflexivity.
Qed.

Lemma queryNormalized country index n : queryCall country index n =
  if bool_decide (index = 0) then writeArray arraydef_0__reply 0 1000000001 else
  if bool_decide (index = coerceInt (n+1) 64) then writeArray arraydef_0__reply 0 0 else
  outputChar country >>= fun _ => outputChar 32 >>= fun _ =>
  mappedPrinter index >>= fun _ => outputChar 10 >>= fun _ => flushAction >>= fun _ =>
  mappedReader >>= fun _ => readArray arraydef_0__input 0 >>= fun value =>
  @writeArray arrayIndex2 (arrayType _ environment2) arraydef_0__reply 0 value.
Proof.
  unfold queryCall, funcdef_0__query, funcdef_0__query_body.
  unfold numberLocalGet, numberLocalSet, addInt, retrieve, store, writeChar, flush.
  normalize_kth.
  destruct (bool_decide (index = 0)); normalize_kth.
  - reflexivity.
  - destruct (bool_decide (index = coerceInt (n+1) 64)); normalize_kth.
    + reflexivity.
    + unfold outputChar, flushAction, readArray, writeArray. cbn [bind].
      fold mappedPrinter mappedReader. normalize_kth. reflexivity.
Qed.
