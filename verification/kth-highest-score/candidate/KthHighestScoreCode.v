From CoqCP Require Import Options Imperative Execution.
From Generated Require Import KthHighestScore.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Open Scope Z_scope.

(* Extract the loop directly from the generated entry point, without replacing
   any procedure or effect. *)
Definition generatedSearchLoop :
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  lazymatch code with context [(Done _ _ _ 17%Z >>= ?cont)] =>
    let body := eval cbn [bind] in (Done _ _ _ 17%Z >>= cont) in exact body
  end).
Definition kernelBody : nat ->
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue LoopOutcome := ltac:(
  let code := eval unfold generatedSearchLoop in generatedSearchLoop in
  lazymatch code with loop _ ?body => exact body end).

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
