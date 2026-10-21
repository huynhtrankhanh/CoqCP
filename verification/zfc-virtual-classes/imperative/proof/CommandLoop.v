From CoqCP Require Import Options Imperative Execution InteractiveExecution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow SipHash ObservedLocal ObservedTape CommandQuit SeedInput Startup QuitLoop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandLoopExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition pending_state (s : Machine) ch := store_meta s 15 (ch+1).
Definition outcome (s : Machine) := if bool_decide (meta_value s 9 <> 0) then Stop else KeepGoing.
Local Opaque funcdef_0__command.
Theorem generated_callback (f : SeedInputExecution.Frame) ch observations after trace :
  0 <= ch < 256 -> (15 < length (memory (machine f) arraydef_0__meta))%nat ->
  (9 < length (memory after arraydef_0__meta))%nat ->
  execObserved (funcdef_0__command (fun _ => false) (fun _ => 0)) (pending_state (machine f) ch,observations) = Some (tt,(after,trace)) ->
  execLocalObserved (QuitLoopExecution.callback ch) (f,observations) =
    Some (outcome after,(setMachine f after,trace)).
Proof.
  intros Hbyte Hmeta Hafter Hcommand. destruct f as [s bs ns]. cbn [machine] in *.
  unfold pending_state in Hcommand. unfold QuitLoopExecution.callback.
  repeat first [progress cbn [optionBind fst snd]
    |rewrite local_bind |rewrite drop_assoc |rewrite drop_lift |rewrite lift_correct |rewrite Hcommand
    |rewrite QuitLoopExecution.local_done
    |rewrite QuitLoopExecution.local_store_meta by (cbn [machine setMachine]; lia)
    |rewrite QuitLoopExecution.local_read_meta by (cbn [machine setMachine]; lia)
    |progress replace (Z.to_nat 15) with 15%nat by reflexivity
    |progress replace (Z.to_nat 9) with 9%nat by reflexivity
    |match goal with |- context [coerceInt ?value 64] =>
      rewrite (coerce_word value) by (unfold word, maximum; lia) end
    |progress cbn [bind addInt optionBind fst snd]
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ].
  unfold outcome. destruct (bool_decide (meta_value after 9 <> 0)); reflexivity.
Qed.
End CommandLoopExecution.
