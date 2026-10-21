From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith.
Open Scope Z_scope.

Module ReplyNOExecution.
Import IndexExecution.
Definition reply_state (s : Machine) := withOutput s (stdout s ++ Protocol.reply_bytes Protocol.NO).
Theorem generated_no s bs ns observations :
  execObserved (funcdef_0__no bs ns) (s,observations) = Some (tt,(reply_state s,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin s|}])).
Proof.
  destruct s as [values input output].
  cbv beta iota zeta delta [funcdef_0__no funcdef_0__no_body eliminateLocalVariables Action_rect
    loopString dropWithinLoop liftToWithinLoop bind writeChar flush execObserved observedStep step optionBind fst snd
    withOutput stdout stdin memory].
  unfold reply_state. cbn [Protocol.reply_bytes stdout stdin withOutput]. repeat rewrite <-app_assoc. reflexivity.
Qed.
Lemma reply_input s : stdin (reply_state s) = stdin s.
Proof. reflexivity. Qed.
Lemma reply_output s : stdout (reply_state s) = stdout s ++ Protocol.reply_bytes Protocol.NO.
Proof. reflexivity. Qed.
Lemma reply_memory s name : memory (reply_state s) name = memory s name.
Proof. reflexivity. Qed.
End ReplyNOExecution.
