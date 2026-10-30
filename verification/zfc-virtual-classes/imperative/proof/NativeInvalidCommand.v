From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeInvalidCommand.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Definition failed state := store_meta state 8 1.
Definition final state := store_meta (withOutput(failed state)(stdout state++Protocol.reply_bytes Protocol.ERR))9 1.
Theorem generated_body reader (f:Frame) readstate observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(readstate,observations)) ->
 (17<length(memory readstate arraydef_0__meta))%nat ->
 meta_value readstate 11=0 -> meta_value readstate 14=0 -> meta_value readstate 8=1 -> meta_value readstate 6=1024 ->
 execLocalObserved(body_with reader)(f,observations)=Some(tt,
  (setMachine (setNum (setMachine f readstate) vardef_0__command_op 0) (final readstate),
   observations++[{|flushedOutput:=stdout readstate++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin readstate|}])).
Proof.
 intros Hreader Hmeta Hnumber Hvalid Herror Hcount. destruct f as [s bs ns]. cbn [machine] in Hreader.
 destruct (Z.eq_dec (meta_value readstate 7) 0) as [Heof|Heof].
 all: unfold body_with.
 all: repeat first [match goal with |- context [execLocalObserved (bind ?code ?next) ?state] => rewrite (local_bind code next state) end
  |match goal with |- context [execLocalObserved (liftToWithLocalVariables ?code) (?frame,?trace)] => rewrite (lift_correct code frame trace) end |rewrite Hreader
  |rewrite local_done |rewrite local_get |rewrite local_set |rewrite local_write |rewrite local_flush
  |rewrite local_read_meta by (cbn [machine setMachine];repeat first [rewrite store_meta_length|rewrite output_length];lia)
  |rewrite local_store_meta by (cbn [machine setMachine];repeat first [rewrite store_meta_length|rewrite output_length];lia)
  |rewrite output_meta |rewrite meta_store_other by lia |rewrite meta_store_same by (repeat rewrite store_meta_length;lia)
  |rewrite Hnumber |rewrite Hvalid |rewrite Herror |rewrite Hcount |rewrite Heof
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 9) with 9%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 7) with 7%nat by reflexivity
  |progress replace (Z.to_nat 6) with 6%nat by reflexivity
  |match goal with |- context [execLocalObserved (dropWithinLoop (bind (bind ?code ?next) ?last)) ?state] => rewrite (drop_assoc code next last state) end
  |match goal with |- context [execLocalObserved (dropWithinLoop (bind (liftToWithinLoop ?code) ?next)) ?state] => rewrite (drop_lift code next state) end
  |rewrite dropWithinLoop_1
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by (try congruence;lia)|rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [rewrite (decide_True (P := P)) by congruence |rewrite (decide_False (P := P)) by congruence] end
  |match goal with |- context [execLocalObserved (shortCircuitAnd _ _) _] => unfold shortCircuitAnd at 1 end
  |match goal with |- context [execLocalObserved (shortCircuitOr _ _) _] => unfold shortCircuitOr at 1 end
  |progress cbn [bind optionBind fst snd shortCircuitAnd shortCircuitOr loopString]
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]].
 all: unfold final,failed,Protocol.reply_bytes. all: cbn [withOutput store_meta withMemory memory stdout stdin setMachine setNum machine nums bools Imperative.update].
 all: repeat rewrite <-List.app_assoc. all: reflexivity.
Qed.
End NativeInvalidCommand.
