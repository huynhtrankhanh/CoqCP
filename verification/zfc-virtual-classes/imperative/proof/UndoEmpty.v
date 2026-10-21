From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandChain CommandDispatch CommandSteps ReplyNO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module UndoEmptyExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Local Opaque funcdef_0__no funcdef_0__ok.
Theorem generated_handler reader (f : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 8 = 0 -> meta_value (machine f) 3 = 0 ->
  execLocalObserved (CommandStructure.handler_16 reader) (f,observations) =
    Some (tt,(setMachine f (ReplyNOExecution.reply_state (machine f)),
      observations ++ [{|flushedOutput := stdout (machine f) ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin (machine f)|}])).
Proof.
  intros Hmeta Herror Hhistory. destruct f as [s bs ns]. cbn [machine] in *.
  unfold CommandStructure.handler_16.
  repeat first [progress cbn [optionBind fst snd]
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bs_no ?ns_no) ?state] =>
        lazymatch state with (?current,?trace) =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__no bs_no ns_no) state) in
          let Hno := fresh "Hno" in
          assert (Hno : expression = Some (tt,(ReplyNOExecution.reply_state current,
            trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
            (exact (ReplyNOExecution.generated_no current bs_no ns_no trace)); rewrite Hno; clear Hno
        end
      end
    |match goal with |- context [meta_value s 8] => progress rewrite Herror end
    |match goal with |- context [meta_value s 3] => progress rewrite Hhistory end
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Theorem generated_after_read s bs ns readstate observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = 16 -> meta_value readstate 14 = 1 ->
  meta_value readstate 8 = 0 -> meta_value readstate 3 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(ReplyNOExecution.reply_state readstate,
      observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hmeta Hnumber Hvalid Herror Hhistory.
  set (f := {|machine := s; bools := bs; nums := ns|}).
  set (initial := CommandDispatch.opcode_frame f readstate 16).
  set (after := setMachine initial (ReplyNOExecution.reply_state readstate)).
  apply (CommandDispatch.generated_positive_command s bs ns after readstate 16 observations
    (observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin readstate|}]));
    try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_16 funcdef_0__readNat) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin readstate|}]))).
    apply generated_handler; assumption.
  - change (8 < length (memory readstate arraydef_0__meta))%nat. lia.
Qed.
End UndoEmptyExecution.
