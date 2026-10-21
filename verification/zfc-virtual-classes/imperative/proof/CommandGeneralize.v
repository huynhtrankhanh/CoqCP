From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps CommandDispatch ReplyOK ReplyNO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandGeneralizeExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments value := update (fun _ => 0) vardef_0__generalize_theorem value.
Definition after (f : Frame) readstate final value :=
  setMachine (setNum (setMachine f readstate) vardef_0__command_a value) final.
Local Opaque funcdef_0__generalize funcdef_0__no.
Theorem generated_handler reader (f : Frame) readstate final value observations after_observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = value -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  value < meta_value readstate 3 ->
  execObserved (funcdef_0__generalize (fun _ => false) (arguments value)) (readstate,observations) = Some (tt,(final,after_observations)) ->
  execLocalObserved (CommandStructure.handler_13 reader) (f,observations) = Some (tt,(after f readstate final value,after_observations)).
Proof.
  intros Hreader Hinitial Hinitialerror Hmeta Hnumber Hvalid Herror Hreference Hgeneralize.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_13.
  repeat first [progress cbn [optionBind fst snd]
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(readstate,observations))) by exact Hreader;
        rewrite Hread; clear Hread end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__generalize ?bg ?ng) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__generalize bg ng) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(final,after_observations))) by exact Hgeneralize;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |match goal with |- context [meta_value s 8] => progress rewrite Hinitialerror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold after. reflexivity.
Qed.
Theorem generated_command s bs ns opcode_state argument_state final value observations after_observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(opcode_state,observations)) ->
  (17 < length (memory opcode_state arraydef_0__meta))%nat ->
  meta_value opcode_state 11 = 13 -> meta_value opcode_state 14 = 1 -> meta_value opcode_state 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opcode_state,observations) = Some (tt,(argument_state,observations)) ->
  (17 < length (memory argument_state arraydef_0__meta))%nat ->
  meta_value argument_state 11 = value -> meta_value argument_state 14 = 1 -> meta_value argument_state 8 = 0 ->
  value < meta_value argument_state 3 ->
  execObserved (funcdef_0__generalize (fun _ => false) (arguments value)) (argument_state,observations) = Some (tt,(final,after_observations)) ->
  (8 < length (memory final arraydef_0__meta))%nat -> meta_value final 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,after_observations)).
Proof.
  intros Hopcode Hmeta Hnumber Hvalid Herror Hargument Hargmeta Ha Hargvalid Hargerror Hreference Hgeneralize Hpostmeta Hposterror.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opcode_state 13).
  set (finalframe := after initial argument_state final value).
  apply (CommandDispatch.generated_positive_command s bs ns finalframe opcode_state 13 observations after_observations); try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_13 funcdef_0__readNat) (initial,observations) = Some (tt,(finalframe,after_observations))).
    now apply generated_handler.
Qed.
Definition rejected_frame (f : Frame) readstate value :=
  setMachine (setNum (setMachine f readstate) vardef_0__command_a value) (ReplyNOExecution.reply_state readstate).
Theorem generated_rejected_handler reader (f : Frame) readstate value observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = value -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  meta_value readstate 3 <= value ->
  execLocalObserved (CommandStructure.handler_13 reader) (f,observations) =
    Some (tt,(rejected_frame f readstate value,
      observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hinitial Hinitialerror Hmeta Hnumber Hvalid Herror Hreference.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_13.
  repeat first [progress cbn [optionBind fst snd]
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(readstate,observations))) by exact Hreader;
        rewrite Hread; clear Hread end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bn ?nn) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__no bn nn) (current,trace)) in
        let Hno := fresh "Hno" in assert (Hno : expression = Some (tt,(ReplyNOExecution.reply_state current,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
          (exact (ReplyNOExecution.generated_no current bn nn trace)); rewrite Hno; clear Hno end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |match goal with |- context [meta_value s 8] => progress rewrite Hinitialerror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold rejected_frame. reflexivity.
Qed.
Theorem generated_rejected_command s bs ns opcode_state argument_state value observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(opcode_state,observations)) ->
  (17 < length (memory opcode_state arraydef_0__meta))%nat ->
  meta_value opcode_state 11 = 13 -> meta_value opcode_state 14 = 1 -> meta_value opcode_state 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opcode_state,observations) = Some (tt,(argument_state,observations)) ->
  (17 < length (memory argument_state arraydef_0__meta))%nat ->
  meta_value argument_state 11 = value -> meta_value argument_state 14 = 1 -> meta_value argument_state 8 = 0 ->
  meta_value argument_state 3 <= value ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(ReplyNOExecution.reply_state argument_state,
      observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin argument_state|}])).
Proof.
  intros Hopcode Hmeta Hnumber Hvalid Herror Hargument Haftermeta Ha Haftervalid Haftererror Hreference.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opcode_state 13).
  set (after := rejected_frame initial argument_state value).
  apply (CommandDispatch.generated_positive_command s bs ns after opcode_state 13 observations
    (observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin argument_state|}]));
    try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_13 funcdef_0__readNat) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin argument_state|}]))).
    now apply generated_rejected_handler.
  - change (8 < length (memory argument_state arraydef_0__meta))%nat. lia.
Qed.
End CommandGeneralizeExecution.
