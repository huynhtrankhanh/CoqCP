From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps CommandDispatch ReplyOK ReplyNO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module FormulaAllExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments value := update (update (update (fun _ => 0) vardef_0__intern_tag 4) vardef_0__intern_a value) vardef_0__intern_b 0.
Definition frame_after (f : Frame) readstate internstate index value :=
  setMachine (setNum (setMachine f readstate) vardef_0__command_a value) (ReplyOKExecution.reply_state internstate index).
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern.
Theorem generated_handler reader (f : Frame) readstate internstate index value observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = value -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  value < meta_value readstate 1 ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments value)) (readstate,observations) = Some (tt,(internstate,observations)) ->
  (17 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 0 = Z.of_nat index -> Z.of_nat index <= maximum ->
  execLocalObserved (CommandStructure.handler_4 reader) (f,observations) = Some (tt,(frame_after f readstate internstate index value,
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}])).
Proof.
  intros Hreader Hinitial Hinitialerror Hmeta Hnumber Hvalid Herror Hreference Hintern Hpostmeta Hbuffer Hposterror Hresult Hword.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_4.
  repeat first [progress cbn [optionBind fst snd]
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hpostmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(readstate,observations))) by exact Hreader;
        rewrite Hread; clear Hread end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
        let Hi := fresh "Hi" in assert (Hi : expression = Some (tt,(internstate,observations))) by exact Hintern;
        rewrite Hi; clear Hi end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__ok bo no) (current,trace)) in
        let Hok := fresh "Hok" in assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current index,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin current|}]))) by
          (apply (ReplyOKExecution.generated_ok current bo no index trace); [reflexivity|exact Hword|exact Hbuffer]);
        rewrite Hok; clear Hok end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |match goal with |- context [meta_value internstate 8] => progress rewrite Hposterror end
    |match goal with |- context [meta_value internstate 0] => progress rewrite Hresult end
    |match goal with |- context [meta_value s 8] => progress rewrite Hinitialerror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold frame_after. reflexivity.
Qed.
Theorem generated_command s bs ns opcode_state argument_state internstate index value observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(opcode_state,observations)) ->
  (17 < length (memory opcode_state arraydef_0__meta))%nat ->
  meta_value opcode_state 11 = 4 -> meta_value opcode_state 14 = 1 -> meta_value opcode_state 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opcode_state,observations) = Some (tt,(argument_state,observations)) ->
  (17 < length (memory argument_state arraydef_0__meta))%nat ->
  meta_value argument_state 11 = value -> meta_value argument_state 14 = 1 -> meta_value argument_state 8 = 0 ->
  value < meta_value argument_state 1 ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments value)) (argument_state,observations) = Some (tt,(internstate,observations)) ->
  (17 < length (memory internstate arraydef_0__meta))%nat ->
  (20 <= length (memory internstate arraydef_0__printBuffer))%nat ->
  meta_value internstate 8 = 0 -> meta_value internstate 0 = Z.of_nat index -> Z.of_nat index <= maximum ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(ReplyOKExecution.reply_state internstate index,
    observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}])).
Proof.
  intros Hopcode Hmeta Hnumber Hvalid Herror Hargument Hargmeta Ha Hargvalid Hargerror Hreference Hintern Hpostmeta Hbuffer Hposterror Hresult Hword.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opcode_state 4).
  set (after := frame_after initial argument_state internstate index value).
  apply (CommandDispatch.generated_positive_command s bs ns after opcode_state 4 observations
    (observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}]));
    try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_4 funcdef_0__readNat) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout internstate ++ Protocol.reply_bytes (Protocol.OK index); unreadInput := stdin internstate|}]))).
    now apply generated_handler.
  - change (8 < length (memory (ReplyOKExecution.reply_state internstate index) arraydef_0__meta))%nat.
    rewrite ReplyOKExecution.reply_other by discriminate. lia.
  - change (meta_value (ReplyOKExecution.reply_state internstate index) 8 = 0).
    unfold meta_value. rewrite ReplyOKExecution.reply_other by discriminate. exact Hposterror.
Qed.
Definition rejected_frame (f : Frame) readstate value :=
  setMachine (setNum (setMachine f readstate) vardef_0__command_a value) (ReplyNOExecution.reply_state readstate).
Theorem generated_rejected_handler reader (f : Frame) readstate value observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = value -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  meta_value readstate 1 <= value ->
  execLocalObserved (CommandStructure.handler_4 reader) (f,observations) =
    Some (tt,(rejected_frame f readstate value,
      observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hinitial Hinitialerror Hmeta Hnumber Hvalid Herror Hreference.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_4.
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
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
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
  meta_value opcode_state 11 = 4 -> meta_value opcode_state 14 = 1 -> meta_value opcode_state 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opcode_state,observations) = Some (tt,(argument_state,observations)) ->
  (17 < length (memory argument_state arraydef_0__meta))%nat ->
  meta_value argument_state 11 = value -> meta_value argument_state 14 = 1 -> meta_value argument_state 8 = 0 ->
  meta_value argument_state 1 <= value ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(ReplyNOExecution.reply_state argument_state,
      observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin argument_state|}])).
Proof.
  intros Hopcode Hmeta Hnumber Hvalid Herror Hargument Haftermeta Ha Haftervalid Haftererror Hreference.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opcode_state 4).
  set (after := rejected_frame initial argument_state value).
  apply (CommandDispatch.generated_positive_command s bs ns after opcode_state 4 observations
    (observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin argument_state|}]));
    try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_4 funcdef_0__readNat) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin argument_state|}]))).
    now apply generated_rejected_handler.
  - change (8 < length (memory argument_state arraydef_0__meta))%nat. lia.
Qed.
End FormulaAllExecution.
