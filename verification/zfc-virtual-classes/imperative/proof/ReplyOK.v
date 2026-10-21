From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index Overflow SipHash ObservedLocal PrintingFrame PrintUnsigned.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ReplyOKExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ok) withLocalVariablesReturnValue R.
Definition prefix : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__ok_body in funcdef_0__ok_body in
  lazymatch code with bind ?first _ => exact first end).
Definition body : LocalAction unit :=
  prefix >>= fun _ =>
  (numberLocalGet _ _ _ vardef_0__ok_value >>= fun value =>
    liftToWithLocalVariables (PrintingFrame.translate_print
      (funcdef_0_PrintInt64_unsigned (fun _ => false) (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num value)))) >>= fun _ =>
  writeChar _ _ _ 10 >>= fun _ => flush _ _ _ >>= fun _ => Done _ _ _ tt.
Lemma actual_body : funcdef_0__ok_body = body.
Proof. reflexivity. Qed.
Definition prefix_state (s : Machine) := withOutput s (stdout s ++ [79;75;32]).
Definition format_state s value := PrintUnsignedExecution.result_state (prefix_state s) (fun _ => false)
  (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num (Z.of_nat value)) value.
Definition reply_state s value := withOutput (format_state s value) (stdout (format_state s value) ++ [10]).
Theorem generated_prefix (f : Frame) observations :
  execLocalObserved prefix (f,observations) = Some (tt,(setMachine f (prefix_state (machine f)),observations)).
Proof.
  destruct f as [[input output arrays] bs ns].
  cbv beta iota zeta delta [prefix loopString Action_rect dropWithinLoop liftToWithinLoop bind
    writeChar execLocalObserved localStepObserved observedStep step optionBind fst snd machine setMachine
    withOutput stdout stdin memory bools nums].
  unfold prefix_state. cbn [stdout machine withOutput setMachine]. repeat rewrite <-app_assoc. reflexivity.
Qed.
Theorem generated_body (f : Frame) value observations :
  nums f vardef_0__ok_value = Z.of_nat value -> Z.of_nat value <= maximum ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved funcdef_0__ok_body (f,observations) =
    Some (tt,(setMachine f (reply_state (machine f) value),
      observations ++ [{|flushedOutput := stdout (reply_state (machine f) value); unreadInput := stdin (reply_state (machine f) value)|}])).
Proof.
  intros Hvalue Hword Hbuffer. rewrite actual_body. unfold body. rewrite local_bind, generated_prefix.
  cbn [optionBind fst snd]. rewrite local_bind, local_bind.
  cbn [numberLocalGet execLocalObserved localStepObserved optionBind fst snd setMachine nums]. rewrite Hvalue.
  rewrite ObservedLocal.lift_correct. cbn [machine setMachine].
  pose proof (PrintUnsignedExecution.generated_unsigned (prefix_state (machine f)) (fun _ => false)
    (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num (Z.of_nat value)) value observations
    eq_refl Hword Hbuffer) as Hprint.
  unfold IndexExecution.Machine in Hprint |- *. rewrite Hprint.
  cbn [optionBind fst snd]. rewrite local_bind.
  destruct f as [s bs ns].
  cbn [writeChar flush execLocalObserved localStepObserved observedStep step optionBind fst snd setMachine machine bools nums withOutput stdout stdin].
  reflexivity.
Qed.
Lemma reply_input s value : stdin (reply_state s value) = stdin s.
Proof. unfold reply_state, format_state. change
  (stdin (PrintUnsignedExecution.result_state (prefix_state s) (fun _ => false)
    (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num (Z.of_nat value)) value) = stdin s).
  unfold PrintUnsignedExecution.result_state. rewrite PrintUnsignedExecution.printed_input. reflexivity. Qed.
Lemma reply_output s value : stdout (reply_state s value) = stdout s ++ Protocol.reply_bytes (Protocol.OK value).
Proof.
  unfold reply_state, format_state. cbn [withOutput stdout].
  unfold PrintUnsignedExecution.result_state. rewrite PrintUnsignedExecution.printed_output.
  unfold prefix_state. cbn [withOutput machine stdout Protocol.reply_bytes]. repeat rewrite <-app_assoc. reflexivity.
Qed.
Lemma reply_other s value name : name <> arraydef_0__printBuffer -> memory (reply_state s value) name = memory s name.
Proof. intro Hname. unfold reply_state, format_state. change
  (memory (PrintUnsignedExecution.result_state (prefix_state s) (fun _ => false)
    (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num (Z.of_nat value)) value) name = memory s name).
  unfold PrintUnsignedExecution.result_state. rewrite PrintUnsignedExecution.printed_other by exact Hname. reflexivity. Qed.
Lemma reply_buffer_length s value :
  length (memory (reply_state s value) arraydef_0__printBuffer) = length (memory s arraydef_0__printBuffer).
Proof. unfold reply_state, format_state. change
  (length (memory (PrintUnsignedExecution.result_state (prefix_state s) (fun _ => false)
    (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num (Z.of_nat value)) value) arraydef_0__printBuffer) =
    length (memory s arraydef_0__printBuffer)).
  unfold PrintUnsignedExecution.result_state. rewrite PrintUnsignedExecution.printed_buffer_length. reflexivity. Qed.
Theorem generated_ok s bs ns value observations :
  ns vardef_0__ok_value = Z.of_nat value -> Z.of_nat value <= maximum ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  execObserved (funcdef_0__ok bs ns) (s,observations) = Some (tt,(reply_state s value,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin s|}])).
Proof.
  intros Hvalue Hword Hbuffer. unfold funcdef_0__ok. rewrite ObservedLocal.eliminate_correct.
  pose proof (generated_body {|machine := s; bools := bs; nums := ns|} value observations Hvalue Hword Hbuffer) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. cbn [optionBind fst snd machine setMachine].
  rewrite reply_input, reply_output. reflexivity.
Qed.
Theorem generated_ok_protocol s bs ns value observations :
  ns vardef_0__ok_value = Z.of_nat value -> Z.of_nat value <= maximum ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  exists final, execObserved (funcdef_0__ok bs ns) (s,observations) = Some (tt,(final,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin s|}])) /\
    stdin final = stdin s /\ stdout final = stdout s ++ Protocol.reply_bytes (Protocol.OK value) /\
    length (memory final arraydef_0__printBuffer) = length (memory s arraydef_0__printBuffer) /\
    (forall name, name <> arraydef_0__printBuffer -> memory final name = memory s name).
Proof.
  intros Hvalue Hword Hbuffer. exists (reply_state s value). split; [now apply generated_ok|].
  split; [apply reply_input|]. split; [apply reply_output|]. split; [apply reply_buffer_length|].
  intros name Hname. now apply reply_other.
Qed.
End ReplyOKExecution.
