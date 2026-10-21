From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash TokenByte InternTail ObservedLocal PrintingFrame PrintTranslation PrintDigits PrintOutput DecimalInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module PrintUnsignedExecution.
Import IndexExecution SipHashExecution ObservedLocal PrintDigitsExecution PrintOutputExecution.
Definition source_with (digits output : Z -> SourceAction unit) : SourceAction unit :=
  ((numberLocalGet _ _ _ vardef_0_PrintInt64_unsigned_num >>= fun value =>
    Done _ _ _ (bool_decide (value = 0))) >>= fun zero =>
    if zero then writeChar _ _ _ 48 >>= fun _ => Done _ _ _ tt
    else numberLocalSet _ _ _ vardef_0_PrintInt64_unsigned_i 0 >>= fun _ =>
      digits 20 >>= fun _ =>
      (numberLocalGet _ _ _ vardef_0_PrintInt64_unsigned_i >>= output) >>= fun _ => Done _ _ _ tt)
  >>= fun _ => Done _ _ _ tt.
Lemma source_factorization : funcdef_0_PrintInt64_unsigned_body = source_with source_digits source_output.
Proof. reflexivity. Qed.

Lemma generated_condition (f : Frame) observations :
  execLocalObserved (PrintTranslation.local_translate
    (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned vardef_0_PrintInt64_unsigned_num
      >>= fun value => Done _ _ _ (bool_decide (value = 0)))) (f,observations) =
  Some (bool_decide (nums f vardef_0_PrintInt64_unsigned_num = 0),(f,observations)).
Proof. rewrite PrintTranslation.local_bind_correct. reflexivity. Qed.
Lemma generated_initialize (f : Frame) observations :
  execLocalObserved (PrintTranslation.local_translate
    (numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned vardef_0_PrintInt64_unsigned_i 0))
    (f,observations) = Some (tt,(setNum f vardef_0_PrintInt64_unsigned_i 0,observations)).
Proof. reflexivity. Qed.
Lemma generated_get_index (f : Frame) observations :
  execLocalObserved (PrintTranslation.local_translate
    (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned vardef_0_PrintInt64_unsigned_i))
    (f,observations) = Some (nums f vardef_0_PrintInt64_unsigned_i,(f,observations)).
Proof. reflexivity. Qed.

Theorem generated_source_zero (f : Frame) observations :
  nums f vardef_0_PrintInt64_unsigned_num = 0 ->
  execLocalObserved (PrintTranslation.local_translate funcdef_0_PrintInt64_unsigned_body) (f,observations) =
    Some (tt,(output_frame f [48],observations)).
Proof.
  intros Hzero. rewrite source_factorization. unfold source_with.
  repeat rewrite PrintTranslation.local_bind_correct.
  cbn [PrintTranslation.local_translate Action_rect execLocalObserved localStepObserved numberLocalGet
    optionBind fst snd]. rewrite Hzero, bool_decide_true by reflexivity.
  destruct f as [s bs ns]. reflexivity.
Qed.
Definition start_frame (f : Frame) := setNum f vardef_0_PrintInt64_unsigned_i 0.
Definition final_frame f value :=
  let written := filled (start_frame f) value 0 20 in
  output_frame written (reverse (littleDigits 20 value)).

Theorem generated_source_positive (f : Frame) value observations :
  nums f vardef_0_PrintInt64_unsigned_num = value -> 0 < value <= maximum ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (PrintTranslation.local_translate funcdef_0_PrintInt64_unsigned_body) (f,observations) =
    Some (tt,(final_frame f value,observations)).
Proof.
  intros Hvalue Hword Hbuffer. rewrite source_factorization. unfold source_with.
  rewrite PrintTranslation.local_bind_correct, PrintTranslation.local_bind_correct, generated_condition.
  cbn [optionBind fst snd]. rewrite Hvalue, bool_decide_false by lia.
  rewrite PrintTranslation.local_bind_correct, generated_initialize. cbn [optionBind fst snd].
  rewrite PrintTranslation.local_bind_correct.
  fold (start_frame f).
  assert (Hdigits := generated_translated_digits (start_frame f) value 0 observations
    ltac:(cbn [start_frame setNum nums Imperative.update]; assumption) eq_refl ltac:(lia) ltac:(lia) Hbuffer).
  unfold PrintDigitsExecution.Frame in Hdigits |- *. rewrite Hdigits.
  cbn [optionBind fst snd]. rewrite PrintTranslation.local_bind_correct, PrintTranslation.local_bind_correct, generated_get_index.
  cbn [optionBind fst snd].
  rewrite filled_index by reflexivity. cbn [Nat.add].
  rewrite generated_translated_output.
  2: { rewrite filled_index by reflexivity. reflexivity. }
  2: apply DecimalInput.little_length.
  2: { rewrite filled_buffer, buffer_write_length. eapply Nat.le_trans; [apply DecimalInput.little_length|exact Hbuffer]. }
  cbn [optionBind fst snd PrintTranslation.local_translate Action_rect execLocalObserved].
  unfold final_frame. rewrite filled_buffer, emit_written.
  - reflexivity.
  - eapply Nat.le_trans; [apply DecimalInput.little_length|exact Hbuffer].
Qed.
Definition printed_frame (f : Frame) value :=
  if decide (value = 0%nat) then output_frame f [48] else final_frame f (Z.of_nat value).
Theorem generated_source_unsigned (f : Frame) value observations :
  nums f vardef_0_PrintInt64_unsigned_num = Z.of_nat value -> Z.of_nat value <= maximum ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (PrintTranslation.local_translate funcdef_0_PrintInt64_unsigned_body) (f,observations) =
    Some (tt,(printed_frame f value,observations)).
Proof.
  intros Hvalue Hword Hbuffer. unfold printed_frame. case_decide as Hz.
  - subst value. apply generated_source_zero. exact Hvalue.
  - apply generated_source_positive; try assumption. lia.
Qed.
Lemma filled_other fuel (f : Frame) value index name : name <> arraydef_0__printBuffer ->
  memory (machine (filled f value index fuel)) name = memory (machine f) name.
Proof.
  intro Hname. induction fuel as [|fuel IH] in f, value, index |- *; [reflexivity|].
  cbn [filled]. case_decide; [reflexivity|]. rewrite IH.
  unfold digit_frame, put_digit. cbn [machine setMachine setNum memory withMemory].
  now apply PrintingFrame.modify_print_other.
Qed.
Lemma printed_input f value : stdin (machine (printed_frame f value)) = stdin (machine f).
Proof. unfold printed_frame, final_frame, output_frame. case_decide; [reflexivity|].
  cbn [machine setMachine withOutput stdin]. apply (proj1 (filled_io 20 (start_frame f) (Z.of_nat value) 0)). Qed.
Lemma printed_output f value : stdout (machine (printed_frame f value)) = stdout (machine f) ++ decimalBytes value.
Proof.
  unfold printed_frame, final_frame, output_frame, decimalBytes. case_decide; [reflexivity|].
  cbn [machine setMachine withOutput stdout]. rewrite (proj2 (filled_io 20 (start_frame f) (Z.of_nat value) 0)). reflexivity.
Qed.
Lemma printed_other f value name : name <> arraydef_0__printBuffer ->
  memory (machine (printed_frame f value)) name = memory (machine f) name.
Proof. intro Hname. unfold printed_frame, final_frame, output_frame. case_decide; [reflexivity|].
  cbn [machine setMachine withOutput memory]. rewrite filled_other by exact Hname. reflexivity. Qed.
Lemma printed_buffer_length f value :
  length (memory (machine (printed_frame f value)) arraydef_0__printBuffer) = length (memory (machine f) arraydef_0__printBuffer).
Proof. unfold printed_frame, final_frame, output_frame. case_decide; [reflexivity|].
  cbn [machine setMachine withOutput memory]. rewrite filled_buffer, buffer_write_length. reflexivity. Qed.
Definition result_state s bs ns value := machine (printed_frame {|machine := s; bools := bs; nums := ns|} value).
Theorem generated_unsigned s bs ns value observations :
  ns vardef_0_PrintInt64_unsigned_num = Z.of_nat value -> Z.of_nat value <= maximum ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  execObserved (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned bs ns)) (s,observations) =
    Some (tt,(result_state s bs ns value,observations)).
Proof.
  intros Hvalue Hword Hbuffer. unfold funcdef_0_PrintInt64_unsigned.
  rewrite PrintTranslation.eliminate_commutes, ObservedLocal.eliminate_correct.
  pose proof (generated_source_unsigned {|machine := s; bools := bs; nums := ns|} value observations Hvalue Hword Hbuffer) as Hrun.
  unfold PrintDigitsExecution.Frame in Hrun |- *. rewrite Hrun. reflexivity.
Qed.
Theorem generated_unsigned_protocol s bs ns value observations :
  ns vardef_0_PrintInt64_unsigned_num = Z.of_nat value -> Z.of_nat value <= maximum ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  exists final, execObserved (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned bs ns)) (s,observations) = Some (tt,(final,observations)) /\
    stdin final = stdin s /\ stdout final = stdout s ++ decimalBytes value /\
    length (memory final arraydef_0__printBuffer) = length (memory s arraydef_0__printBuffer) /\
    (forall name, name <> arraydef_0__printBuffer -> memory final name = memory s name).
Proof.
  intros Hvalue Hword Hbuffer. exists (result_state s bs ns value). split; [now apply generated_unsigned|].
  split; [apply printed_input|]. split; [apply printed_output|]. split; [apply printed_buffer_length|].
  intros name Hname. now apply printed_other.
Qed.
End PrintUnsignedExecution.
