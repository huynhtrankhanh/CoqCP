From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash TokenByte InternTail ObservedLocal PrintTranslation PrintDigits DecimalInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module PrintOutputExecution.
Import IndexExecution SipHashExecution ObservedLocal PrintDigitsExecution.
Definition source_output (total : Z) : SourceAction unit := ltac:(
  let code := eval unfold funcdef_0_PrintInt64_unsigned_body in funcdef_0_PrintInt64_unsigned_body in
  print_callbacks code ltac:(fun digits output => exact (output total))).
Definition source_output_step total remaining : SourceAction LoopOutcome := ltac:(
  let code := eval unfold source_output in (source_output total) in
  let code := eval cbn beta in code in
  lazymatch code with loop _ ?body => exact (body remaining) end).
Definition native_output_step total remaining := PrintTranslation.local_translate (source_output_step total remaining).
Definition output_frame (f : Frame) bytes := setMachine f (withOutput (machine f) (stdout (machine f) ++ bytes)).

Theorem generated_output_step (f : Frame) count remaining observations :
  nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat count ->
  (remaining < count <= 20)%nat ->
  (count <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (native_output_step (Z.of_nat count) remaining) (f,observations) =
    Some (KeepGoing,(output_frame f [List.nth remaining (memory (machine f) arraydef_0__printBuffer) 0],observations)).
Proof.
  intros Hindex Hbound Hbuffer.
  assert (Hfirst : coerceInt (Z.of_nat count - (Z.of_nat count - Z.of_nat remaining - 1)) 64 = Z.of_nat (S remaining)).
  { replace (Z.of_nat count - (Z.of_nat count - Z.of_nat remaining - 1)) with (Z.of_nat (S remaining)) by lia.
    apply coerce_word. unfold word, maximum. lia. }
  assert (Hsecond : coerceInt (Z.of_nat (S remaining)-1) 64 = Z.of_nat remaining).
  { replace (Z.of_nat (S remaining)-1) with (Z.of_nat remaining) by lia. apply coerce_word. unfold word, maximum. lia. }
  destruct f as [s bs ns]. cbn [nums machine] in *.
  unfold native_output_step, source_output_step.
  repeat first [rewrite Hindex |rewrite Hfirst |rewrite Hsecond |rewrite Nat2Z.id
    |rewrite nth_lt_default with (default := 0%Z)
    |match goal with |- context [decide ?P] => first
       [rewrite (decide_True (P := P)) by (try congruence; lia) |rewrite (decide_False (P := P)) by (try congruence; lia)] end
    |progress cbv beta iota zeta delta [PrintTranslation.local_translate Action_rect bind dropWithinLoop liftToWithinLoop
      subInt numberLocalGet retrieve writeChar execLocalObserved localStepObserved observedStep step
      optionBind fst snd machine setMachine nums bools]
  ].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
  cbn [optionBind fst snd setMachine machine nums bools]. unfold output_frame. reflexivity.
Qed.
Fixpoint emit (buffer : list Z) fuel := match fuel with
| O => [] | S fuel => List.nth fuel buffer 0 :: emit buffer fuel end.
Lemma output_nil f : output_frame f [] = f.
Proof. destruct f as [[input output arrays] bs ns]. unfold output_frame. cbn [machine stdout withOutput setMachine]. now rewrite app_nil_r. Qed.
Lemma output_app f a b : output_frame (output_frame f a) b = output_frame f (a++b).
Proof. destruct f as [[input output arrays] bs ns]. unfold output_frame. cbn [machine stdout withOutput setMachine]. now rewrite app_assoc. Qed.
Lemma output_index f bytes : nums (output_frame f bytes) vardef_0_PrintInt64_unsigned_i = nums f vardef_0_PrintInt64_unsigned_i.
Proof. reflexivity. Qed.
Lemma output_buffer f bytes : memory (machine (output_frame f bytes)) arraydef_0__printBuffer = memory (machine f) arraydef_0__printBuffer.
Proof. reflexivity. Qed.
Theorem generated_output_loop fuel count (f : Frame) observations :
  nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat count -> (fuel <= count <= 20)%nat ->
  (count <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (loop fuel (native_output_step (Z.of_nat count))) (f,observations) =
    Some (tt,(output_frame f (emit (memory (machine f) arraydef_0__printBuffer) fuel),observations)).
Proof.
  induction fuel as [|fuel IH] in f |- *.
  - intros. cbn [loop emit execLocalObserved]. now rewrite output_nil.
  - intros Hindex Hbound Hbuffer. rewrite loop_S, local_bind.
    rewrite generated_output_step by assumption || lia.
    cbn [optionBind fst snd]. rewrite IH by (try rewrite output_index; try rewrite output_buffer; try assumption; lia).
    rewrite output_buffer, output_app. reflexivity.
Qed.
Lemma source_output_loop count : source_output (Z.of_nat count) = loop count (source_output_step (Z.of_nat count)).
Proof. unfold source_output, source_output_step. now rewrite Nat2Z.id. Qed.
Theorem generated_translated_output count (f : Frame) observations :
  nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat count -> (count <= 20)%nat ->
  (count <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (PrintTranslation.local_translate (source_output (Z.of_nat count))) (f,observations) =
    Some (tt,(output_frame f (emit (memory (machine f) arraydef_0__printBuffer) count),observations)).
Proof. intros Hindex Hbound Hbuffer. rewrite source_output_loop, PrintTranslation.local_loop_correct.
  apply generated_output_loop; assumption || lia. Qed.
Lemma emit_take buffer fuel : (fuel <= length buffer)%nat -> emit buffer fuel = reverse (take fuel buffer).
Proof.
  induction fuel as [|fuel IH]; [reflexivity|]. intro Hlength. cbn [emit].
  destruct (nth_lookup_or_length buffer fuel 0) as [Hlookup|Hbad]; [|lia].
  rewrite (take_S_r buffer fuel _ Hlookup), reverse_app, reverse_singleton, <-IH by lia. reflexivity.
Qed.
Lemma take_written buffer chars : (length chars <= length buffer)%nat ->
  take (length chars) (buffer_write buffer 0 chars) = chars.
Proof.
  intro Hlength. apply (list_eq_same_length _ _ (length chars)).
  - reflexivity.
  - rewrite length_take, buffer_write_length. lia.
  - intros i x y Hi Hx Hy.
    destruct (nth_lookup_or_length (buffer_write buffer 0 chars) i 0) as [Hb|Hb]; [|rewrite buffer_write_length in Hb; lia].
    destruct (nth_lookup_or_length chars i 0) as [Hc|Hc]; [|lia].
    rewrite lookup_take_lt in Hx by lia. rewrite Hb in Hx. rewrite Hc in Hy.
    injection Hx as <-. injection Hy as <-. apply (buffer_write_entry buffer 0 chars i); assumption.
Qed.
Lemma emit_written buffer chars : (length chars <= length buffer)%nat ->
  emit (buffer_write buffer 0 chars) (length chars) = reverse chars.
Proof. intro Hlength. rewrite emit_take by (rewrite buffer_write_length; lia). now rewrite take_written. Qed.
End PrintOutputExecution.
