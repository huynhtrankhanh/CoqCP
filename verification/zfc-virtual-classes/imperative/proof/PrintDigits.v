From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash TokenByte InternTail ObservedLocal PrintTranslation DecimalInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module PrintDigitsExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0_PrintInt64_unsigned.
Definition SourceAction R := Action (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue R.
Ltac print_callbacks code use :=
  lazymatch code with bind (bind _ ?branch) _ =>
    let code := eval cbn beta iota in (branch false) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind (bind _ ?digits) ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind (bind _ ?output) _ => use digits output end
      end
    end
  end.
Definition source_digits (total : Z) : SourceAction unit := ltac:(
  let code := eval unfold funcdef_0_PrintInt64_unsigned_body in funcdef_0_PrintInt64_unsigned_body in
  print_callbacks code ltac:(fun digits output => exact (digits total))).
Definition source_digit remaining : SourceAction LoopOutcome := ltac:(
  let code := eval unfold source_digits in (source_digits 20) in
  let code := eval cbn beta in code in
  lazymatch code with loop _ ?body => exact (body remaining) end).
Definition native_digit remaining := PrintTranslation.local_translate (source_digit remaining).
Definition put_digit (s : Machine) index ch := withMemory s (modifyArray (memory s) arraydef_0__printBuffer index ch).
Definition digit_frame (f : Frame) value index :=
  let ch := value mod 10 + 48 in
  let temp := setNum f vardef_0_PrintInt64_unsigned_tmpChar ch in
  let written := setMachine temp (put_digit (machine temp) index ch) in
  let divided := setNum written vardef_0_PrintInt64_unsigned_num (value/10) in
  setNum divided vardef_0_PrintInt64_unsigned_i (Z.of_nat (S index)).
Theorem generated_extract_digit (f : Frame) remaining value index observations :
  nums f vardef_0_PrintInt64_unsigned_num = value -> nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat index ->
  0 < value <= maximum -> (index < 20)%nat ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (native_digit remaining) (f,observations) = Some (KeepGoing,(digit_frame f value index,observations)).
Proof.
  intros Hvalue Hindex Hword Hbound Hbuffer.
  assert (Hmod : 0 <= value mod 10 < 10) by (apply Z.mod_pos_bound; lia).
  assert (Hbyte : coerceInt (value mod 10 + 48) 8 = value mod 10 + 48) by (apply TokenByteExecution.byte_coerce; lia).
  assert (Hchar : coerceInt (value mod 10 + 48) 64 = value mod 10 + 48) by (apply coerce_word; unfold word, maximum; lia).
  assert (Hnext : coerceInt (Z.of_nat index + 1) 64 = Z.of_nat (S index)).
  { replace (Z.of_nat index+1) with (Z.of_nat (S index)) by lia. apply coerce_word. unfold word, maximum. lia. }
  destruct f as [s bs ns]. cbn [nums machine] in *.
  unfold native_digit, source_digit.
  repeat first [rewrite Hvalue |rewrite Hindex |rewrite Hchar |rewrite Hbyte |rewrite Hnext |rewrite Nat2Z.id
    |rewrite nth_lt_default with (default := 0%Z)
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by lia |rewrite (bool_decide_false P) by lia] end
    |match goal with |- context [decide ?P] => first
       [rewrite (decide_True (P := P)) by (try congruence; lia) |rewrite (decide_False (P := P)) by (try congruence; lia)] end
    |progress cbv beta iota zeta delta [PrintTranslation.local_translate Action_rect bind dropWithinLoop liftToWithinLoop
      addInt modIntUnsigned divIntUnsigned numberLocalGet numberLocalSet store
      execLocalObserved localStepObserved observedStep step optionBind fst snd machine setMachine setNum nums bools Imperative.update]
  ].
  unfold digit_frame, put_digit. reflexivity.
Qed.

Theorem generated_extract_zero (f : Frame) remaining observations :
  nums f vardef_0_PrintInt64_unsigned_num = 0 ->
  execLocalObserved (native_digit remaining) (f,observations) = Some (Stop,(f,observations)).
Proof.
  intro Hzero. destruct f as [s bs ns]. cbn [nums] in Hzero. unfold native_digit, source_digit.
  repeat first [rewrite Hzero |rewrite bool_decide_true by reflexivity
    |progress cbv beta iota zeta delta [PrintTranslation.local_translate Action_rect bind dropWithinLoop liftToWithinLoop
      numberLocalGet execLocalObserved localStepObserved optionBind fst snd nums]]; reflexivity.
Qed.
Lemma digit_num f value index : nums (digit_frame f value index) vardef_0_PrintInt64_unsigned_num = value/10.
Proof. reflexivity. Qed.
Lemma digit_index f value index : nums (digit_frame f value index) vardef_0_PrintInt64_unsigned_i = Z.of_nat (S index).
Proof. reflexivity. Qed.
Lemma digit_buffer f value index : memory (machine (digit_frame f value index)) arraydef_0__printBuffer =
  <[index := value mod 10 + 48]> (memory (machine f) arraydef_0__printBuffer).
Proof. unfold digit_frame, put_digit. cbn [setNum setMachine machine withMemory memory]. apply InternTailExecution.modify_same. Qed.
Lemma digit_buffer_length f value index : length (memory (machine (digit_frame f value index)) arraydef_0__printBuffer) =
  length (memory (machine f) arraydef_0__printBuffer).
Proof. rewrite digit_buffer. apply length_insert. Qed.
Fixpoint filled (f : Frame) value index fuel := match fuel with
| O => f | S fuel => if decide (value = 0) then f else filled (digit_frame f value index) (value/10) (S index) fuel end.
Theorem generated_digit_loop fuel (f : Frame) value index observations :
  nums f vardef_0_PrintInt64_unsigned_num = value -> nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat index ->
  0 <= value <= maximum -> (index + fuel <= 20)%nat ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (loop fuel native_digit) (f,observations) = Some (tt,(filled f value index fuel,observations)).
Proof.
  induction fuel as [|fuel IH] in f, value, index |- *; [reflexivity|].
  intros Hvalue Hindex Hword Hbound Hbuffer. rewrite loop_S, local_bind. cbn [filled].
  case_decide as Hz.
  - rewrite Hz in Hvalue. rewrite (generated_extract_zero f fuel observations Hvalue). reflexivity.
  - rewrite (generated_extract_digit f fuel value index observations Hvalue Hindex ltac:(lia) ltac:(lia) Hbuffer).
    cbn [optionBind fst snd]. apply IH.
    + apply digit_num.
    + apply digit_index.
    + split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; unfold maximum in *; lia.
    + lia.
    + now rewrite digit_buffer_length.
Qed.
Lemma source_digits_loop : source_digits 20 = loop 20 source_digit.
Proof. reflexivity. Qed.
Theorem generated_translated_digits (f : Frame) value index observations :
  nums f vardef_0_PrintInt64_unsigned_num = value -> nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat index ->
  0 <= value <= maximum -> (index + 20 <= 20)%nat ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  execLocalObserved (PrintTranslation.local_translate (source_digits 20)) (f,observations) =
    Some (tt,(filled f value index 20,observations)).
Proof. intros Hvalue Hindex Hword Hbound Hbuffer. rewrite source_digits_loop, PrintTranslation.local_loop_correct.
  now apply generated_digit_loop. Qed.

Lemma filled_index fuel (f : Frame) value index :
  nums f vardef_0_PrintInt64_unsigned_i = Z.of_nat index ->
  nums (filled f value index fuel) vardef_0_PrintInt64_unsigned_i = Z.of_nat (index + length (littleDigits fuel value)).
Proof.
  induction fuel as [|fuel IH] in f, value, index |- *.
  - cbn [filled littleDigits length]. now rewrite Nat.add_0_r.
  - intro Hindex. cbn [filled littleDigits]. case_decide.
    + now rewrite Nat.add_0_r.
    + rewrite IH by apply digit_index. cbn [length]. f_equal. lia.
Qed.
Lemma filled_zero fuel (f : Frame) value index :
  nums f vardef_0_PrintInt64_unsigned_num = value -> 0 <= value < DecimalInput.radix fuel ->
  nums (filled f value index fuel) vardef_0_PrintInt64_unsigned_num = 0.
Proof.
  induction fuel as [|fuel IH] in f, value, index |- *.
  - intros Hvalue Hbound. cbn [DecimalInput.radix] in Hbound. cbn [filled]. rewrite Hvalue. lia.
  - intros Hvalue Hbound. cbn [filled]. case_decide as Hz.
    + now rewrite Hvalue, Hz.
    + apply IH; [apply digit_num|]. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; cbn [DecimalInput.radix] in Hbound; lia.
Qed.
Fixpoint buffer_write (buffer : list Z) index chars := match chars with
| [] => buffer | ch :: chars => buffer_write (<[index := ch]> buffer) (S index) chars end.
Lemma buffer_write_length buffer index chars : length (buffer_write buffer index chars) = length buffer.
Proof. induction chars as [|ch chars IH] in buffer, index |- *; [reflexivity|]. cbn [buffer_write]. now rewrite IH, length_insert. Qed.
Lemma filled_buffer fuel (f : Frame) value index :
  memory (machine (filled f value index fuel)) arraydef_0__printBuffer =
    buffer_write (memory (machine f) arraydef_0__printBuffer) index (littleDigits fuel value).
Proof.
  induction fuel as [|fuel IH] in f, value, index |- *; [reflexivity|].
  cbn [filled littleDigits]. case_decide; [reflexivity|]. cbn [buffer_write]. rewrite IH, digit_buffer. reflexivity.
Qed.
Lemma buffer_write_before buffer index chars i : (i < index)%nat ->
  List.nth i (buffer_write buffer index chars) 0 = List.nth i buffer 0.
Proof.
  induction chars as [|ch chars IH] in buffer, index |- *; [reflexivity|].
  intro Hi. cbn [buffer_write]. rewrite IH by lia. apply ArrayFacts.nth_insert_other. lia.
Qed.
Lemma buffer_write_entry buffer index chars i : (i < length chars)%nat ->
  (index + length chars <= length buffer)%nat ->
  List.nth (index+i) (buffer_write buffer index chars) 0 = List.nth i chars 0.
Proof.
  induction chars as [|ch chars IH] in buffer, index, i |- *; [cbn; lia|].
  intros Hi Hcapacity. destruct i as [|i].
  - cbn [buffer_write]. rewrite Nat.add_0_r, buffer_write_before by lia. apply OverflowExecution.nth_insert_same. cbn [length] in Hcapacity. lia.
  - cbn [buffer_write]. replace (index+S i)%nat with (S index+i)%nat by lia. rewrite IH; [reflexivity|cbn [length] in Hi; lia|].
    rewrite length_insert. cbn [length] in Hcapacity. lia.
Qed.
Lemma digit_io f value index : stdin (machine (digit_frame f value index)) = stdin (machine f) /\
  stdout (machine (digit_frame f value index)) = stdout (machine f).
Proof. split; reflexivity. Qed.
Lemma filled_io fuel (f : Frame) value index : stdin (machine (filled f value index fuel)) = stdin (machine f) /\
  stdout (machine (filled f value index fuel)) = stdout (machine f).
Proof.
  induction fuel as [|fuel IH] in f, value, index |- *; [split; reflexivity|].
  cbn [filled]. case_decide; [split; reflexivity|]. destruct (IH (digit_frame f value index) (value/10) (S index)) as [Hi Ho].
  destruct (digit_io f value index). split; congruence.
Qed.
End PrintDigitsExecution.


