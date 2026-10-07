(* Lift component execution proofs across the flush-observing interpreter. *)
From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Submission Require Import PermutedBinaryStringsCode PermutedBinaryStringsIO PermutedBinaryStringsPrinter PermutedBinaryStringsProgram.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Lemma char_NoFlush : NoFlush (@charAction arrayIndex2 (arrayType _ environment2)).
Proof. cbn [charAction NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma output_NoFlush c : NoFlush (@outputChar arrayIndex2 (arrayType _ environment2) c).
Proof. cbn [outputChar NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma read_NoFlush name index : NoFlush (readArray name index).
Proof. cbn [readArray NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma write_NoFlush name index value : NoFlush (writeArray name index value).
Proof. cbn [writeArray NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma readFirst_NoFlush fuel value c : NoFlush (@readFirst arrayIndex2 (arrayType _ environment2) fuel value c).
Proof.
  induction fuel as [| fuel IH] in value, c |- *; [constructor |].
  cbn [readFirst]. apply NoFlush_bind; [apply char_NoFlush |].
  intro digit. destruct (invalidDigit digit); [apply IH | constructor].
Qed.
Lemma readRest_NoFlush fuel value c : NoFlush (@readRest arrayIndex2 (arrayType _ environment2) fuel value c).
Proof.
  induction fuel as [| fuel IH] in value, c |- *; [constructor |].
  cbn [readRest]. apply NoFlush_bind; [apply char_NoFlush |].
  intro digit. destruct (invalidDigit digit); [constructor | apply IH].
Qed.
Lemma reader_NoFlush : NoFlush mappedReader.
Proof.
  rewrite mappedReaderNormalized. unfold readUnsignedAction.
  apply NoFlush_bind; [apply readFirst_NoFlush |]. intros [value c].
  apply NoFlush_bind; [apply readRest_NoFlush |]. intros [value' c'].
  change (NoFlush (writeArray arraydef_0__input 0 value')). apply write_NoFlush.
Qed.
Lemma readBinary_NoFlush fuel previous : NoFlush (readBinary fuel previous).
Proof.
  induction fuel as [| fuel IH] in previous |- *; [constructor |].
  cbn [readBinary]. apply NoFlush_bind; [apply char_NoFlush |].
  intro c. destruct (binaryChar c); [constructor | apply IH].
Qed.
Lemma bitReader_NoFlush : NoFlush bitReader.
Proof.
  rewrite bitReaderNormalized. apply NoFlush_bind; [apply readBinary_NoFlush |]. intro c. apply write_NoFlush.
Qed.
Lemma queryCall_NoFlush index weight : NoFlush (queryCall index weight).
Proof.
  unfold queryCall, funcdef_0__queryBit, funcdef_0__queryBit_body, queryNums,
    numberLocalGet, divIntUnsigned, modIntUnsigned, addInt, writeChar.
  normalize_pbs. destruct (decide (weight = 0)).
  - normalize_pbs. cbn [bind trap NoFlush isFlush]. split; [tauto | intros []].
  - normalize_pbs. destruct (decide (2 = 0)%Z) as [bad | good]; [lia |].
    normalize_pbs. cbn [bind NoFlush isFlush]. split; [tauto | intros []; constructor].
Qed.
Lemma recordCall_NoFlush index weight digit : NoFlush (recordCall index weight digit).
Proof.
  unfold recordCall, funcdef_0__recordBit, funcdef_0__recordBit_body, recordNums,
    numberLocalGet, addInt, subInt, multInt, retrieve, store.
  normalize_pbs. cbn [NoFlush isFlush]. split; [tauto |]. intro value.
  split; [tauto | intros; constructor].
Qed.
Lemma queryLoop_NoFlush n count weight : NoFlush (queryLoop n count weight).
Proof. unfold queryLoop. apply NoFlush_arrayLoop. intro index. apply queryCall_NoFlush. Qed.
Lemma receiveLoop_NoFlush n count weight : NoFlush (receiveLoop n count weight).
Proof.
  unfold receiveLoop. apply NoFlush_arrayLoop. intro index.
  apply NoFlush_bind; [apply bitReader_NoFlush |]. intros [].
  apply NoFlush_bind; [apply read_NoFlush |]. intro digit. apply recordCall_NoFlush.
Qed.
Lemma collect_NoFlush fuel value count c : NoFlush (mappedCollectDigits fuel value count c).
Proof.
  induction fuel as [| fuel IH] in value, count, c |- *; [constructor |].
  cbn [mappedCollectDigits]. destruct (bool_decide (value = 0)); [constructor |].
  cbn [NoFlush isFlush]. split; [tauto |]. intros []. apply IH.
Qed.
Lemma outputDigits_NoFlush count : NoFlush (mappedOutputDigits count).
Proof.
  unfold mappedOutputDigits. apply NoFlush_arrayLoop. intro index.
  cbn [NoFlush isFlush]. split; [tauto |]. intro digit. apply output_NoFlush.
Qed.
Lemma printer_NoFlush value : NoFlush (mappedPrinter value).
Proof.
  rewrite mappedPrinterNormalized. destruct (bool_decide (value = 0)); [apply output_NoFlush |].
  apply NoFlush_bind; [apply collect_NoFlush |]. intro nums. apply outputDigits_NoFlush.
Qed.
Lemma printLoop_NoFlush n count : NoFlush (printLoop n count).
Proof.
  unfold printLoop. apply NoFlush_arrayLoop. intro index.
  apply NoFlush_bind; [apply output_NoFlush |]. intros [].
  apply NoFlush_bind; [apply read_NoFlush |]. intro value. apply printer_NoFlush.
Qed.
