From CoqCP Require Import Options Imperative Execution InteractiveExecution ArrayExecution.
From Submission Require Import KthHighestScoreIO KthHighestScorePrinter KthHighestScoreProgram.
From Generated Require Import KthHighestScore.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Lemma char_NoFlush : NoFlush (@charAction arrayIndex2 (arrayType _ environment2)).
Proof. cbn [charAction NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma output_NoFlush c : NoFlush (@outputChar arrayIndex2 (arrayType _ environment2) c).
Proof. cbn [outputChar NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma read_NoFlush (name : arrayIndex2) index : NoFlush (@readArray arrayIndex2 (arrayType _ environment2) name index).
Proof. cbn [readArray NoFlush isFlush]. split; [tauto | intros; constructor]. Qed.
Lemma write_NoFlush (name : arrayIndex2) index value : NoFlush (@writeArray arrayIndex2 (arrayType _ environment2) name index value).
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
  change (NoFlush (@writeArray arrayIndex2 (arrayType _ environment2) arraydef_0__input 0 value')). apply write_NoFlush.
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
