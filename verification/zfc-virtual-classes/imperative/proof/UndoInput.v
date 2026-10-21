From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte CommandInput UndoEmpty UndoPositive ReplyNO ReplyOK ArenaFrame FormulaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module UndoInputExecution.
Import IndexExecution SipHashExecution.
Definition parsed s tail := CommandInput.parsed s 49 [54] tail.
Theorem generated_empty_pending s bs ns sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> meta_value s 3 = 0 ->
  TokenByteExecution.separator sep -> stdin s = 54 :: sep :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(ReplyNOExecution.reply_state (parsed s tail),
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hpending Herror Hhistory Hsep Hin.
  assert (Hword : Z.of_nat 16 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (CommandInput.generated_pending s (fun _ => false) (fun _ => 0) 16 49 [54] sep tail observations
    Hmeta Htoken Hpending Herror Hword eq_refl Hsep Hin) as Hreader.
  assert (Hrm : (17 < length (memory (parsed s tail) arraydef_0__meta))%nat).
  { unfold parsed. now rewrite CommandInput.parsed_meta_length. }
  assert (Hnumber : meta_value (parsed s tail) 11 = 16).
  { unfold parsed. exact (CommandInput.parsed_number s 16 49 [54] tail Hmeta Hword eq_refl). }
  assert (Hvalid : meta_value (parsed s tail) 14 = 1).
  { unfold parsed. now apply CommandInput.parsed_valid. }
  assert (Herr : meta_value (parsed s tail) 8 = 0).
  { unfold parsed. rewrite CommandInput.parsed_meta_other by lia. exact Herror. }
  assert (Hhist : meta_value (parsed s tail) 3 = 0).
  { unfold parsed. rewrite CommandInput.parsed_meta_other by lia. exact Hhistory. }
  pose proof (UndoEmptyExecution.generated_after_read s bs ns (parsed s tail) observations
    Hreader Hrm Hnumber Hvalid Herr Hhist) as Hrun.
  unfold parsed in Hrun. rewrite CommandInput.parsed_input, CommandInput.parsed_output in Hrun. exact Hrun.
Qed.
Theorem generated_positive_pending s bs ns count sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> meta_value s 3 = Z.of_nat (S count) ->
  Z.of_nat (S count) <= maximum -> TokenByteExecution.separator sep -> stdin s = 54 :: sep :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(UndoPositiveExecution.result (parsed s tail) count,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hhistory Hcount Hsep Hin.
  assert (Hword : Z.of_nat 16 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (CommandInput.generated_pending s (fun _ => false) (fun _ => 0) 16 49 [54] sep tail observations
    Hmeta Htoken Hpending Herror Hword eq_refl Hsep Hin) as Hreader.
  assert (Hrm : (17 < length (memory (parsed s tail) arraydef_0__meta))%nat).
  { unfold parsed. now rewrite CommandInput.parsed_meta_length. }
  assert (Hrb : (20 <= length (memory (parsed s tail) arraydef_0__printBuffer))%nat).
  { unfold parsed. rewrite CommandInput.parsed_other by discriminate. exact Hbuffer. }
  assert (Hnumber : meta_value (parsed s tail) 11 = 16).
  { unfold parsed. exact (CommandInput.parsed_number s 16 49 [54] tail Hmeta Hword eq_refl). }
  assert (Hvalid : meta_value (parsed s tail) 14 = 1).
  { unfold parsed. now apply CommandInput.parsed_valid. }
  assert (Herr : meta_value (parsed s tail) 8 = 0).
  { unfold parsed. rewrite CommandInput.parsed_meta_other by lia. exact Herror. }
  assert (Hhist : meta_value (parsed s tail) 3 = Z.of_nat (S count)).
  { unfold parsed. rewrite CommandInput.parsed_meta_other by lia. exact Hhistory. }
  pose proof (UndoPositiveExecution.generated_after_read s bs ns (parsed s tail) count observations
    Hreader Hrm Hrb Hnumber Hvalid Herr Hhist Hcount) as Hrun.
  unfold parsed in Hrun. rewrite CommandInput.parsed_input, CommandInput.parsed_output in Hrun. exact Hrun.
Qed.
Definition reply count := match count with O => Protocol.NO | S n => Protocol.OK n end.
Definition result s tail count := match count with
  | O => ReplyNOExecution.reply_state (parsed s tail)
  | S n => UndoPositiveExecution.result (parsed s tail) n
  end.
Theorem generated_pending s bs ns count sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> meta_value s 3 = Z.of_nat count ->
  Z.of_nat count <= maximum -> TokenByteExecution.separator sep -> stdin s = 54 :: sep :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(result s tail count,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (reply count); unreadInput := tail|}])).
Proof.
  destruct count as [|count]; cbn [reply result]; intros Hmeta Htoken Hbuffer Hpending Herror Hhistory Hword Hsep Hin.
  - exact (generated_empty_pending s bs ns sep tail observations Hmeta Htoken Hpending Herror Hhistory Hsep Hin).
  - exact (generated_positive_pending s bs ns count sep tail observations Hmeta Htoken Hbuffer Hpending Herror Hhistory Hword Hsep Hin).
Qed.
Lemma result_meta_length s tail count :
  length (memory (result s tail count) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof.
  destruct count as [|count].
  - exact (CommandInput.parsed_meta_length s 49 [54] tail).
  - change (length (memory (UndoPositiveExecution.result (parsed s tail) count) arraydef_0__meta) = length (memory s arraydef_0__meta)).
    rewrite UndoPositiveExecution.result_meta_length. exact (CommandInput.parsed_meta_length s 49 [54] tail).
Qed.
Lemma result_meta_other s tail count i : i <> 3%nat -> i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (result s tail count) i = meta_value s i.
Proof.
  intros H3 H6 H11 H14 H15 H17. destruct count as [|count].
  - exact (CommandInput.parsed_meta_other s 49 [54] tail i H6 H11 H14 H15 H17).
  - change (meta_value (UndoPositiveExecution.result (parsed s tail) count) i = meta_value s i).
    rewrite UndoPositiveExecution.result_meta, meta_store_other by exact H3.
    exact (CommandInput.parsed_meta_other s 49 [54] tail i H6 H11 H14 H15 H17).
Qed.
Lemma result_input s tail count : stdin (result s tail count) = tail.
Proof. destruct count as [|count]; [reflexivity|]. cbn [result]. unfold UndoPositiveExecution.result.
  rewrite ReplyOKExecution.reply_input. reflexivity. Qed.
Lemma result_output s tail count : stdout (result s tail count) = stdout s ++ Protocol.reply_bytes (reply count).
Proof. destruct count as [|count]; cbn [result reply].
  - change (stdout (parsed s tail) ++ Protocol.reply_bytes Protocol.NO = stdout s ++ Protocol.reply_bytes Protocol.NO).
    unfold parsed. now rewrite CommandInput.parsed_output.
  - unfold UndoPositiveExecution.result. rewrite ReplyOKExecution.reply_output.
    change (stdout (parsed s tail) ++ Protocol.reply_bytes (Protocol.OK count) = stdout s ++ Protocol.reply_bytes (Protocol.OK count)).
    unfold parsed. now rewrite CommandInput.parsed_output.
Qed.
Lemma result_history s tail count :
  (17 < length (memory s arraydef_0__meta))%nat -> meta_value s 3 = Z.of_nat count ->
  meta_value (result s tail count) 3 = Z.of_nat (Nat.pred count).
Proof.
  intros Hmeta Hhistory. destruct count as [|count]; cbn [result Nat.pred].
  - change (meta_value (CommandInput.parsed s 49 [54] tail) 3 = 0).
    rewrite CommandInput.parsed_meta_other by lia. exact Hhistory.
  - rewrite UndoPositiveExecution.result_meta. apply meta_store_same.
    unfold parsed. rewrite CommandInput.parsed_meta_length. lia.
Qed.
Lemma result_named_objects s tail count name : name <> arraydef_0__meta -> name <> arraydef_0__token -> name <> arraydef_0__printBuffer ->
  memory (result s tail count) name = memory s name.
Proof.
  intros Hm Ht Hp. destruct count as [|count].
  - exact (CommandInput.parsed_other s 49 [54] tail name Hm Ht).
  - change (memory (UndoPositiveExecution.result (parsed s tail) count) name = memory s name).
    unfold UndoPositiveExecution.result. rewrite ReplyOKExecution.reply_other by exact Hp.
    rewrite store_meta_other by exact Hm. exact (CommandInput.parsed_other s 49 [54] tail name Hm Ht).
Qed.
Lemma result_storage s tail count : FormulaFrame.storage s (result s tail count).
Proof.
  pose proof (CommandInput.parsed_storage s 49 [54] tail) as Hparsed.
  destruct count as [|count].
  - exact (FormulaFrame.strong_storage s (ReplyNOExecution.reply_state (parsed s tail))
      (ArenaFrame.storage_trans s (parsed s tail) (ReplyNOExecution.reply_state (parsed s tail))
        Hparsed (ArenaFrame.storage_output (parsed s tail) _))).
  - pose proof (ArenaFrame.storage_meta (parsed s tail) 3 (Z.of_nat count) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hstore.
    exact (FormulaFrame.storage_trans s (store_meta (parsed s tail) 3 (Z.of_nat count)) (result s tail (S count))
      (FormulaFrame.strong_storage _ _ (ArenaFrame.storage_trans _ _ _ Hparsed Hstore))
      (FormulaFrame.reply_storage _ count)).
Qed.
End UndoInputExecution.
