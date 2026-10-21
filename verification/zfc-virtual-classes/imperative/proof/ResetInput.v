From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput ObservedLocal CommandQuit ReplyOK CommandReset TokenFrame ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ResetInputExecution.
Import IndexExecution SipHashExecution.
Definition parsed_reset s tail := ReadNatExecution.token_number (ReadTokenExecution.pending_result s 49 [55] tail) [49;55].
Theorem generated_reset_after_read s bs ns readstate observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  (20 <= length (memory readstate arraydef_0__printBuffer))%nat ->
  meta_value readstate 11 = 17 -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(CommandResetExecution.reset_state readstate,
    observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hmeta Hbuffer Hnumber Hvalid Herror.
  set (f := {|machine := s; bools := bs; nums := ns|} : CommandQuitExecution.Frame).
  unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct, CommandQuitExecution.actual_body. fold f.
  pose proof (CommandResetExecution.generated_reset_body funcdef_0__readNat f readstate observations Hreader Hmeta Hbuffer Hnumber Hvalid Herror) as Hrun.
  unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
Theorem generated_reset_pending s bs ns sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 50 -> meta_value s 8 = 0 -> TokenByteExecution.separator sep -> stdin s = 55 :: sep :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(CommandResetExecution.reset_state (parsed_reset s tail),
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hsep Hin.
  assert (Hreader : execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) =
    Some (tt,(parsed_reset s tail,observations))).
  { apply ReadNatExecution.generated_readNat_observed.
    apply (ReadNatExecution.generated_readNat_pending s (fun _ => false) (fun _ => 0) 49 [55] sep tail); try assumption.
    - cbn [length]. lia.
    - repeat constructor; lia.
    - change (17 <= maximum). unfold maximum. lia. }
  assert (Hrmeta : (17 < length (memory (parsed_reset s tail) arraydef_0__meta))%nat).
  { unfold parsed_reset, ReadNatExecution.token_number. now rewrite store_meta_length, ReadTokenExecution.pending_meta_length. }
  assert (Hrbuffer : (20 <= length (memory (parsed_reset s tail) arraydef_0__printBuffer))%nat).
  { unfold parsed_reset, ReadNatExecution.token_number. rewrite store_meta_other by discriminate.
    rewrite TokenFrame.pending_other by discriminate. exact Hbuffer. }
  assert (Hrnumber : meta_value (parsed_reset s tail) 11 = 17).
  { unfold parsed_reset. rewrite ReadNatExecution.number_result_value.
    - reflexivity.
    - rewrite ReadTokenExecution.pending_meta_length. lia. }
  assert (Hrvalid : meta_value (parsed_reset s tail) 14 = 1).
  { unfold parsed_reset, ReadNatExecution.token_number. rewrite meta_store_other by lia.
    now apply ReadTokenExecution.pending_valid. }
  assert (Hrerror : meta_value (parsed_reset s tail) 8 = 0).
  { unfold parsed_reset, ReadNatExecution.token_number, ReadTokenExecution.pending_result.
    rewrite !meta_store_other by lia.
    change (meta_value (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.started s 49) 1 [55]) 17 1) 8 = 0).
    rewrite meta_store_other by lia. rewrite ReadTokenExecution.put_many_meta_other.
    - apply ReadTokenExecution.started_zero; [exact Hmeta|right; auto].
    - lia. }
  rewrite (generated_reset_after_read s bs ns (parsed_reset s tail) observations Hreader Hrmeta Hrbuffer Hrnumber Hrvalid Hrerror).
  reflexivity.
Qed.
Theorem reset_history_zero s : (3 < length (memory s arraydef_0__meta))%nat ->
  meta_value (CommandResetExecution.reset_state s) 3 = 0.
Proof. intro Hmeta. rewrite CommandResetExecution.reset_meta. now apply meta_store_same. Qed.
Theorem reset_named_objects s name : name <> arraydef_0__meta -> name <> arraydef_0__printBuffer ->
  memory (CommandResetExecution.reset_state s) name = memory s name.
Proof. intros Hmeta Hprint. unfold CommandResetExecution.reset_state.
  rewrite ReplyOKExecution.reply_other by exact Hprint. now rewrite store_meta_other. Qed.
Lemma parsed_input s tail : stdin (parsed_reset s tail) = tail.
Proof. reflexivity. Qed.
Lemma parsed_output s tail : stdout (parsed_reset s tail) = stdout s.
Proof. unfold parsed_reset, ReadNatExecution.token_number. change
  (stdout (ReadTokenExecution.pending_result s 49 [55] tail) = stdout s). apply TokenFrame.pending_output. Qed.
Lemma parsed_meta_length s tail : length (memory (parsed_reset s tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold parsed_reset, ReadNatExecution.token_number. now rewrite store_meta_length, ReadTokenExecution.pending_meta_length. Qed.
Lemma parsed_meta_other s tail i : i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (parsed_reset s tail) i = meta_value s i.
Proof. intros H6 H11 H14 H15 H17. unfold parsed_reset, ReadNatExecution.token_number.
  rewrite meta_store_other by exact H11. now apply TokenFrame.pending_meta_other. Qed.
Lemma parsed_other s tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (parsed_reset s tail) name = memory s name.
Proof. intros Hm Ht. unfold parsed_reset, ReadNatExecution.token_number. rewrite store_meta_other by exact Hm.
  now apply TokenFrame.pending_other. Qed.
Lemma reset_arrays s name : name <> arraydef_0__meta -> memory (CommandResetExecution.reset_state s) name = memory s name.
Proof. intro Hm. change (memory (store_meta s 3 0) name = memory s name). now apply store_meta_other. Qed.
Lemma parsed_storage s tail : ArenaFrame.storage s (parsed_reset s tail).
Proof. split; [apply parsed_meta_length|]. split; [intros; now apply parsed_other|].
  repeat split; apply parsed_meta_other; lia. Qed.
Lemma reset_storage s : ArenaFrame.storage s (CommandResetExecution.reset_state s).
Proof. split; [apply CommandResetExecution.reset_meta_length|]. split; [intros; now apply reset_arrays|].
  repeat split; rewrite CommandResetExecution.reset_meta; apply meta_store_other; lia. Qed.
End ResetInputExecution.
