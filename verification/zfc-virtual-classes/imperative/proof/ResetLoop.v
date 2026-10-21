From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash TokenByte ReplyOK ObservedLocal Startup CommandLoop Dialogue CommandReset ResetInput ArenaFrame Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ResetLoopExecution.
Import IndexExecution SipHashExecution.
Definition pending s := CommandLoopExecution.pending_state (withInput s [55;10]) 49.
Definition result s := CommandResetExecution.reset_state (ResetInputExecution.parsed_reset (pending s) []).
Lemma pending_meta_length s : length (memory (pending s) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold pending, CommandLoopExecution.pending_state. rewrite store_meta_length. reflexivity. Qed.
Lemma result_meta_length s : length (memory (result s) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result. now rewrite CommandResetExecution.reset_meta_length, ResetInputExecution.parsed_meta_length, pending_meta_length. Qed.
Lemma result_input s : stdin (result s) = [].
Proof. reflexivity. Qed.
Lemma result_output s : stdout (result s) = stdout s ++ Protocol.reply_bytes (Protocol.OK 0).
Proof.
  unfold result, CommandResetExecution.reset_state. rewrite ReplyOKExecution.reply_output.
  change (stdout (ResetInputExecution.parsed_reset (pending s) []) ++ Protocol.reply_bytes (Protocol.OK 0) = stdout s ++ Protocol.reply_bytes (Protocol.OK 0)).
  rewrite ResetInputExecution.parsed_output. reflexivity.
Qed.
Lemma result_meta_other s i : i <> 3%nat -> i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (result s) i = meta_value s i.
Proof.
  intros H3 H6 H11 H14 H15 H17. unfold result. rewrite CommandResetExecution.reset_meta.
  rewrite meta_store_other by exact H3. rewrite ResetInputExecution.parsed_meta_other by assumption.
  unfold pending, CommandLoopExecution.pending_state. now rewrite meta_store_other by exact H15.
Qed.
Theorem generated_loop_reset s bs ns observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 8 = 0 -> meta_value s 9 = 0 -> stdin s = [49;55;10] ->
  execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body) (s,observations) =
    Some (tt,(result s,observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := []|}])).
Proof.
  intros Hmeta Htoken Hprint Herror Hstop Hin.
  assert (Hpm : (17 < length (memory (pending s) arraydef_0__meta))%nat) by (now rewrite pending_meta_length).
  assert (Hpt : (1024 <= length (memory (pending s) arraydef_0__token))%nat).
  { unfold pending, CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
  assert (Hpp : (20 <= length (memory (pending s) arraydef_0__printBuffer))%nat).
  { unfold pending, CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Hprint. }
  assert (Hpend : meta_value (pending s) 15 = 50).
  { unfold pending, CommandLoopExecution.pending_state. apply meta_store_same. eapply Nat.le_lt_trans with (m := 17%nat); [lia|exact Hmeta]. }
  assert (Herr : meta_value (pending s) 8 = 0).
  { unfold pending, CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
  pose proof (ResetInputExecution.generated_reset_pending (pending s) (fun _ => false) (fun _ => 0) 10 [] observations
    Hpm Hpt Hpp Hpend Herr ltac:(unfold TokenByteExecution.separator; tauto) eq_refl) as Hcommand.
  change (execObserved (funcdef_0__command (fun _ => false) (fun _ => 0)) (pending s,observations) =
    Some (tt,(result s,observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := []|}]))) in Hcommand.
  apply DialogueExecution.generated_commands.
  eapply DialogueExecution.next with (ch := 49) (tail := [55;10]) (after := result s)
    (trace := observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := []|}]);
    [lia|exact Hin|lia|exact Hcommand| | |].
  - rewrite result_meta_length. lia.
  - rewrite result_meta_other by lia. exact Hstop.
  - apply DialogueExecution.eof. apply result_input.
Qed.
Lemma result_storage s : ArenaFrame.storage s (result s).
Proof.
  eapply ArenaFrame.storage_trans with (t := pending s).
  - unfold pending, CommandLoopExecution.pending_state.
    eapply ArenaFrame.storage_trans with (t := withInput s [55;10]); [apply ArenaFrame.storage_input|].
    apply ArenaFrame.storage_meta; lia.
  - unfold result. eapply ArenaFrame.storage_trans; [apply ResetInputExecution.parsed_storage|apply ResetInputExecution.reset_storage].
Qed.
Lemma result_arena s meaning : NativeRepresentation.canonical_arena s meaning -> NativeRepresentation.canonical_arena (result s) meaning.
Proof. intro Harena. eapply ArenaFrame.storage_arena; [apply result_storage|exact Harena]. Qed.
Lemma result_history_zero s : (17 < length (memory s arraydef_0__meta))%nat -> meta_value (result s) 3 = 0.
Proof. intro Hmeta. unfold result. apply ResetInputExecution.reset_history_zero.
  rewrite ResetInputExecution.parsed_meta_length, pending_meta_length. lia. Qed.
End ResetLoopExecution.
