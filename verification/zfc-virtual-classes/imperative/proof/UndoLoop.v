From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash TokenByte Startup CommandLoop Dialogue CommandInput UndoInput FormulaFrame ArenaFrame Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module UndoLoopExecution.
Import IndexExecution SipHashExecution.
Definition pending s := CommandLoopExecution.pending_state (withInput s [54;10]) 49.
Definition result s count := UndoInputExecution.result (pending s) [] count.
Lemma pending_meta_length s : length (memory (pending s) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold pending, CommandLoopExecution.pending_state. rewrite store_meta_length. reflexivity. Qed.
Lemma result_meta_length s count : length (memory (result s count) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result. now rewrite UndoInputExecution.result_meta_length, pending_meta_length. Qed.
Lemma result_input s count : stdin (result s count) = [].
Proof. unfold result. apply UndoInputExecution.result_input. Qed.
Lemma result_output s count : stdout (result s count) = stdout s ++ Protocol.reply_bytes (UndoInputExecution.reply count).
Proof. unfold result. rewrite UndoInputExecution.result_output. reflexivity. Qed.
Lemma result_meta_other s count i : i <> 3%nat -> i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (result s count) i = meta_value s i.
Proof.
  intros H3 H6 H11 H14 H15 H17. unfold result. rewrite UndoInputExecution.result_meta_other by assumption.
  unfold pending, CommandLoopExecution.pending_state. now rewrite meta_store_other by exact H15.
Qed.
Theorem generated_loop_undo s bs ns count observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 8 = 0 -> meta_value s 9 = 0 -> meta_value s 3 = Z.of_nat count ->
  Z.of_nat count <= maximum -> stdin s = [49;54;10] ->
  execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body) (s,observations) =
    Some (tt,(result s count,observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (UndoInputExecution.reply count); unreadInput := []|}])).
Proof.
  intros Hmeta Htoken Hprint Herror Hstop Hhistory Hword Hin.
  assert (Hpm : (17 < length (memory (pending s) arraydef_0__meta))%nat) by (now rewrite pending_meta_length).
  assert (Hpt : (1024 <= length (memory (pending s) arraydef_0__token))%nat).
  { unfold pending, CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Htoken. }
  assert (Hpp : (20 <= length (memory (pending s) arraydef_0__printBuffer))%nat).
  { unfold pending, CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact Hprint. }
  assert (Hpend : meta_value (pending s) 15 = 50).
  { unfold pending, CommandLoopExecution.pending_state. apply meta_store_same.
    eapply Nat.le_lt_trans with (m := 17%nat); [lia|exact Hmeta]. }
  assert (Herr : meta_value (pending s) 8 = 0).
  { unfold pending, CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Herror. }
  assert (Hhist : meta_value (pending s) 3 = Z.of_nat count).
  { unfold pending, CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Hhistory. }
  pose proof (UndoInputExecution.generated_pending (pending s) (fun _ => false) (fun _ => 0) count 10 [] observations
    Hpm Hpt Hpp Hpend Herr Hhist Hword ltac:(unfold TokenByteExecution.separator; tauto) eq_refl) as Hcommand.
  change (execObserved (funcdef_0__command (fun _ => false) (fun _ => 0)) (pending s,observations) =
    Some (tt,(result s count,observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (UndoInputExecution.reply count); unreadInput := []|}]))) in Hcommand.
  apply DialogueExecution.generated_commands.
  eapply DialogueExecution.next with (ch := 49) (tail := [54;10]) (after := result s count)
    (trace := observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (UndoInputExecution.reply count); unreadInput := []|}]);
    [lia|exact Hin|lia|exact Hcommand| | |].
  - rewrite result_meta_length. lia.
  - rewrite result_meta_other by lia. exact Hstop.
  - apply DialogueExecution.eof. apply result_input.
Qed.
Lemma result_storage s count : FormulaFrame.storage s (result s count).
Proof.
  eapply FormulaFrame.storage_trans with (t := pending s).
  - apply FormulaFrame.strong_storage. unfold pending, CommandLoopExecution.pending_state.
    eapply ArenaFrame.storage_trans with (t := withInput s [54;10]);
      [apply ArenaFrame.storage_input|apply ArenaFrame.storage_meta; lia].
  - apply UndoInputExecution.result_storage.
Qed.
Lemma result_arena s count meaning : NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (result s count) meaning.
Proof. intro Harena. eapply FormulaFrame.storage_arena; [apply result_storage|exact Harena]. Qed.
Lemma result_history s count : (17 < length (memory s arraydef_0__meta))%nat -> meta_value s 3 = Z.of_nat count ->
  meta_value (result s count) 3 = Z.of_nat (Nat.pred count).
Proof.
  intros Hmeta Hhistory. refine (UndoInputExecution.result_history (pending s) [] count _ _);
    [now rewrite pending_meta_length|].
  unfold pending, CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact Hhistory.
Qed.
End UndoLoopExecution.
