From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ObservedLocal CommandQuit ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module QuitInputExecution.
Import IndexExecution SipHashExecution.
Theorem generated_quit_after_read s bs ns readstate observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = 0 -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(CommandQuitExecution.quit_state readstate,
    observations ++ [{|flushedOutput := stdout readstate ++ CommandQuitExecution.bye_bytes; unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hmeta Hnumber Hvalid Herror.
  set (f := {|machine := s; bools := bs; nums := ns|} : CommandQuitExecution.Frame).
  unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct, CommandQuitExecution.actual_body. fold f.
  pose proof (CommandQuitExecution.generated_quit_body funcdef_0__readNat f readstate observations Hreader Hmeta Hnumber Hvalid Herror) as Hrun.
  unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun.
  reflexivity.
Qed.
Definition parsed_quit s tail := ReadNatExecution.token_number (ReadTokenExecution.pending_result s 48 [] tail) [48].
Theorem generated_quit_pending s bs ns sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 49 -> meta_value s 8 = 0 -> TokenByteExecution.separator sep -> stdin s = sep :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(CommandQuitExecution.quit_state (parsed_quit s tail),
    observations ++ [{|flushedOutput := stdout s ++ CommandQuitExecution.bye_bytes; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hpending Herror Hsep Hin.
  assert (Hreader : execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) =
    Some (tt,(parsed_quit s tail,observations))).
  { apply ReadNatExecution.generated_readNat_observed.
    apply (ReadNatExecution.generated_readNat_pending s (fun _ => false) (fun _ => 0) 48 [] sep tail); try assumption.
    - cbn [length]. lia.
    - constructor; [lia|constructor].
    - change (0 <= maximum). unfold maximum. lia. }
  assert (Hrmeta : (17 < length (memory (parsed_quit s tail) arraydef_0__meta))%nat).
  { unfold parsed_quit, ReadNatExecution.token_number. now rewrite store_meta_length, ReadTokenExecution.pending_meta_length. }
  assert (Hrnumber : meta_value (parsed_quit s tail) 11 = 0).
  { unfold parsed_quit. rewrite ReadNatExecution.number_result_value.
    - reflexivity.
    - rewrite ReadTokenExecution.pending_meta_length. lia. }
  assert (Hrvalid : meta_value (parsed_quit s tail) 14 = 1).
  { unfold parsed_quit, ReadNatExecution.token_number. rewrite meta_store_other by lia.
    now apply ReadTokenExecution.pending_valid. }
  assert (Hrerror : meta_value (parsed_quit s tail) 8 = 0).
  { unfold parsed_quit, ReadNatExecution.token_number, ReadTokenExecution.pending_result.
    rewrite !meta_store_other by lia.
    change (meta_value (store_meta (ReadTokenExecution.started s 48) 17 1) 8 = 0).
    rewrite meta_store_other by lia. apply ReadTokenExecution.started_zero; [exact Hmeta|right; auto]. }
  rewrite (generated_quit_after_read s bs ns (parsed_quit s tail) observations Hreader Hrmeta Hrnumber Hrvalid Hrerror).
  reflexivity.
Qed.
Lemma quit_stop s tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (CommandQuitExecution.quit_state (parsed_quit s tail)) 9 = 1.
Proof.
  intro Hmeta. change (meta_value (store_meta (parsed_quit s tail) 9 1) 9 = 1).
  apply meta_store_same. unfold parsed_quit, ReadNatExecution.token_number.
  rewrite store_meta_length, ReadTokenExecution.pending_meta_length. lia.
Qed.

Theorem quit_storage s tail : ArenaFrame.storage s (CommandQuitExecution.quit_state (parsed_quit s tail)).
Proof.
  unfold CommandQuitExecution.quit_state, parsed_quit, ReadNatExecution.token_number,
    ReadTokenExecution.pending_result, ReadTokenExecution.started, ReadTokenExecution.reset.
  cbn [ReadTokenExecution.put_many]. ArenaFrame.storage_steps.
Qed.
End QuitInputExecution.

