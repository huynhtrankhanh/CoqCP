From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte UndoInput ResetInput CommandReset
 NativeState NativeStateFrames HistoryRefinement Representation ArenaFrame FormulaFrame SemanticFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeHistoryCommands.
Import IndexExecution SipHashExecution.
Lemma undo_frame native tail count :
 NativeStateFrames.registries native (UndoInputExecution.result native tail count).
Proof.
 constructor;first [apply UndoInputExecution.result_meta_other;lia|
 apply UndoInputExecution.result_named_objects;discriminate].
Qed.
Lemma reset_frame native tail :
 NativeStateFrames.registries native (CommandResetExecution.reset_state (ResetInputExecution.parsed_reset native tail)).
Proof.
 constructor;first
 [rewrite CommandResetExecution.reset_meta,meta_store_other by lia;apply ResetInputExecution.parsed_meta_other;lia|
 rewrite ResetInputExecution.reset_arrays by discriminate;apply ResetInputExecution.parsed_other;discriminate].
Qed.
Theorem undo_represents native logical tail :
 (17<length (memory native arraydef_0__meta))%nat ->
 NativeState.represents native logical ->
 NativeState.represents (UndoInputExecution.result native tail (length (Protocol.history logical)))
   (HistoryRefinement.undone logical).
Proof.
 intros Hmeta Hstate. destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 pose proof (SemanticFrames.arena_NoDup native _ Harena) as Hunique.
 eapply NativeStateFrames.finish with (native:=native) (before:=logical)
   (request:=Protocol.Req 16 [] []) (reply:=UndoInputExecution.reply (length (Protocol.history logical))).
 - constructor;assumption.
 - apply undo_frame.
 - now apply HistoryRefinement.logical_undo.
 - discriminate.
 - reflexivity.
 - exact (FormulaFrame.storage_arena native _ _ (UndoInputExecution.result_storage native tail _) Harena).
 - destruct Hclasses as [Hcount Harray]. split.
   + rewrite UndoInputExecution.result_meta_other by lia. exact Hcount.
   + rewrite UndoInputExecution.result_named_objects by discriminate. exact Harray.
 - now apply HistoryRefinement.undo_represents.
Qed.
Theorem reset_represents native logical tail :
 (17<length (memory native arraydef_0__meta))%nat -> NativeState.represents native logical ->
 NativeState.represents (CommandResetExecution.reset_state (ResetInputExecution.parsed_reset native tail))
   (Protocol.with_history logical []).
Proof.
 intros Hmeta Hstate. destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 pose proof (SemanticFrames.arena_NoDup native _ Harena) as Hunique.
 eapply NativeStateFrames.finish with (native:=native) (before:=logical)
   (request:=Protocol.Req 17 [] []) (reply:=Protocol.OK 0).
 - constructor;assumption.
 - apply reset_frame.
 - now apply HistoryRefinement.logical_reset.
 - discriminate.
 - reflexivity.
 - eapply ArenaFrame.storage_arena;[|exact Harena].
   eapply ArenaFrame.storage_trans;[apply ResetInputExecution.parsed_storage|apply ResetInputExecution.reset_storage].
 - destruct Hclasses as [Hcount Harray]. split.
   + rewrite CommandResetExecution.reset_meta,meta_store_other by lia.
     rewrite ResetInputExecution.parsed_meta_other by lia. exact Hcount.
   + rewrite ResetInputExecution.reset_arrays,ResetInputExecution.parsed_other by discriminate. exact Harray.
 - now apply HistoryRefinement.reset_represents.
Qed.
Theorem generated_undo native logical bs ns sep tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=50 -> meta_value native 8=0 ->
 Z.of_nat (length (Protocol.history logical))<=maximum -> NativeState.represents native logical ->
 TokenByteExecution.separator sep -> stdin native=54::sep::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (UndoInputExecution.reply (length (Protocol.history logical)));unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 16 [] []) (UndoInputExecution.reply (length (Protocol.history logical)))
   (HistoryRefinement.undone logical) /\ NativeState.represents final (HistoryRefinement.undone logical).
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hword Hstate Hsep Hinput.
 exists (UndoInputExecution.result native tail (length (Protocol.history logical))). split.
 - exact (UndoInputExecution.generated_pending native bs ns (length (Protocol.history logical)) sep tail observations
    Hmeta Htoken Hprint Hpending Herror (proj1 (NativeState.history_representation _ _ Hstate)) Hword Hsep Hinput).
 - split;[apply HistoryRefinement.logical_undo;exact (SemanticFrames.arena_NoDup native _ (NativeState.formula_representation _ _ Hstate))|].
   now apply undo_represents.
Qed.
Theorem generated_reset native logical bs ns sep tail observations :
 (17<length (memory native arraydef_0__meta))%nat ->
 (1024<=length (memory native arraydef_0__token))%nat ->
 (20<=length (memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=50 -> meta_value native 8=0 -> NativeState.represents native logical ->
 TokenByteExecution.separator sep -> stdin native=55::sep::tail ->
 exists final,
 execObserved (funcdef_0__command bs ns) (native,observations)=Some (tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes (Protocol.OK 0);unreadInput:=tail|}])) /\
 Protocol.step logical (Protocol.Req 17 [] []) (Protocol.OK 0) (Protocol.with_history logical []) /\
 NativeState.represents final (Protocol.with_history logical []).
Proof.
 intros Hmeta Htoken Hprint Hpending Herror Hstate Hsep Hinput.
 exists (CommandResetExecution.reset_state (ResetInputExecution.parsed_reset native tail)). split.
 - exact (ResetInputExecution.generated_reset_pending native bs ns sep tail observations Hmeta Htoken Hprint Hpending Herror Hsep Hinput).
 - split;[apply HistoryRefinement.logical_reset;exact (SemanticFrames.arena_NoDup native _ (NativeState.formula_representation _ _ Hstate))|].
   now apply reset_represents.
Qed.
End NativeHistoryCommands.
