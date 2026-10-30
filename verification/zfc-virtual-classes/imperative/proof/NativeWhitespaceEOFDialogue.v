From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenPendingLeading NativeState NativeSession NativeDialogueComposition CommandLoop Dialogue NativePendingWhitespaceEOF NativeWhitespaceEOF.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeWhitespaceEOFDialogue.
Import IndexExecution SipHashExecution TokenByteExecution.
Theorem generated native logical whitespace observations :
 NativeDialogueComposition.boundary native logical -> Forall separator whitespace -> stdin native=whitespace ->
 exists final, DialogueExecution.run native observations final observations /\
 NativeState.represents final logical /\ stdin final=[] /\ stdout final=stdout native /\ meta_value final 8=0.
Proof.
 intros Hboundary Hspaces Hin. destruct whitespace as [|ch tail].
 - exists native. split;[apply DialogueExecution.eof;exact Hin|].
   split;[exact(NativeDialogueComposition.state _ _ Hboundary)|].
   split;[exact Hin|]. split;[reflexivity|exact(NativeDialogueComposition.error _ _ Hboundary)].
 - inversion Hspaces as [|? ? Hsep Htail];subst.
   assert(Hbyte:0<=ch<256) by (unfold separator in Hsep;lia).
   pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary)) as Hmeta.
   set(pending:=CommandLoopExecution.pending_state(withInput native tail)ch).
   assert(Hpmeta:(17<length(memory pending arraydef_0__meta))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_length. cbn [memory withInput]. lia. }
   assert(Hptoken:(1024<=length(memory pending arraydef_0__token))%nat).
   { unfold pending,CommandLoopExecution.pending_state. rewrite store_meta_other by discriminate. exact(NativeDialogueComposition.token _ _ Hboundary). }
   assert(Hppending:meta_value pending 15=ch+1).
   { unfold pending,CommandLoopExecution.pending_state. apply meta_store_same. cbn [memory withInput]. lia. }
   assert(Hperror:meta_value pending 8=0).
   { unfold pending,CommandLoopExecution.pending_state. rewrite meta_store_other by lia. exact(NativeDialogueComposition.error _ _ Hboundary). }
   destruct(NativeWhitespaceEOF.generated pending (fun _=>false)(fun _=>0) ch tail observations Hpmeta Hptoken Hppending Hperror Hbyte Hsep Htail eq_refl)
    as(Hrun & Hinput & Houtput & Hstop & Herror).
   set(final:=store_meta(NativePendingWhitespaceEOF.number_result pending)9 1).
   exists final. split.
   + eapply DialogueExecution.stop with (ch:=ch) (tail:=tail) (after:=final) (trace:=observations).
     1: exact Hbyte.
     1: exact Hin.
     1: lia.
     1: exact Hrun.
     1: { unfold final,NativePendingWhitespaceEOF.number_result,NativePendingWhitespaceEOF.token_result.
       repeat rewrite store_meta_length. change(9<length(memory(ReadTokenPendingLeading.pending_base pending)arraydef_0__meta))%nat.
       rewrite ReadTokenPendingLeading.pending_base_length. lia. }
     1: { unfold final. rewrite Hstop. discriminate. }
   + split.
     * unfold final,NativePendingWhitespaceEOF.number_result,NativePendingWhitespaceEOF.token_result,ReadTokenPendingLeading.pending_base,ReadTokenExecution.reset,pending,CommandLoopExecution.pending_state.
       repeat first [apply NativeSession.state_meta;try lia | apply NativeSession.state_input].
       exact(NativeDialogueComposition.state _ _ Hboundary).
     * split;[exact Hinput|]. split;[exact Houtput|exact Herror].
Qed.
End NativeWhitespaceEOFDialogue.
