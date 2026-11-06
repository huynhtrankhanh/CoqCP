From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeGeneralSession NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeSetSchemaSession NativeSetBudgetPlan NativeWhitespaceSchemaSpacedSet NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaGeneralEntry NativeWhitespaceSchemaLeadingGeneral CommandLoop Dialogue.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaStopSet.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaSpacedGeneral.
Theorem generated_finite items ending remaining : forall native logical observations,
 NativeGeneralPrefixStop.stop_spec ending remaining -> Forall valid_item items -> NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (map req items) -> stdin native=wire items ending ->
 exists final replies target, length replies=length items /\ DialogueExecution.run native observations final(observations++schedule items replies ending(stdout native)++[{|flushedOutput:=stdout native++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=remaining|}]) /\
 Protocol.dialogue logical (map req items) replies target [] /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=remaining /\ meta_value final 9=1.
Proof.
 induction items as [|[prefix entry] rest IH];intros native logical observations Hstop Hvalid Hboundary Hextra Hcapacity Hinput.
 - destruct(Hstop native logical observations Hboundary Hinput) as(final & Hrun & Hout & Hin & Hflag).
   exists final,[],logical. split;[reflexivity|]. split;[cbn [schedule map concat];exact Hrun|].
   split;[apply Protocol.dialogue_eof|]. cbn [map concat]. repeat first [assumption|split].
 - inversion Hvalid as [|? ? Hitem Hrest];subst. cbn [valid_item fst snd] in Hitem. destruct Hitem as [Hprefix Hentry].
   change(NativeSetBudgetPlan.capacity logical (request entry::map req rest)) in Hcapacity.
   destruct(NativeWhitespaceSchemaSpacedSet.command native logical prefix entry (map req rest) (wire rest ending) observations Hboundary Hextra Hcapacity Hentry Hprefix Hinput)
    as(ch & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
   destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire rest ending|}]) Hstop Hrest HnextBoundary HnextExtra HnextCapacity Hin)
    as(final & replies & target & Hlen & Hrun & Hdialogue & HfinalOut & HfinalIn & Hflag).
   exists final,(reply::replies),target. split;[cbn;lia|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=ch) (tail:=unread) (after:=after).
     * exact Hbyte.
     * exact Hwire.
     * pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
     * exact Hcommand.
     * pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
     * exact(NativeDialogueComposition.running _ _ HnextBoundary).
     * rewrite Hout in Hrun. cbn [map concat req]. repeat rewrite <-app_assoc in *. exact Hrun.
   + split.
     * cbn [map req]. eapply Protocol.dialogue_step;[|exact Hstep|exact Hdialogue].
       change (Protocol.opcode (request entry)<>0%nat). destruct entry;cbn [valid request] in Hentry |- *;[exact (proj2 Hentry)|discriminate].
     * split;[|now split]. cbn [map concat req]. rewrite Hout in HfinalOut. repeat rewrite <-app_assoc in *. exact HfinalOut.
Qed.
End NativeWhitespaceSchemaStopSet.
