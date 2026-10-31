From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeGeneralSession NativeSetSchemaSession NativeSetArbitraryTailCommand NativeSetBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeWhitespaceSchemaArguments NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaGeneralEntry NativeWhitespaceSchemaSetEntry NativeWhitespaceSchemaMixedGeneral FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaMixedSet.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaMixedGeneral.
Theorem generated_finite frames ending : forall native logical observations,
 Forall TokenByteExecution.separator ending -> Forall valid frames -> NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (map request frames) -> stdin native=wire frames ending ->
 exists final replies target, length replies=length frames /\ DialogueExecution.run native observations final(observations++schedule frames replies ending(stdout native)) /\
 Protocol.dialogue logical (map request frames) replies target [] /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 induction frames as [|item rest IH];intros native logical observations Hending Hvalid Hboundary Hextra Hcapacity Hinput.
 - destruct(NativeWhitespaceEOFDialogue.generated native logical ending observations Hboundary Hending Hinput) as(final & Hrun & Hstate & Hin & Hout & Herror).
   exists final,[],logical. split;[reflexivity|]. split;[cbn [schedule];now rewrite app_nil_r|].
   split;[apply Protocol.dialogue_eof|]. split;[exact Hstate|]. split;[exact Herror|]. split;[now rewrite app_nil_r|exact Hin].
 - inversion Hvalid as [|? ? Hitem Hrest];subst. destruct item as [r|fields name namespaces namesep countspaces countsep firstsep].
   + cbn [valid] in Hitem. destruct Hitem as [Hshape Hpositive]. cbn [wire frame_wire] in Hinput.
     change(NativeSetBudgetPlan.capacity logical (r::map request rest)) in Hcapacity.
     destruct(NativeSetArbitraryTailCommand.commands native logical r (map request rest) (wire rest ending) observations
       Hboundary Hextra Hcapacity Hshape Hpositive Hinput) as(first & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire rest ending|}]) Hending Hrest HnextBoundary HnextExtra HnextCapacity Hin)
       as(final & replies & target & Hlen & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
     exists final,(reply::replies),target. split;[cbn;lia|]. split.
     * cbn [schedule]. eapply DialogueExecution.next with (ch:=first) (tail:=unread) (after:=after).
       -- exact Hbyte.
       -- exact Hwire.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout,<-app_assoc in Hrun. exact Hrun.
     * split;[cbn [map request];eapply Protocol.dialogue_step;[exact Hpositive|exact Hstep|exact Hdialogue]|].
       split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [map concat]. rewrite Hout in HfinalOut. now rewrite <-app_assoc in HfinalOut.
   + cbn [valid] in Hitem. destruct Hitem as (Hshape & Hfields & Hns & Hnsep & Hcs & Hcsep & Hfirst).
     cbn [wire frame_wire] in Hinput.
     change(NativeSetBudgetPlan.capacity logical (Protocol.Req 24 (map snd fields) name::map request rest)) in Hcapacity.
     destruct(NativeWhitespaceSchemaSetEntry.generated native logical fields name namespaces namesep countspaces countsep firstsep (wire rest ending) (map request rest) observations
       Hboundary Hextra Hcapacity Hshape Hfields Hns Hnsep Hcs Hcsep Hfirst Hinput)
       as(after & reply & next & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire rest ending|}]) Hending Hrest HnextBoundary HnextExtra HnextCapacity Hin)
       as(final & replies & target & Hlen & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
     exists final,(reply::replies),target. split;[cbn;lia|]. split.
     * cbn [schedule]. eapply DialogueExecution.next with (ch:=50) (tail:=52::firstsep::NativeWhitespaceSchemaUniformCommand.payload name fields namespaces namesep countspaces countsep (wire rest ending)) (after:=after).
       -- lia.
       -- exact Hinput.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout,<-app_assoc in Hrun. exact Hrun.
     * split;[cbn [map request];eapply Protocol.dialogue_step;[discriminate|exact Hstep|exact Hdialogue]|].
       split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [map concat]. rewrite Hout in HfinalOut. now rewrite <-app_assoc in HfinalOut.
Qed.
End NativeWhitespaceSchemaMixedSet.
