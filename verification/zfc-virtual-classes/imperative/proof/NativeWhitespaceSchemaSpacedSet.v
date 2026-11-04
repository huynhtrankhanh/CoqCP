From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeSetSchemaSession NativeSetArbitraryTailCommand NativeSetWhitespaceTailCommand NativeSetBudgetPlan NativeDialogueComposition NativeWhitespaceEOFDialogue NativeWhitespaceSchemaUniformCommand NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaSetEntry NativeWhitespaceSchemaLeadingSet NativeWhitespaceSchemaSpacedGeneral CommandLoop Dialogue.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaSpacedSet.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaSpacedGeneral.
Theorem command native logical prefix entry requests tail observations :
 NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (request entry::requests) -> valid entry -> Forall TokenByteExecution.separator prefix ->
 stdin native=prefix++frame_wire entry tail ->
 exists ch unread after reply next, 0<=ch<256 /\ stdin native=ch::unread /\
 execObserved(funcdef_0__command (fun _=>false)(fun _=>0))(CommandLoopExecution.pending_state(withInput native unread)ch,observations)=Some(tt,(after,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical (request entry) reply next /\ NativeDialogueComposition.boundary after next /\ NativeSetSchemaSession.extra after next /\
 NativeSetBudgetPlan.capacity next requests /\ stdin after=tail /\ stdout after=stdout native++Protocol.reply_bytes reply.
Proof.
 intros Hboundary Hextra Hcapacity Hvalid Hprefix Hinput. destruct prefix as [|ch prefix].
 - destruct entry as [r|fields name namespaces namesep countspaces countsep firstsep].
   + cbn [frame_wire request valid] in *. destruct Hvalid as [Hshape Hpositive].
     exact(NativeSetArbitraryTailCommand.commands native logical r requests tail observations Hboundary Hextra Hcapacity Hshape Hpositive Hinput).
   + cbn [frame_wire request valid] in *. destruct Hvalid as (Hshape & Hfields & Hns & Hnsep & Hcs & Hcsep & Hfirst).
     destruct(NativeWhitespaceSchemaSetEntry.generated native logical fields name namespaces namesep countspaces countsep firstsep tail requests observations
       Hboundary Hextra Hcapacity Hshape Hfields Hns Hnsep Hcs Hcsep Hfirst Hinput) as(after & reply & next & Hrun & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     exists 50,(52::firstsep::NativeWhitespaceSchemaUniformCommand.payload name fields namespaces namesep countspaces countsep tail),after,reply,next. repeat first[assumption|split|lia].
 - inversion Hprefix as [|? ? Hch Hprefix'];subst. assert(Hbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
   set(base:=withInput native(frame_wire entry tail)).
   assert(HbaseBoundary:NativeDialogueComposition.boundary base logical).
   { destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning]. constructor;try assumption. unfold base. now apply NativeSession.state_input. }
   assert(HbaseExtra:NativeSetSchemaSession.extra base logical).
   { destruct Hextra as [Hbasic [Hflat Hsets]]. destruct Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact]. split;[constructor;assumption|split;assumption]. }
   destruct entry as [r|fields name namespaces namesep countspaces countsep firstsep].
   + cbn [valid] in Hvalid. destruct Hvalid as [Hshape Hpositive].
     destruct(NativeSetWhitespaceTailCommand.generated base logical r requests tail observations ch prefix HbaseBoundary HbaseExtra Hcapacity Hshape Hpositive eq_refl Hbyte Hch Hprefix')
      as(after & reply & next & Hrun & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     exists ch,(prefix++Protocol.request_bytes r++tail),after,reply,next. cbn [request frame_wire] in *. repeat first[assumption|split].
   + cbn [valid] in Hvalid. destruct Hvalid as (Hshape & Hfields & Hns & Hnsep & Hcs & Hcsep & Hfirst).
     destruct(NativeWhitespaceSchemaLeadingSet.generated base logical fields name namespaces namesep countspaces countsep firstsep tail requests observations ch prefix
      HbaseBoundary HbaseExtra Hcapacity Hshape Hfields Hns Hnsep Hcs Hcsep Hfirst Hbyte Hch Hprefix')
      as(after & reply & next & Hrun & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     exists ch,(prefix++50::52::firstsep::NativeWhitespaceSchemaUniformCommand.payload name fields namespaces namesep countspaces countsep tail),after,reply,next.
     cbn [request frame_wire] in *. repeat first[assumption|split].
Qed.
Theorem generated_finite items ending : forall native logical observations,
 Forall TokenByteExecution.separator ending -> Forall valid_item items -> NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (map req items) -> stdin native=wire items ending ->
 exists final replies target, length replies=length items /\ DialogueExecution.run native observations final(observations++schedule items replies ending(stdout native)) /\
 Protocol.dialogue logical (map req items) replies target [] /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 induction items as [|[prefix entry] rest IH];intros native logical observations Hending Hvalid Hboundary Hextra Hcapacity Hinput.
 - destruct(NativeWhitespaceEOFDialogue.generated native logical ending observations Hboundary Hending Hinput) as(final & Hrun & Hstate & Hin & Hout & Herror).
   exists final,[],logical. split;[reflexivity|]. split;[cbn [schedule];now rewrite app_nil_r|].
   split;[apply Protocol.dialogue_eof|]. split;[exact Hstate|]. split;[exact Herror|]. split;[now rewrite app_nil_r|exact Hin].
 - inversion Hvalid as [|? ? Hitem Hrest];subst. cbn [valid_item fst snd] in Hitem. destruct Hitem as [Hprefix Hentry].
   change(NativeSetBudgetPlan.capacity logical (request entry::map req rest)) in Hcapacity.
   destruct(command native logical prefix entry (map req rest) (wire rest ending) observations Hboundary Hextra Hcapacity Hentry Hprefix Hinput)
    as(ch & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
   destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire rest ending|}]) Hending Hrest HnextBoundary HnextExtra HnextCapacity Hin)
    as(final & replies & target & Hlen & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
   exists final,(reply::replies),target. split;[cbn;lia|]. split.
   + cbn [schedule]. eapply DialogueExecution.next with (ch:=ch) (tail:=unread) (after:=after).
     * exact Hbyte.
     * exact Hwire.
     * pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
     * exact Hcommand.
     * pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
     * exact(NativeDialogueComposition.running _ _ HnextBoundary).
     * rewrite Hout,<-app_assoc in Hrun. exact Hrun.
   + split.
     * cbn [map req]. eapply Protocol.dialogue_step;[|exact Hstep|exact Hdialogue].
       change (Protocol.opcode (request entry)<>0%nat). destruct entry;cbn [valid request] in Hentry |- *;[exact (proj2 Hentry)|discriminate].
     * split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [map concat]. rewrite Hout in HfinalOut. now rewrite <-app_assoc in HfinalOut.
Qed.
End NativeWhitespaceSchemaSpacedSet.
