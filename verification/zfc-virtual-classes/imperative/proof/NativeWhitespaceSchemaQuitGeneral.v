From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeGeneralSession NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaSpacedGeneral
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceQuit NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition ClassLookup LogicalRegistryBounds CommandLoop CommandQuit QuitLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaQuitGeneral.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaMixedGeneral.
Definition wire items quit_prefix suffix := NativeWhitespaceSchemaSpacedGeneral.wire items (quit_prefix++[48;10]++suffix).
Fixpoint schedule (items:list item) (replies:list Protocol.reply) quit_prefix suffix output : list FlushSnapshot :=
 match items,replies with
 | [],[]=>[{|flushedOutput:=output++CommandQuitExecution.bye_bytes;unreadInput:=suffix|}]
 | _::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in {|flushedOutput:=next;unreadInput:=wire tail quit_prefix suffix|}::schedule tail rest quit_prefix suffix next
 | _,_=>[] end.
Theorem generated_finite argument_cap items : forall native logical quit_prefix suffix observations,
 Forall valid_item items -> Forall TokenByteExecution.separator quit_prefix -> NativeDialogueComposition.boundary native logical -> NativeGeneralSession.extra argument_cap native logical ->
 NativeBudgetPlan.capacity argument_cap logical (map req items++[NativeSession.quit]) -> stdin native=wire items quit_prefix suffix ->
 exists final replies target,
 length replies=length items /\ DialogueExecution.run native observations final (observations++schedule items replies quit_prefix suffix (stdout native)) /\
 Protocol.dialogue logical (map req items++[NativeSession.quit]) (replies++[Protocol.BYE]) target [] /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=NativeSession.output (stdout native) replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 induction items as [|[prefix entry] rest IH];intros native logical quit_prefix suffix observations Hvalid HquitPrefix Hboundary Hextra Hcapacity Hinput.
 - destruct quit_prefix as [|ch prefix].
   + change(stdin native=NativeSession.input [] suffix) in Hinput.
     destruct(NativeSession.generated_quit native logical suffix observations (NativeDialogueComposition.state _ _ Hboundary)
       (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hinput)
       as(Hrun & Hstate & Hin & Hout & Hstop & Herror).
     exists(QuitLoopExecution.loop_result native suffix),[],logical. split;[reflexivity|]. split;[exact Hrun|].
     split;[apply Protocol.dialogue_quit|]. repeat first[assumption|split].
   + inversion HquitPrefix as [|ch' prefix' Hch Hprefix];subst ch' prefix'.
     assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
     destruct(NativeWhitespaceQuit.generated native logical ch prefix suffix observations Hboundary Hchbyte Hch Hprefix)
       as(after & Hcommand & Hstate & Hin & Hout & Hstop & Herror & Hlength).
     exists after,[],logical. split;[reflexivity|]. split.
     * cbn [schedule]. eapply DialogueExecution.stop with (ch:=ch) (tail:=prefix++[48;10]++suffix).
       -- exact Hchbyte.
       -- exact Hinput.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- exact Hlength.
       -- rewrite Hstop;discriminate.
     * split;[apply Protocol.dialogue_quit|]. repeat first[assumption|split].
 - inversion Hvalid as [|? ? Hitem Htail];subst. cbn [valid_item fst snd] in Hitem. destruct Hitem as [Hprefix Hentry].
   change(NativeBudgetPlan.capacity argument_cap logical (request entry::(map req rest++[NativeSession.quit]))) in Hcapacity.
   change(stdin native=prefix++frame_wire entry (wire rest quit_prefix suffix)) in Hinput.
   destruct(NativeWhitespaceSchemaSpacedGeneral.command argument_cap native logical prefix entry (map req rest++[NativeSession.quit]) (wire rest quit_prefix suffix) observations Hboundary Hextra Hcapacity Hentry Hprefix Hinput)
    as(ch & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
   destruct(IH after next quit_prefix suffix (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire rest quit_prefix suffix|}]) Htail HquitPrefix HnextBoundary HnextExtra HnextCapacity Hin)
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
       cbn [NativeSession.output]. now rewrite Hout in HfinalOut.
Qed.
End NativeWhitespaceSchemaQuitGeneral.
