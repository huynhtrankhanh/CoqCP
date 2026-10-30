From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeSetSchemaSession
 NativeSetArbitraryTailCommand NativeSetWhitespaceTailCommand NativeSetBudgetPlan NativeRequestBounds NativeBudgetFrame NativeSetSchemaSession NativeSetBudgetPlan NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetPrefixStop.
Import IndexExecution SipHashExecution.
Definition frame := (list Z * Protocol.request)%type.
Fixpoint wire (frames:list frame) : list Z := match frames with
 | []=>[] | (prefix,request)::tail=>prefix++Protocol.request_bytes request++wire tail end.
Fixpoint schedule (frames:list frame) (replies:list Protocol.reply) output : list FlushSnapshot :=
 match frames,replies with
 | (_,_)::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in
   {|flushedOutput:=next;unreadInput:=wire tail|}::schedule tail rest next
 | _,_=>[] end.
Fixpoint schedule_tail (frames:list frame) (replies:list Protocol.reply) output ending : list FlushSnapshot :=
 match frames,replies with
 | (_,_)::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in
   {|flushedOutput:=next;unreadInput:=wire tail++ending|}::schedule_tail tail rest next ending
 | _,_=>[] end.
Definition valid (item:frame) := Protocol.shape (snd item) /\ Protocol.opcode(snd item)<>0%nat /\ Forall TokenByteExecution.separator (fst item).
Definition stop_spec := NativeGeneralPrefixStop.stop_spec.
Theorem generated_finite frames ending remaining : forall native logical observations,
 stop_spec ending remaining -> Forall valid frames -> NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (map snd frames) -> stdin native=wire frames++ending ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final
   (observations++schedule_tail frames replies(stdout native) ending++[{|flushedOutput:=stdout native++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=remaining|}]) /\
 Protocol.dialogue logical (map snd frames) replies target [] /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=remaining /\ meta_value final 9=1.
Proof.
 induction frames as [|[prefix request] frames IH];intros native logical observations Hstop Hvalid Hboundary Hextra Hcapacity Hinput.
 - destruct(Hstop native logical observations Hboundary Hinput) as(final & Hrun & Hout & Hin & Hstopflag).
   exists final,[],logical. split;[reflexivity|]. split.
   + cbn [schedule_tail map concat]. exact Hrun.
   + split;[apply Protocol.dialogue_eof|]. cbn [map concat]. repeat first [assumption|split].
 - inversion Hvalid as [|item tail Hitem Htail];subst item tail.
   cbn [valid fst snd] in Hitem. destruct Hitem as [Hshape [Hpositive Hprefix]].
   change (NativeSetBudgetPlan.capacity logical (request::map snd frames)) in Hcapacity.
   destruct prefix as [|ch prefix].
   + cbn [wire app] in Hinput. rewrite <- app_assoc in Hinput.
     destruct(NativeSetArbitraryTailCommand.commands native logical request (map snd frames) (wire frames++ending) observations
       Hboundary Hextra Hcapacity Hshape Hpositive Hinput)
       as(first & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames++ending|}])
       Hstop Htail HnextBoundary HnextExtra HnextCapacity Hin) as(final & replies & target & Hlength & Hrun & Hdialogue & HfinalOut & HfinalIn & Hstopflag).
     exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
     * cbn [schedule_tail]. eapply DialogueExecution.next with (ch:=first) (tail:=unread) (after:=after).
       -- exact Hbyte.
       -- exact Hwire.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout in Hrun. cbn [map concat]. repeat rewrite <-app_assoc in *. exact Hrun.
     * split;[cbn [map];eapply Protocol.dialogue_step;[exact Hpositive|exact Hstep|exact Hdialogue]|].
       split;[|now split].
       cbn [map concat]. rewrite Hout in HfinalOut. repeat rewrite <-app_assoc in *. exact HfinalOut.
   + cbn [wire app] in Hinput. repeat rewrite <- app_assoc in Hinput.
     inversion Hprefix as [|ch' prefix' Hch Hprefix'];subst ch' prefix'.
     assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
     set(base:=withInput native (Protocol.request_bytes request++wire frames++ending)).
     assert(HbaseBoundary:NativeDialogueComposition.boundary base logical).
     { destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning]. constructor.
       - unfold base. now apply NativeSession.state_input.
       - exact Htoken.
       - exact Hprint.
       - exact Herror.
       - exact Hrunning. }
     assert(HbaseExtra:NativeSetSchemaSession.extra base logical).
     { destruct Hextra as [Hbasic [Hflat Hsets]]. destruct Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hclasses Hunique Hcompact].
       split;[constructor;assumption|split;assumption]. }
     destruct(NativeSetWhitespaceTailCommand.generated base logical request (map snd frames) (wire frames++ending) observations ch prefix
       HbaseBoundary HbaseExtra Hcapacity Hshape Hpositive eq_refl Hchbyte Hch Hprefix')
       as(after & reply & next & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames++ending|}])
       Hstop Htail HnextBoundary HnextExtra HnextCapacity Hin) as(final & replies & target & Hlength & Hrun & Hdialogue & HfinalOut & HfinalIn & Hstopflag).
     exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
     * cbn [schedule_tail]. eapply DialogueExecution.next with (ch:=ch) (tail:=prefix++Protocol.request_bytes request++wire frames++ending) (after:=after).
       -- exact Hchbyte.
       -- exact Hinput.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout in Hrun. cbn [map concat]. repeat rewrite <-app_assoc in *. exact Hrun.
     * split;[cbn [map];eapply Protocol.dialogue_step;[exact Hpositive|exact Hstep|exact Hdialogue]|].
       split;[|now split].
       cbn [map concat]. rewrite Hout in HfinalOut. repeat rewrite <-app_assoc in *. exact HfinalOut.
Qed.
End NativeSetPrefixStop.
