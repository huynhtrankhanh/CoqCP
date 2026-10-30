From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralWhitespaceDialogue.
Import IndexExecution SipHashExecution.
Definition frame := (list Z * Protocol.request)%type.
Fixpoint wire (frames:list frame) : list Z := match frames with
 | []=>[] | (prefix,request)::tail=>prefix++Protocol.request_bytes request++wire tail end.
Fixpoint schedule (frames:list frame) (replies:list Protocol.reply) output : list FlushSnapshot :=
 match frames,replies with
 | (_,_)::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in
   {|flushedOutput:=next;unreadInput:=wire tail|}::schedule tail rest next
 | _,_=>[] end.
Definition valid (item:frame) := Protocol.shape (snd item) /\ Protocol.opcode(snd item)<>0%nat /\ Forall TokenByteExecution.separator (fst item).
Theorem generated_finite argument_cap frames : forall native logical observations,
 Forall valid frames -> NativeDialogueComposition.boundary native logical -> NativeGeneralSession.extra argument_cap native logical ->
 NativeBudgetPlan.capacity argument_cap logical (map snd frames) -> stdin native=wire frames ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final (observations++schedule frames replies(stdout native)) /\
 Protocol.dialogue logical (map snd frames) replies target [] /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 induction frames as [|[prefix request] frames IH];intros native logical observations Hvalid Hboundary Hextra Hcapacity Hinput.
 - exists native,[],logical. split;[reflexivity|]. split.
   + cbn [schedule]. rewrite app_nil_r. apply DialogueExecution.eof. exact Hinput.
   + split;[apply Protocol.dialogue_eof|]. split;[exact(NativeDialogueComposition.state _ _ Hboundary)|].
     split;[exact(NativeDialogueComposition.error _ _ Hboundary)|]. split;[now rewrite app_nil_r|exact Hinput].
 - inversion Hvalid as [|item tail Hitem Htail];subst item tail.
   cbn [valid fst snd] in Hitem. destruct Hitem as [Hshape [Hpositive Hprefix]].
   change (NativeBudgetPlan.capacity argument_cap logical (request::map snd frames)) in Hcapacity.
   destruct prefix as [|ch prefix].
   + change(stdin native=Protocol.request_bytes request++wire frames) in Hinput.
     destruct(NativeGeneralArbitraryTailCommand.commands argument_cap native logical request (map snd frames) (wire frames) observations
       Hboundary Hextra Hcapacity Hshape Hpositive Hinput)
       as(first & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames|}])
       Htail HnextBoundary HnextExtra HnextCapacity Hin) as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
     exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
     * cbn [schedule]. eapply DialogueExecution.next with (ch:=first) (tail:=unread) (after:=after).
       -- exact Hbyte.
       -- exact Hwire.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout,<-app_assoc in Hrun. exact Hrun.
     * split;[cbn [map];eapply Protocol.dialogue_step;[exact Hpositive|exact Hstep|exact Hdialogue]|].
       split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [map concat]. exact (eq_trans HfinalOut (eq_trans
         (f_equal (fun bytes=>bytes++concat(map Protocol.reply_bytes replies)) Hout)
         (eq_sym(app_assoc (stdout native) (Protocol.reply_bytes reply) (concat(map Protocol.reply_bytes replies)))))).
   + inversion Hprefix as [|ch' prefix' Hch Hprefix'];subst ch' prefix'.
     assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
     set(base:=withInput native (Protocol.request_bytes request++wire frames)).
     assert(HbaseBoundary:NativeDialogueComposition.boundary base logical).
     { destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning]. constructor.
       - unfold base. now apply NativeSession.state_input.
       - exact Htoken.
       - exact Hprint.
       - exact Herror.
       - exact Hrunning. }
     assert(HbaseExtra:NativeGeneralSession.extra argument_cap base logical).
     { destruct Hextra as [Hbasic Hfields]. destruct Hbasic as [Hmeta Hsip Hsafe Htop Hfalse Hclasses Hunique Hcompact].
       split;[constructor;assumption|exact Hfields]. }
     destruct(NativeGeneralWhitespaceTailCommand.generated argument_cap base logical request (map snd frames) (wire frames) observations ch prefix
       HbaseBoundary HbaseExtra Hcapacity Hshape Hpositive eq_refl Hchbyte Hch Hprefix')
       as(after & reply & next & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames|}])
       Htail HnextBoundary HnextExtra HnextCapacity Hin) as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
     exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
     * cbn [schedule]. eapply DialogueExecution.next with (ch:=ch) (tail:=prefix++Protocol.request_bytes request++wire frames) (after:=after).
       -- exact Hchbyte.
       -- exact Hinput.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout,<-app_assoc in Hrun. exact Hrun.
     * split;[cbn [map];eapply Protocol.dialogue_step;[exact Hpositive|exact Hstep|exact Hdialogue]|].
       split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [map concat]. exact (eq_trans HfinalOut (eq_trans
         (f_equal (fun bytes=>bytes++concat(map Protocol.reply_bytes replies)) Hout)
         (eq_sym(app_assoc (stdout native) (Protocol.reply_bytes reply) (concat(map Protocol.reply_bytes replies)))))).
Qed.
Theorem generated_main key0 key1 frames bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeBudgetPlan.domain (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames|}]++schedule frames replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hvalid Hdomain.
 set(argument_cap:=NativeRequestBounds.maximum(map snd frames)).
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hextra:NativeGeneralSession.extra argument_cap ready Protocol.initial).
 { split.
   - constructor.
     + lia.
     + lia.
     + exact Guarantees.initial_safe.
     + exact Htop.
     + reflexivity.
     + apply ClassLookup.empty. exact(NativeState.empty_classes _ Hempty).
     + exact LogicalRegistryBounds.initial_unique.
     + apply NativeNameCompact.initial_compact. exact(NativeState.empty_names _ Hempty).
   - exact(NativeBudgetFrame.initial_fields ready argument_cap Hempty). }
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames|}]).
 destruct(generated_finite argument_cap frames ready Protocol.initial observations Hvalid Hboundary Hextra
   (NativeBudgetPlan.initial_capacity (map snd frames) Hdomain) Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact Hcommands]|]. split;assumption.
Qed.
End NativeGeneralWhitespaceDialogue.
