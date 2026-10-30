From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeGeneralSession NativeGeneralWhitespaceDialogue
 NativeSetArbitraryTailCommand NativeSetWhitespaceTailCommand NativeSetSchemaSession NativeSchemaFlat NativeWhitespaceQuit NativeSetBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition ClassLookup LogicalRegistryBounds CommandLoop CommandQuit QuitLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetWhitespaceQuitDialogue.
Import IndexExecution SipHashExecution NativeGeneralWhitespaceDialogue.
Definition wire frames quit_prefix suffix := NativeGeneralWhitespaceDialogue.wire frames++quit_prefix++[48;10]++suffix.
Lemma wire_cons prefix request frames quit_prefix suffix :
 wire ((prefix,request)::frames) quit_prefix suffix=prefix++Protocol.request_bytes request++wire frames quit_prefix suffix.
Proof. unfold wire. cbn [NativeGeneralWhitespaceDialogue.wire]. repeat rewrite <-app_assoc. reflexivity. Qed.
Fixpoint schedule (frames:list frame) (replies:list Protocol.reply) quit_prefix suffix output : list FlushSnapshot :=
 match frames,replies with
 | [],[]=>[{|flushedOutput:=output++CommandQuitExecution.bye_bytes;unreadInput:=suffix|}]
 | (_,_)::tail,reply::rest=>let next:=output++Protocol.reply_bytes reply in
   {|flushedOutput:=next;unreadInput:=wire tail quit_prefix suffix|}::schedule tail rest quit_prefix suffix next
 | _,_=>[] end.
Theorem generated_finite frames : forall native logical quit_prefix suffix observations,
 Forall valid frames -> Forall TokenByteExecution.separator quit_prefix -> NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (map snd frames++[NativeSession.quit]) -> stdin native=wire frames quit_prefix suffix ->
 exists final replies target,
 length replies=length frames /\ DialogueExecution.run native observations final (observations++schedule frames replies quit_prefix suffix (stdout native)) /\
 Protocol.dialogue logical (map snd frames++[NativeSession.quit]) (replies++[Protocol.BYE]) target [] /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=NativeSession.output (stdout native) replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix /\ meta_value final 9=1.
Proof.
 induction frames as [|[prefix request] frames IH];intros native logical quit_prefix suffix observations Hvalid HquitPrefix Hboundary Hextra Hcapacity Hinput.
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
 - inversion Hvalid as [|item tail Hitem Htail];subst item tail.
   cbn [valid fst snd] in Hitem. destruct Hitem as [Hshape [Hpositive Hprefix]].
   change (NativeSetBudgetPlan.capacity logical (request::(map snd frames++[NativeSession.quit]))) in Hcapacity.
   rewrite wire_cons in Hinput. destruct prefix as [|ch prefix].
   + change(stdin native=Protocol.request_bytes request++wire frames quit_prefix suffix) in Hinput.
     destruct(NativeSetArbitraryTailCommand.commands native logical request (map snd frames++[NativeSession.quit]) (wire frames quit_prefix suffix) observations
       Hboundary Hextra Hcapacity Hshape Hpositive Hinput)
       as(first & unread & after & reply & next & Hbyte & Hwire & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next quit_prefix suffix (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames quit_prefix suffix|}])
       Htail HquitPrefix HnextBoundary HnextExtra HnextCapacity Hin) as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
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
       cbn [NativeSession.output]. now rewrite Hout in HfinalOut.
   + inversion Hprefix as [|ch' prefix' Hch Hprefix'];subst ch' prefix'.
     assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
     set(base:=withInput native (Protocol.request_bytes request++wire frames quit_prefix suffix)).
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
     destruct(NativeSetWhitespaceTailCommand.generated base logical request (map snd frames++[NativeSession.quit]) (wire frames quit_prefix suffix) observations ch prefix
       HbaseBoundary HbaseExtra Hcapacity Hshape Hpositive eq_refl Hchbyte Hch Hprefix')
       as(after & reply & next & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
     destruct(IH after next quit_prefix suffix (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=wire frames quit_prefix suffix|}])
       Htail HquitPrefix HnextBoundary HnextExtra HnextCapacity Hin) as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & Hclear & HfinalOut & HfinalIn).
     exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
     * cbn [schedule]. eapply DialogueExecution.next with (ch:=ch) (tail:=prefix++Protocol.request_bytes request++wire frames quit_prefix suffix) (after:=after).
       -- exact Hchbyte.
       -- exact Hinput.
       -- pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
       -- exact Hcommand.
       -- pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
       -- exact(NativeDialogueComposition.running _ _ HnextBoundary).
       -- rewrite Hout,<-app_assoc in Hrun. exact Hrun.
     * split;[cbn [map];eapply Protocol.dialogue_step;[exact Hpositive|exact Hstep|exact Hdialogue]|].
       split;[exact Hstate|]. split;[exact Hclear|]. split;[|exact HfinalIn].
       cbn [NativeSession.output]. now rewrite Hout in HfinalOut.
Qed.
Theorem generated_main key0 key1 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 NativeSetBudgetPlan.domain (map snd frames++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames quit_prefix suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames quit_prefix suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames quit_prefix suffix|}]++
 schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix.
Proof.
 intros Hkey0 Hkey1 Hvalid HquitPrefix Hdomain.
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire frames quit_prefix suffix)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hextra:NativeSetSchemaSession.extra ready Protocol.initial).
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
   - split.
     + apply NativeSchemaFlat.empty. exact(NativeState.empty_schemas _ Hempty).
     + constructor. }
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames quit_prefix suffix|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames quit_prefix suffix|}]).
 destruct(generated_finite frames ready Protocol.initial quit_prefix suffix observations Hvalid HquitPrefix Hboundary Hextra
   (NativeSetBudgetPlan.initial_capacity (map snd frames++[NativeSession.quit]) Hdomain) Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin & HstopFinal).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[exact HstopFinal|]. split;[etransitivity;[exact Hmain|exact Hcommands]|]. split;assumption.
Qed.
End NativeSetWhitespaceQuitDialogue.
