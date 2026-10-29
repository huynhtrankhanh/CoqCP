From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeGeneralSuffixSession NativeSetSchemaSession NativeSetSuffixCommand NativeSetBudgetPlan NativeSchemaFlat NativeBudgetFrame NativeRequestBounds NativeNameCompact
 FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop CommandQuit QuitLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetSuffixSession.
Import IndexExecution SipHashExecution.
Theorem generated_finite requests : forall native logical suffix observations,
 Forall Protocol.shape requests -> Forall(fun request=>Protocol.opcode request<>0%nat) requests ->
 NativeDialogueComposition.boundary native logical -> NativeSetSchemaSession.extra native logical ->
 NativeSetBudgetPlan.capacity logical (requests++[NativeSession.quit]) ->
 stdin native=NativeSession.input requests suffix ->
 exists final replies target,
 length replies=length requests /\
 DialogueExecution.run native observations final (observations++NativeSession.schedule (stdout native) requests replies suffix) /\
 Protocol.dialogue logical (requests++[NativeSession.quit]) (replies++[Protocol.BYE]) target [] /\
 NativeState.represents final target /\ stdin final=suffix /\
 stdout final=NativeSession.output (stdout native) replies++CommandQuitExecution.bye_bytes /\
 meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 induction requests as [|request requests IH]; intros native logical suffix observations Hshape Hpositive Hboundary Hextra Hcapacity Hinput.
 - destruct(NativeSession.generated_quit native logical suffix observations (NativeDialogueComposition.state _ _ Hboundary)
    (NativeDialogueComposition.token _ _ Hboundary) (NativeDialogueComposition.error _ _ Hboundary) Hinput)
   as(Hrun & Hstate & Hin & Hout & Hstop & Herror).
   exists(QuitLoopExecution.loop_result native suffix),[],logical. split;[reflexivity|]. split;[exact Hrun|].
   split;[apply Protocol.dialogue_quit|]. repeat first[assumption|split].
 - inversion Hshape as [|request' requests' Hrequest Hrequests];subst request' requests'.
   inversion Hpositive as [|request' requests' HrequestPositive HrequestsPositive];subst request' requests'.
   assert(Hwire:stdin native=Protocol.request_bytes request++(Protocol.wire(requests++[NativeSession.quit])++suffix)).
   { rewrite NativeGeneralSuffixSession.wire_quit. rewrite <-NativeSession.input_cons. exact Hinput. }
   destruct(NativeSetSuffixCommand.commands native logical request (requests++[NativeSession.quit]) suffix observations
    Hboundary Hextra Hcapacity Hrequest HrequestPositive Hwire)
   as(ch & unread & after & reply & next & Hbyte & Hbytes & Hcommand & Hstep & HnextBoundary & HnextExtra & HnextCapacity & Hin & Hout).
   rewrite NativeGeneralSuffixSession.wire_quit in Hin,Hcommand.
   destruct(IH after next suffix (observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=NativeSession.input requests suffix|}])
    Hrequests HrequestsPositive HnextBoundary HnextExtra HnextCapacity Hin)
   as(final & replies & target & Hlength & Hrun & Hdialogue & Hstate & HfinalInput & HfinalOutput & HfinalStop & HfinalError).
   exists final,(reply::replies),target. split;[cbn [length];congruence|]. split.
   + cbn [NativeSession.schedule]. eapply DialogueExecution.next with (ch:=ch) (tail:=unread) (after:=after).
     * exact Hbyte.
     * exact Hbytes.
     * pose proof(NativeSession.represented_meta native logical (NativeDialogueComposition.state _ _ Hboundary));lia.
     * exact Hcommand.
     * pose proof(NativeSession.represented_meta after next (NativeDialogueComposition.state _ _ HnextBoundary));lia.
     * exact(NativeDialogueComposition.running _ _ HnextBoundary).
     * rewrite Hout,<-app_assoc in Hrun. exact Hrun.
   + split.
     * cbn [app]. apply Protocol.dialogue_step with (t:=next);[exact HrequestPositive|exact Hstep|exact Hdialogue].
     * split;[exact Hstate|]. split;[exact HfinalInput|]. split.
       -- cbn [NativeSession.output]. now rewrite Hout in HfinalOutput.
       -- split;assumption.
Qed.
Theorem generated_main key0 key1 requests suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Forall Protocol.shape requests -> Forall(fun request=>Protocol.opcode request<>0%nat) requests ->
 NativeSetBudgetPlan.domain (requests++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length requests /\
 Protocol.dialogue Protocol.initial (requests++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeSession.input requests suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeSession.input requests suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeSession.input requests suffix|}]++
 NativeSession.schedule Protocol.handshake_output requests replies suffix)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\
 stdin final=suffix /\ meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 intros Hkey0 Hkey1 Hshape Hpositive Hdomain.
 destruct(NativeStartupCompact.main_to_commands key0 key1(NativeSession.input requests suffix)bs ns Hkey0 Hkey1)
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
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeSession.input requests suffix|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeSession.input requests suffix|}]).
 destruct(generated_finite requests ready Protocol.initial suffix observations Hshape Hpositive Hboundary Hextra
   (NativeSetBudgetPlan.initial_capacity (requests++[NativeSession.quit]) Hdomain) Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hin & Hout & HstopFinal & Hclear).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|].
 split;[etransitivity;[exact Hmain|exact Hcommands]|]. repeat first[assumption|split].
Qed.
End NativeSetSuffixSession.
