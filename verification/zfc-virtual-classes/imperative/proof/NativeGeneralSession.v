From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeBasicDispatcher NativeFullDispatcher NativeFullTapeStep NativeBudgetFrame NativeBudgetPlan NativeUniformCommand NativeGeneralDispatcher NativeGeneralCommandInvariant
 NativeSchemaFieldBounds NativeNameCompact NativeRequestBounds NativeCommandBoundary FormulaTopology ClassLookup LogicalRegistryBounds
 CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralSession.
Import IndexExecution SipHashExecution.
Definition extra argument_cap native logical := NativeBasicSession.extra native logical /\ NativeSchemaFieldBounds.fields native argument_cap.
Theorem commands argument_cap : NativeDialogueComposition.command_spec (extra argument_cap) (NativeBudgetPlan.capacity argument_cap).
Proof.
 intros native logical request requests observations Hboundary [Hextra Hfields] [caps [Hbounds Hcheck]] Hshape Hpositive Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 destruct(NativeBudgetPlan.check_tail argument_cap caps request requests Hpositive Hcheck) as [Hconditions HtailCheck].
 assert(Hrange:(1<=Protocol.opcode request<=26)%nat) by (pose proof(NativeBudgetPlan.opcode_bound _ _ _ Hconditions);lia).
 destruct(NativeFullDispatcher.request_encoding request Hrange) as [Hwire Hbyte].
 change(stdin native=Protocol.request_bytes request++Protocol.wire requests) in Hinput.
 set(pending:=NativeFullTapeStep.entered native request (Protocol.wire requests)).
 assert(HpendingState:NativeState.represents pending logical) by (unfold pending;now apply NativeBudgetFrame.entered_state).
 assert(HpendingMeta:(31<length(memory pending arraydef_0__meta))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingSip:(0<length(memory pending arraydef_0__sipState))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingToken:(1024<=length(memory pending arraydef_0__token))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingPrint:(20<=length(memory pending arraydef_0__printBuffer))%nat).
 { unfold pending. now rewrite NativeBudgetFrame.entered_lengths. }
 assert(HpendingValue:meta_value pending 15=NativeBasicDispatcher.first(Protocol.opcode request)+1).
 { unfold pending. apply NativeBudgetFrame.entered_pending;lia. }
 assert(HpendingError:meta_value pending 8=0).
 { unfold pending. rewrite NativeBudgetFrame.entered_meta_other by lia. exact Herror. }
 assert(HpendingTop:FormulaTopology.ordered pending(length(Protocol.formulas logical))).
 { unfold pending. now apply NativeBudgetFrame.entered_top. }
 assert(HpendingGood:ClassLookup.wellformed pending).
 { unfold pending. now apply NativeBudgetFrame.entered_class_wellformed. }
 assert(HpendingCompact:NativeNameCompact.compact pending logical).
 { unfold pending. now apply NativeBudgetFrame.entered_compact. }
 assert(HpendingFields:NativeSchemaFieldBounds.fields pending argument_cap).
 { unfold pending. now apply NativeBudgetFrame.entered_fields. }
 pose proof(NativeBudgetPlan.current_resources pending logical argument_cap caps request Hshape HpendingState HpendingTop Hfalse
   HpendingGood HpendingCompact HpendingFields Hbounds Hconditions) as Hresources.
 pose proof(NativeBudgetPlan.arithmetic pending logical argument_cap caps request HpendingState HpendingFields Hbounds Hconditions) as Harithmetic.
 destruct(NativeUniformCommand.generated_canonical pending logical request (fun _=>false) (fun _=>0) (Protocol.wire requests) observations
   (NativeBudgetPlan.formulas caps) (NativeBudgetPlan.indices caps) (NativeBudgetPlan.classes caps) (NativeBudgetPlan.expressions caps) argument_cap
   Hshape Hrange HpendingMeta HpendingSip HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe HpendingTop Hfalse
   HpendingGood Hunique Hresources HpendingCompact Harithmetic eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & Hpost & Hquantitative).
 destruct Hpost as(HnextSafe & HnextTop & HnextGood & HnextCompact & HnextUnique & HnextFalse & HmetaLength & HsipLength & HnextMeta & HnextSip & Hextends & HregistryCounts).
 assert(HnextFields:NativeSchemaFieldBounds.fields after argument_cap).
 { exact(NativeSchemaFieldBounds.preserves pending logical request (fun _=>false) (fun _=>0) (Protocol.wire requests) observations after _ argument_cap
   Hshape Hrange ltac:(lia) HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe
   (NativeGeneralDispatcher.schema_room _ _ _ Hresources) HpendingFields (NativeBudgetPlan.arguments_bound _ _ _ Hconditions) eq_refl Hrun). }
 pose proof(NativeBudgetPlan.capacity_next after logical request requests reply next argument_cap caps Hshape Hpositive Hstep HnextState HnextTop
   Hbounds Hcheck Hquantitative) as HnextCapacity.
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 assert(HpendingStop:meta_value pending 9=meta_value native 9).
 { unfold pending. apply NativeBudgetFrame.entered_meta_other;lia. }
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++Protocol.wire requests),after,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|]. split;[exact Hrun|]. split;[exact Hstep|].
 split;[constructor;try assumption;now rewrite Hstop,HpendingStop|]. split.
 - split;[constructor;assumption|exact HnextFields].
 - split;[exact HnextCapacity|]. split;[exact Hin|exact Hout].
Qed.
Theorem generated_finite argument_cap requests native logical observations :
 Forall Protocol.shape requests -> NativeDialogueComposition.boundary native logical -> extra argument_cap native logical ->
 NativeBudgetPlan.capacity argument_cap logical requests -> stdin native=Protocol.wire requests ->
 exists final replies target remaining,
 DialogueExecution.run native observations final(observations++Protocol.flush_schedule requests replies(stdout native)) /\
 Protocol.dialogue logical requests replies target remaining /\ NativeState.represents final target /\ meta_value final 8=0 /\
 stdout final=stdout native++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 exact(NativeDialogueComposition.generated_finite (extra argument_cap)(NativeBudgetPlan.capacity argument_cap)(commands argument_cap)
   requests native logical observations).
Qed.
Theorem generated_main argument_cap key0 key1 requests bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall Protocol.shape requests ->
 NativeBudgetPlan.capacity argument_cap Protocol.initial requests ->
 exists replies final logical remaining,
 Protocol.dialogue Protocol.initial requests replies logical remaining /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(Protocol.wire requests)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]++
 Protocol.flush_schedule requests replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=remaining.
Proof.
 intros Hkey0 Hkey1 Hshape Hcapacity.
 destruct(NativeStartupCompact.main_to_commands key0 key1(Protocol.wire requests)bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hextra:extra argument_cap ready Protocol.initial).
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
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++Protocol.wire requests|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=Protocol.wire requests|}]).
 destruct(generated_finite argument_cap requests ready Protocol.initial observations Hshape Hboundary Hextra Hcapacity Hinput)
 as(final & replies & logical & remaining & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as HcommandsRun.
 rewrite Houtput in HcommandsRun,Hout.
 exists replies,final,logical,remaining. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact HcommandsRun]|]. split;assumption.
Qed.
(** All twenty-six positive opcodes, quit and EOF, for the actual seeded main
    program. The only resource domain is the finite numeric Boolean plan. *)
Theorem required bs ns : Spec.required(funcdef_0__main bs ns)(arrays _ environment1)NativeBudgetPlan.domain.
Proof.
 intros key0 key1 requests Hkey0 Hkey1 Hshape Hdomain.
 destruct(generated_main (NativeRequestBounds.maximum requests) key0 key1 requests bs ns Hkey0 Hkey1 Hshape
   (NativeBudgetPlan.initial_capacity requests Hdomain))
 as(replies & final & logical & remaining & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical,remaining. split;[exact Hdialogue|]. split;[exact Hsafe|]. split;[exact Hrun|]. split;assumption.
Qed.
End NativeGeneralSession.
