From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeBasicDispatcher NativeFullDispatcher NativeFullTapeStep NativeBudgetFrame NativeBudgetPlan NativeGeneralSession NativeUniformCommand NativeGeneralDispatcher NativeGeneralCommandInvariant
 NativeSchemaFieldBounds NativeNameCompact NativeRequestBounds NativeCommandBoundary FormulaTopology ClassLookup LogicalRegistryBounds
 CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralSuffixCommand.
Import IndexExecution SipHashExecution.
Definition command_spec (extra:Machine->Protocol.state->Prop)
 (capacity:Protocol.state->list Protocol.request->Prop) :=
 forall native logical request requests suffix observations,
 NativeDialogueComposition.boundary native logical -> extra native logical -> capacity logical (request::requests) ->
 Protocol.shape request -> Protocol.opcode request<>0%nat ->
 stdin native=Protocol.request_bytes request++(Protocol.wire requests++suffix) ->
 exists ch unread after reply next,
 0<=ch<256 /\ stdin native=ch::unread /\
 execObserved (funcdef_0__command (fun _=>false) (fun _=>0))
   (CommandLoopExecution.pending_state (withInput native unread) ch,observations)=
 Some(tt,(after,observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;
   unreadInput:=Protocol.wire requests++suffix|}])) /\
 Protocol.step logical request reply next /\ NativeDialogueComposition.boundary after next /\ extra after next /\
 capacity next requests /\ stdin after=Protocol.wire requests++suffix /\
 stdout after=stdout native++Protocol.reply_bytes reply.
Theorem commands argument_cap : command_spec (NativeGeneralSession.extra argument_cap) (NativeBudgetPlan.capacity argument_cap).
Proof.
 intros native logical request requests suffix observations Hboundary [Hextra Hfields] [caps [Hbounds Hcheck]] Hshape Hpositive Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 destruct(NativeBudgetPlan.check_tail argument_cap caps request requests Hpositive Hcheck) as [Hconditions HtailCheck].
 assert(Hrange:(1<=Protocol.opcode request<=26)%nat) by (pose proof(NativeBudgetPlan.opcode_bound _ _ _ Hconditions);lia).
 destruct(NativeFullDispatcher.request_encoding request Hrange) as [Hwire Hbyte].
 change(stdin native=Protocol.request_bytes request++(Protocol.wire requests++suffix)) in Hinput.
 set(pending:=NativeFullTapeStep.entered native request ((Protocol.wire requests++suffix))).
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
 destruct(NativeUniformCommand.generated_canonical pending logical request (fun _=>false) (fun _=>0) ((Protocol.wire requests++suffix)) observations
   (NativeBudgetPlan.formulas caps) (NativeBudgetPlan.indices caps) (NativeBudgetPlan.classes caps) (NativeBudgetPlan.expressions caps) argument_cap
   Hshape Hrange HpendingMeta HpendingSip HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe HpendingTop Hfalse
   HpendingGood Hunique Hresources HpendingCompact Harithmetic eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & Hpost & Hquantitative).
 destruct Hpost as(HnextSafe & HnextTop & HnextGood & HnextCompact & HnextUnique & HnextFalse & HmetaLength & HsipLength & HnextMeta & HnextSip & Hextends & HregistryCounts).
 assert(HnextFields:NativeSchemaFieldBounds.fields after argument_cap).
 { exact(NativeSchemaFieldBounds.preserves pending logical request (fun _=>false) (fun _=>0) ((Protocol.wire requests++suffix)) observations after _ argument_cap
   Hshape Hrange ltac:(lia) HpendingToken HpendingPrint HpendingValue HpendingError HpendingState Hsafe
   (NativeGeneralDispatcher.schema_room _ _ _ Hresources) HpendingFields (NativeBudgetPlan.arguments_bound _ _ _ Hconditions) eq_refl Hrun). }
 pose proof(NativeBudgetPlan.capacity_next after logical request requests reply next argument_cap caps Hshape Hpositive Hstep HnextState HnextTop
   Hbounds Hcheck Hquantitative) as HnextCapacity.
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 assert(HpendingStop:meta_value pending 9=meta_value native 9).
 { unfold pending. apply NativeBudgetFrame.entered_meta_other;lia. }
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++(Protocol.wire requests++suffix)),after,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|]. split;[exact Hrun|]. split;[exact Hstep|].
 split;[constructor;try assumption;now rewrite Hstop,HpendingStop|]. split.
 - split;[constructor;assumption|exact HnextFields].
 - split;[exact HnextCapacity|]. split;[exact Hin|exact Hout].
Qed.
End NativeGeneralSuffixCommand.
