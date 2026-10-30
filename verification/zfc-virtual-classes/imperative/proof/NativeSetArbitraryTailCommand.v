From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees Spec.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeBasicDispatcher NativeBasicCommandInvariant NativeFullDispatcher NativeFullTapeStep NativeBudgetFrame NativeSetBudgetPlan NativeSetSchemaSession NativeGeneralArbitraryTailCommand NativeGeneralDispatcher NativeGeneralCommandInvariant
 NativeProofSession NativeSchemaInvariant NativeSchemaFlat NativeSetClassInvariant NativeSchemaSetBoundedBoundary NativeSchemaInstanceBoundary SchemaInstanceCommand
 SchemaEvaluationSetCell NativeNameCompact NativeRequestBounds NativeCommandBoundary NativeCommandLengths FormulaTopology ClassLookup LogicalRegistryBounds LogicalStorageMonotone
 CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSetArbitraryTailCommand.
Import IndexExecution SipHashExecution.
Theorem commands : NativeGeneralArbitraryTailCommand.command_spec NativeSetSchemaSession.extra NativeSetBudgetPlan.capacity.
Proof.
 intros native logical request requests suffix observations Hboundary [Hextra [Hflat Hsets]] [caps [Hbounds Hcheck]] Hshape Hpositive Hinput.
 destruct Hboundary as [Hstate Htoken Hprint Herror Hrunning].
 destruct Hextra as [Hmeta Hsip Hsafe Htop Hfalse Hgood Hunique Hcompact].
 destruct(NativeSetBudgetPlan.check_tail caps request requests Hpositive Hcheck) as [Hconditions HtailCheck].
 assert(Hrange:(1<=Protocol.opcode request<=26)%nat) by (pose proof(NativeSetBudgetPlan.opcode_bound _ _ Hconditions);lia).
 destruct(NativeFullDispatcher.request_encoding request Hrange) as [Hwire Hbyte].
 change(stdin native=Protocol.request_bytes request++suffix) in Hinput.
 set(pending:=NativeFullTapeStep.entered native request (suffix)).
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
 assert(HpendingFlat:NativeSchemaFlat.flat pending) by(unfold pending;now apply NativeSchemaFlat.entered).
 destruct(NativeSetSchemaSession.generated_command pending logical request (fun _=>false) (fun _=>0)(suffix)observations caps
   Hshape Hpositive HpendingMeta HpendingSip HpendingToken HpendingPrint HpendingValue HpendingError HpendingState
   ltac:(split;[constructor;assumption|split;assumption]) Hbounds Hconditions eq_refl)
 as(after & reply & next & Hrun & Hstep & HnextState & Hio & HnextExtra & Hquantitative).
 pose proof(NativeSetBudgetPlan.capacity_next logical request requests reply next caps Hshape Hpositive Hstep Hbounds Hcheck Hquantitative) as HnextCapacity.
 destruct Hio as(Hin & Hout & HnextToken & HnextPrint & Hclear & Hstop).
 assert(HpendingStop:meta_value pending 9=meta_value native 9).
 { unfold pending. apply NativeBudgetFrame.entered_meta_other;lia. }
 exists(NativeBasicDispatcher.first(Protocol.opcode request)),(NativeBasicDispatcher.rest request++suffix),after,reply,next.
 split;[exact Hbyte|]. split;[rewrite Hinput,Hwire;reflexivity|]. split;[exact Hrun|]. split;[exact Hstep|].
 split;[constructor;try assumption;now rewrite Hstop,HpendingStop|]. split.
 - exact HnextExtra.
 - split;[exact HnextCapacity|]. split;[exact Hin|exact Hout].
Qed.
End NativeSetArbitraryTailCommand.
