From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash DecimalInput TokenByte NativeState NativeBasicDispatcher NativeCommandBoundary
 NativeClassBinaryBoundary RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds FormulaTopology ClassLookup
 NativeAxiomTotal NativeClassCertifyBoundary ClassCertifyTotal NativeSchemaBoundary SchemaNodeTotal
 NativeSchemaInstanceBoundary SchemaInstanceCommand LogicalNames LogicalHistory.
From NativeProof Require Import NativeFullDispatcher NativeGeneralDispatcher AxiomStorage NativeBasicInvariant NativeBasicCommandInvariant NativeBasicSession NativeAxiomInvariant NativeSchemaInvariant NativeSchemaGeneralInvariant NativeNameCompact NativeCommandLengths LogicalRegistryBounds LogicalStorageMonotone NativeStateFrames ImmutableHandlers ImmutableStorage CommandChain CommandStructure CommandDispatch CommandQuit NativeCommandFrames ObservedLocal RenameMemoControl CommandInput EffectFrame SchemaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
From NativeProof Require Import NativeCheckedResources NativeGeneralCommandInvariant.
Module NativeCheckedDispatcher.
Import IndexExecution SipHashExecution.
Theorem generated_canonical native logical request bs ns tail observations :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (31<length(memory native arraydef_0__meta))%nat -> (0<length(memory native arraydef_0__sipState))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat -> (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 -> meta_value native 8=0 ->
 NativeState.represents native logical -> Guarantees.safe logical ->
 FormulaTopology.ordered native(length(Protocol.formulas logical)) -> nth_error(Protocol.formulas logical)0=Some SetTheory.falsity ->
 ClassLookup.wellformed native -> LogicalRegistryBounds.unique logical -> NativeNameCompact.compact native logical ->
 NativeCheckedResources.check native logical request=true -> stdin native=NativeBasicDispatcher.rest request++tail ->
 exists final reply next,
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,
 observations++[{|flushedOutput:=stdout native++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
 Protocol.step logical request reply next /\ NativeState.represents final next /\
 NativeCommandBoundary.io native final reply tail /\ NativeGeneralCommandInvariant.post native logical final next.
Proof.
 intros Hshape Hrange Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hcompact Hcheck Hinput.
 exact(NativeGeneralCommandInvariant.generated_canonical native logical request bs ns tail observations
  Hshape Hrange Hmeta Hsip Htoken Hprint Hpending Herror Hstate Hsafe Htop Hfalse Hgood Hunique Hcompact
  (NativeCheckedResources.resources native logical request Hshape Hstate Htop Hfalse Hgood Hcheck) Hinput).
Qed.
End NativeCheckedDispatcher.
