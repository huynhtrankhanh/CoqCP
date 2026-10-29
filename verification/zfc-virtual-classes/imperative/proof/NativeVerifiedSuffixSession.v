From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeStartupCompact NativeBasicSession NativeDialogueComposition
 NativeVerifiedDomain NativeGeneralSuffixSession NativeSetSuffixSession NativeGeneralSession NativeGeneralSuffixCommand NativeBudgetFrame NativeBudgetPlan NativeRequestBounds NativeNameCompact
 FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop CommandQuit QuitLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeVerifiedSuffixSession.
Import IndexExecution SipHashExecution.
Theorem generated_main key0 key1 requests suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum ->
 Forall Protocol.shape requests -> Forall(fun request=>Protocol.opcode request<>0%nat) requests ->
 NativeVerifiedDomain.within_capacity (requests++[NativeSession.quit]) ->
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
 intros Hkey0 Hkey1 Hshape Hpositive Hcapacity.
 apply NativeVerifiedDomain.domain_iff in Hcapacity.
 destruct Hcapacity as [Hgeneral|Hsets].
 - exact(NativeGeneralSuffixSession.generated_main key0 key1 requests suffix bs ns Hkey0 Hkey1 Hshape Hpositive Hgeneral).
 - exact(NativeSetSuffixSession.generated_main key0 key1 requests suffix bs ns Hkey0 Hkey1 Hshape Hpositive Hsets).
Qed.
End NativeVerifiedSuffixSession.
