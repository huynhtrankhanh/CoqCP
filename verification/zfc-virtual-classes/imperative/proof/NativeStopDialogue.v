From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat NativeGeneralStopDialogue NativeSetStopDialogue NativeFastDomain NativeVerifiedDomain FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeStopDialogue.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_main key0 key1 frames ending tail bs ns :
 NativeGeneralPrefixStop.stop_spec ending tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeGeneralPrefixStop.wire frames++ending)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralPrefixStop.wire frames++ending|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++ending|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output ending++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hstop Hkey0 Hkey1 Hvalid Hcapacity.
 apply NativeFastDomain.domain_exact,NativeVerifiedDomain.domain_iff in Hcapacity.
 destruct Hcapacity as [Hgeneral|Hsets].
 - exact(NativeGeneralStopDialogue.generated_main key0 key1 frames ending tail bs ns Hstop Hkey0 Hkey1 Hvalid Hgeneral).
 - exact(NativeSetStopDialogue.generated_main key0 key1 frames ending tail bs ns Hstop Hkey0 Hkey1 Hvalid Hsets).
Qed.
End NativeStopDialogue.
