From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeFastDomain NativeVerifiedDomain
 NativeGeneralWhitespaceDialogue NativeSetWhitespaceDialogue NativeGeneralWhitespaceQuitDialogue NativeSetWhitespaceQuitDialogue
 CommandQuit SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeVerifiedWhitespaceDialogue.
Import IndexExecution SipHashExecution NativeGeneralWhitespaceDialogue.
Theorem eof key0 key1 frames bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames|}]++schedule frames replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hvalid Hcapacity. apply NativeFastDomain.domain_exact,NativeVerifiedDomain.domain_iff in Hcapacity.
 destruct Hcapacity as [Hgeneral|Hsets].
 - exact(NativeGeneralWhitespaceDialogue.generated_main key0 key1 frames bs ns Hkey0 Hkey1 Hvalid Hgeneral).
 - exact(NativeSetWhitespaceDialogue.generated_main key0 key1 frames bs ns Hkey0 Hkey1 Hvalid Hsets).
Qed.
Theorem quit key0 key1 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 NativeFastDomain.within_capacity (map snd frames++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeGeneralWhitespaceQuitDialogue.wire frames quit_prefix suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralWhitespaceQuitDialogue.wire frames quit_prefix suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralWhitespaceQuitDialogue.wire frames quit_prefix suffix|}]++
 NativeGeneralWhitespaceQuitDialogue.schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix.
Proof.
 intros Hkey0 Hkey1 Hvalid HquitPrefix Hcapacity. apply NativeFastDomain.domain_exact,NativeVerifiedDomain.domain_iff in Hcapacity.
 destruct Hcapacity as [Hgeneral|Hsets].
 - exact(NativeGeneralWhitespaceQuitDialogue.generated_main key0 key1 frames quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid HquitPrefix Hgeneral).
 - exact(NativeSetWhitespaceQuitDialogue.generated_main key0 key1 frames quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid HquitPrefix Hsets).
Qed.
End NativeVerifiedWhitespaceDialogue.
