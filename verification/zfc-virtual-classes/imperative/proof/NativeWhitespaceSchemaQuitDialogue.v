From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeFastDomain NativeSeedInputTransport NativeWhitespaceDialogue
 NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaQuitGeneral NativeWhitespaceSchemaQuitGeneralMain NativeWhitespaceSchemaQuitSetMain NativeVerifiedDomain CommandQuit SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaQuitDialogue.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral.
Theorem quit key0 key1 prefix0 prefix1 sep sep2 items quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid_item items -> Forall TokenByteExecution.separator quit_prefix ->
 NativeFastDomain.within_capacity (map req items++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep sep2
   (NativeWhitespaceSchemaQuitGeneral.wire items quit_prefix suffix),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep::(prefix1++decimalBytes key1++sep2::NativeWhitespaceSchemaQuitGeneral.wire items quit_prefix suffix)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeWhitespaceSchemaQuitGeneral.wire items quit_prefix suffix|}]++
 NativeWhitespaceSchemaQuitGeneral.schedule items replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix.
Proof.
 intros Hkey0 Hkey1 Hsep Hsep2 Hprefix0 Hprefix1 Hvalid HquitPrefix Hcapacity.
 apply NativeFastDomain.domain_exact,NativeVerifiedDomain.domain_iff in Hcapacity.
 assert(Hcanonical:exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeWhitespaceSchemaQuitGeneral.wire items quit_prefix suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeWhitespaceSchemaQuitGeneral.wire items quit_prefix suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeWhitespaceSchemaQuitGeneral.wire items quit_prefix suffix|}]++
 NativeWhitespaceSchemaQuitGeneral.schedule items replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix).
 { destruct Hcapacity as [Hgeneral|Hsets].
   - exact(NativeWhitespaceSchemaQuitGeneralMain.generated_main key0 key1 items quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid HquitPrefix Hgeneral).
   - exact(NativeWhitespaceSchemaQuitSetMain.generated_main key0 key1 items quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid HquitPrefix Hsets). }
 destruct Hcanonical as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hstop & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeWhitespaceSchemaQuitDialogue.
