From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeFastDomain NativeSeedInputTransport NativeWhitespaceDialogue
 NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaMixedGeneralMain NativeWhitespaceSchemaMixedSetMain NativeVerifiedDomain CommandQuit SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaMixedDialogue.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaMixedGeneral.
Theorem eof key0 key1 prefix0 prefix1 sep sep2 frames ending bs ns :
 Forall TokenByteExecution.separator ending ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid frames -> NativeFastDomain.within_capacity (map request frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep sep2(wire frames ending),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep::(prefix1++decimalBytes key1++sep2::(wire frames ending))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames ending|}]++schedule frames replies ending Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hending Hkey0 Hkey1 Hsep Hsep2 Hprefix0 Hprefix1 Hvalid Hcapacity.
 apply NativeFastDomain.domain_exact,NativeVerifiedDomain.domain_iff in Hcapacity.
 assert(Hcanonical:exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map request frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire frames ending)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire frames ending|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames ending|}]++schedule frames replies ending Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[]).
 { destruct Hcapacity as [Hgeneral|Hsets].
   - exact(NativeWhitespaceSchemaMixedGeneralMain.generated_main key0 key1 frames ending bs ns Hending Hkey0 Hkey1 Hvalid Hgeneral).
   - exact(NativeWhitespaceSchemaMixedSetMain.generated_main key0 key1 frames ending bs ns Hending Hkey0 Hkey1 Hvalid Hsets). }
 destruct Hcanonical as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeWhitespaceSchemaMixedDialogue.
