From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeFastDomain NativeSeedInputTransport NativeWhitespaceDialogue
 NativeGeneralWhitespaceDialogue NativeGeneralWhitespaceQuitDialogue NativeVerifiedWhitespaceDialogue CommandQuit.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAllWhitespaceDialogue.
Import IndexExecution SipHashExecution NativeGeneralWhitespaceDialogue.
Theorem eof key0 key1 prefix0 prefix1 sep sep2 frames bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid frames -> NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep sep2(wire frames),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep::(prefix1++decimalBytes key1++sep2::wire frames)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire frames|}]++schedule frames replies Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hkey0 Hkey1 Hsep Hsep2 Hprefix0 Hprefix1 Hvalid Hcapacity.
 destruct(NativeVerifiedWhitespaceDialogue.eof key0 key1 frames bs ns Hkey0 Hkey1 Hvalid Hcapacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
Theorem quit key0 key1 prefix0 prefix1 sep sep2 frames quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid frames -> Forall TokenByteExecution.separator quit_prefix ->
 NativeFastDomain.within_capacity (map snd frames++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep sep2
   (NativeGeneralWhitespaceQuitDialogue.wire frames quit_prefix suffix),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep::(prefix1++decimalBytes key1++sep2::NativeGeneralWhitespaceQuitDialogue.wire frames quit_prefix suffix)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralWhitespaceQuitDialogue.wire frames quit_prefix suffix|}]++
 NativeGeneralWhitespaceQuitDialogue.schedule frames replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix.
Proof.
 intros Hkey0 Hkey1 Hsep Hsep2 Hprefix0 Hprefix1 Hvalid HquitPrefix Hcapacity.
 destruct(NativeVerifiedWhitespaceDialogue.quit key0 key1 frames quit_prefix suffix bs ns Hkey0 Hkey1 Hvalid HquitPrefix Hcapacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hstop & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeAllWhitespaceDialogue.
