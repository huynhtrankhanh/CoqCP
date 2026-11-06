From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeFastDomain NativeSeedInputTransport NativeWhitespaceDialogue
 NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaSpacedGeneralMain NativeWhitespaceSchemaSpacedSetMain NativeWhitespaceSchemaStopGeneralMain NativeWhitespaceSchemaStopSetMain NativeGeneralPrefixStop NativeVerifiedDomain CommandQuit SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaStopDialogue.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral.
Theorem generated_main key0 key1 prefix0 prefix1 sep sep2 items ending remaining bs ns :
 NativeGeneralPrefixStop.stop_spec ending remaining ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid_item items -> NativeFastDomain.within_capacity (map req items) ->
 exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items) replies logical [] /\ Guarantees.safe logical /\
 meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep sep2(wire items ending),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep::(prefix1++decimalBytes key1++sep2::(wire items ending))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items ending|}]++schedule items replies ending Protocol.handshake_output++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=remaining|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=remaining.
Proof.
 intros Hstop Hkey0 Hkey1 Hsep Hsep2 Hprefix0 Hprefix1 Hvalid Hcapacity.
 apply NativeFastDomain.domain_exact,NativeVerifiedDomain.domain_iff in Hcapacity.
 assert(Hcanonical:exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items) replies logical [] /\ Guarantees.safe logical /\
 meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire items ending)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire items ending|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items ending|}]++schedule items replies ending Protocol.handshake_output++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=remaining|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=remaining).
 { destruct Hcapacity as [Hgeneral|Hsets].
   - exact(NativeWhitespaceSchemaStopGeneralMain.generated_main key0 key1 items ending remaining bs ns Hstop Hkey0 Hkey1 Hvalid Hgeneral).
   - exact(NativeWhitespaceSchemaStopSetMain.generated_main key0 key1 items ending remaining bs ns Hstop Hkey0 Hkey1 Hvalid Hsets). }
 destruct Hcanonical as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hflag & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeWhitespaceSchemaStopDialogue.
