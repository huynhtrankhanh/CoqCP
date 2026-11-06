From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeFastDomain NativeSeedInputTransport NativeWhitespaceDialogue
 NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaSpacedGeneralMain NativeWhitespaceSchemaSpacedSetMain NativeWhitespaceSchemaStopGeneralMain NativeWhitespaceSchemaStopSetMain NativeGeneralPrefixStop NativeNumericFirstByteErrorStop NativeMalformedFirstArgumentHandlers NativeMalformedTagHandlers NativeWhitespaceSchemaStopDialogue NativeVerifiedDomain CommandQuit SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaFirstByteError.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral.
Theorem generated_main key0 key1 prefix0 prefix1 sep sep2 items opcode digit digits leading separator input remaining bs ns :
 (NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) \/ NativeMalformedTagHandlers.supported (Z.of_nat opcode)) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator ->
 ByteProtocol.byte_stream input -> NativeNumericFirstByteErrorStop.error_tail(ByteProtocol.read_number input)=Some remaining ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall valid_item items -> NativeFastDomain.within_capacity (map req items) ->
 exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items) replies logical [] /\ Guarantees.safe logical /\
 meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep sep2(wire items (leading++(digit::digits)++separator::input)),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep::(prefix1++decimalBytes key1++sep2::(wire items (leading++(digit::digits)++separator::input)))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items (leading++(digit::digits)++separator::input)|}]++schedule items replies (leading++(digit::digits)++separator::input) Protocol.handshake_output++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=remaining|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=remaining.
Proof.
 intros Hsupported Hword Hop Hleading Hsep Hbytes Herr Hkey0 Hkey1 Hsep0 Hsep1 Hprefix0 Hprefix1 Hvalid Hcapacity.
 apply NativeWhitespaceSchemaStopDialogue.generated_main;try assumption.
 exact(NativeNumericFirstByteErrorStop.generated opcode digit digits leading separator input remaining Hsupported Hword Hop Hleading Hsep Hbytes Herr).
Qed.
End NativeWhitespaceSchemaFirstByteError.
