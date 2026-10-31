From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat NativeGeneralStopDialogue NativeSetStopDialogue NativeFlexibleStopDialogue NativeByteErrorNumericReader NativeTagLaterByteErrorStop NativeFastDomain NativeVerifiedDomain NativeStopDialogue NativeSeedInputTransport NativeWhitespaceDialogue FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeTagLaterByteErrorDialogue.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_11_2 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 11=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input)) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_11_2 digit digits leading sep0 value1 space1 sep1 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
Theorem generated_11_3 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 11=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_11_3 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
Theorem generated_11_4 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 11=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_11_4 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
Theorem generated_22_2 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input)) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_22_2 digit digits leading sep0 value1 space1 sep1 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
Theorem generated_22_3 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input)))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_22_3 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
Theorem generated_22_4 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input))))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_22_4 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
Theorem generated_22_5 key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 value4 space4 sep4 input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 Z.of_nat value4<=maximum -> Forall TokenByteExecution.separator space4 -> TokenByteExecution.separator sep4 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))))),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))))))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))))|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input)))))++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hvalue4 Hspace4 Hsep4 Hbytes Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input))))) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeTagLaterByteErrorStop.generated_22_5 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 value4 space4 sep4 input tail Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hvalue4 Hspace4 Hsep4 Hbytes Hbad) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
End NativeTagLaterByteErrorDialogue.
