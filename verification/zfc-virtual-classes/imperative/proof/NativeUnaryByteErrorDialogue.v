From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat NativeGeneralStopDialogue NativeSetStopDialogue NativeFlexibleStopDialogue NativeUnaryByteErrorStop NativeFastDomain NativeVerifiedDomain NativeStopDialogue NativeSeedInputTransport NativeWhitespaceDialogue FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeUnaryByteErrorDialogue.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames leading separator input tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator ->
 ByteProtocol.byte_stream input -> NativeUnaryByteErrorStop.error_tail(ByteProtocol.read_number input)=Some tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(leading++52::separator::input)),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(leading++52::separator::input)))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(leading++52::separator::input)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (leading++52::separator::input)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hleading Hseparator Hinput Herror Hkey0 Hkey1 Hvalid Hcapacity.
 exact(NativeFlexibleStopDialogue.generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames (leading++52::separator::input) tail bs ns
 Hs0 Hs1 Hp0 Hp1 (NativeUnaryByteErrorStop.generated leading separator input tail Hleading Hseparator Hinput Herror) Hkey0 Hkey1 Hvalid Hcapacity).
Qed.
End NativeUnaryByteErrorDialogue.
