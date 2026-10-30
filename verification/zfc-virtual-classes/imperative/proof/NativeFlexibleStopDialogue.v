From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat NativeGeneralStopDialogue NativeSetStopDialogue NativeFastDomain NativeVerifiedDomain NativeStopDialogue NativeSeedInputTransport NativeWhitespaceDialogue FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeFlexibleStopDialogue.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames ending tail bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 NativeGeneralPrefixStop.stop_spec ending tail ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++ending),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++ending))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++ending|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output ending++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hstop Hkey0 Hkey1 Hvalid Hcapacity.
 destruct(NativeStopDialogue.generated_main key0 key1 frames ending tail bs ns Hstop Hkey0 Hkey1 Hvalid Hcapacity)
 as(replies & final & logical & Hlen & Hdialogue & Hsafe & Hstopped & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeFlexibleStopDialogue.
