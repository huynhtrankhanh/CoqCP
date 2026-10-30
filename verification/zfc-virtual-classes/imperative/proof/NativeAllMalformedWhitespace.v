From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat NativeSetMalformedDialogue NativeGeneralMalformedDialogue NativeWhitespaceMalformedStop NativeStopDialogue NativeWhitespaceMalformedDialogue NativeFastDomain NativeVerifiedDomain NativeSeedInputTransport NativeWhitespaceDialogue FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAllMalformedWhitespace.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_main key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 frames ch spaces chars sep tail prefix bad suffix bs ns :
 TokenByteExecution.separator seed_sep0 -> TokenByteExecution.separator seed_sep1 ->
 Forall TokenByteExecution.separator seed_prefix0 -> Forall TokenByteExecution.separator seed_prefix1 ->
 0<=ch<256 -> TokenByteExecution.separator ch -> Forall TokenByteExecution.separator spaces ->
 (0<length chars<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 TokenByteExecution.separator sep -> prefix++bad::suffix=chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 seed_prefix0 seed_prefix1 seed_sep0 seed_sep1 (NativeGeneralPrefixStop.wire frames++(ch::spaces++chars++sep::tail)),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=seed_prefix0++decimalBytes key0++seed_sep0::(seed_prefix1++decimalBytes key1++seed_sep1::(NativeGeneralPrefixStop.wire frames++(ch::spaces++chars++sep::tail)))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(ch::spaces++chars++sep::tail)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (ch::spaces++chars++sep::tail)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hs0 Hs1 Hp0 Hp1 Hch Hsep0 Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 destruct(NativeWhitespaceMalformedDialogue.generated_main key0 key1 frames ch spaces chars sep tail prefix bad suffix bs ns Hch Hsep0 Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity)
 as(replies & final & logical & Hlen & Hdialogue & Hsafe & Hstop & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeAllMalformedWhitespace.
