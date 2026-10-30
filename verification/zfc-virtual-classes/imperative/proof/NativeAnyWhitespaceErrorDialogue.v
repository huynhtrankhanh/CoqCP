From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat NativeSetMalformedDialogue NativeGeneralMalformedDialogue NativeAnyWhitespaceErrorStop NativeStopDialogue NativeFastDomain NativeVerifiedDomain NativeSeedInputTransport NativeWhitespaceDialogue FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeAnyWhitespaceErrorDialogue.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_main key0 key1 frames spaces chars extra tail bs ns :
 Forall TokenByteExecution.separator spaces ->
 length chars=1024%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeGeneralPrefixStop.wire frames++(spaces++chars++extra::tail))[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralPrefixStop.wire frames++(spaces++chars++extra::tail)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(spaces++chars++extra::tail)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (spaces++chars++extra::tail)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hspaces Hlength Hbytes Hextra Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 apply NativeStopDialogue.generated_main; try assumption.
 exact(NativeAnyWhitespaceErrorStop.too_long spaces chars extra tail Hspaces Hlength Hbytes Hextra Hbad).
Qed.
Theorem flexible_seeds key0 key1 prefix0 prefix1 sep0 sep1 frames spaces chars extra tail bs ns :
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall TokenByteExecution.separator spaces ->
 length chars=1024%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep0 sep1 (NativeGeneralPrefixStop.wire frames++(spaces++chars++extra::tail)),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep0::(prefix1++decimalBytes key1++sep1::(NativeGeneralPrefixStop.wire frames++(spaces++chars++extra::tail)))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(spaces++chars++extra::tail)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (spaces++chars++extra::tail)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hsep0 Hsep1 Hprefix0 Hprefix1 Hspaces Hlength Hbytes Hextra Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 destruct(generated_main key0 key1 frames spaces chars extra tail bs ns Hspaces Hlength Hbytes Hextra Hbad Hkey0 Hkey1 Hvalid Hcapacity)
 as(replies & final & logical & Hlength' & Hdialogue & Hsafe & Hstop & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
Theorem malformed_eof_main key0 key1 frames spaces chars prefix bad suffix bs ns :
 Forall TokenByteExecution.separator spaces ->
 (0<length chars<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 prefix++bad::suffix=chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeGeneralPrefixStop.wire frames++(spaces++chars))[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralPrefixStop.wire frames++(spaces++chars)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(spaces++chars)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (spaces++chars)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=[].
Proof.
 intros Hspaces Hlength Hbytes Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 apply NativeStopDialogue.generated_main; try assumption.
 exact(NativeAnyWhitespaceErrorStop.malformed_eof spaces chars prefix bad suffix Hspaces Hlength Hbytes Hencoding Hdigits Hbound Hbad).
Qed.
Theorem malformed_eof_flexible_seeds key0 key1 prefix0 prefix1 sep0 sep1 frames spaces chars prefix bad suffix bs ns :
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall TokenByteExecution.separator spaces ->
 (0<length chars<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 prefix++bad::suffix=chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep0 sep1 (NativeGeneralPrefixStop.wire frames++(spaces++chars)),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep0::(prefix1++decimalBytes key1++sep1::(NativeGeneralPrefixStop.wire frames++(spaces++chars)))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(spaces++chars)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (spaces++chars)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=[].
Proof.
 intros Hsep0 Hsep1 Hprefix0 Hprefix1 Hspaces Hlength Hbytes Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 destruct(malformed_eof_main key0 key1 frames spaces chars prefix bad suffix bs ns Hspaces Hlength Hbytes Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity)
 as(replies & final & logical & Hlength' & Hdialogue & Hsafe & Hstop & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
Theorem malformed_main key0 key1 frames spaces chars sep tail prefix bad suffix bs ns :
 Forall TokenByteExecution.separator spaces ->
 (0<length chars<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 TokenByteExecution.separator sep -> prefix++bad::suffix=chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeGeneralPrefixStop.wire frames++(spaces++chars++sep::tail))[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralPrefixStop.wire frames++(spaces++chars++sep::tail)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(spaces++chars++sep::tail)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (spaces++chars++sep::tail)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 apply NativeStopDialogue.generated_main; try assumption.
 exact(NativeAnyWhitespaceErrorStop.malformed spaces chars sep tail prefix bad suffix Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad).
Qed.
Theorem malformed_flexible_seeds key0 key1 prefix0 prefix1 sep0 sep1 frames spaces chars sep tail prefix bad suffix bs ns :
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> Forall TokenByteExecution.separator prefix0 -> Forall TokenByteExecution.separator prefix1 ->
 Forall TokenByteExecution.separator spaces ->
 (0<length chars<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 TokenByteExecution.separator sep -> prefix++bad::suffix=chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeFastDomain.within_capacity (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate key0 key1 prefix0 prefix1 sep0 sep1 (NativeGeneralPrefixStop.wire frames++(spaces++chars++sep::tail)),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=prefix0++decimalBytes key0++sep0::(prefix1++decimalBytes key1++sep1::(NativeGeneralPrefixStop.wire frames++(spaces++chars++sep::tail)))|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(spaces++chars++sep::tail)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (spaces++chars++sep::tail)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hsep0 Hsep1 Hprefix0 Hprefix1 Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity.
 destruct(malformed_main key0 key1 frames spaces chars sep tail prefix bad suffix bs ns Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hcapacity)
 as(replies & final & logical & Hlength' & Hdialogue & Hsafe & Hstop & Hrun & Hout & Hin).
 exists replies,final,logical. repeat first [assumption|split].
 eapply NativeSeedInputTransport.generated; eassumption.
Qed.
End NativeAnyWhitespaceErrorDialogue.
