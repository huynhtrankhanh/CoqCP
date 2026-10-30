From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceEOFDialogue NativeGeneralPrefixStop NativeMalformedOpcodeStop NativeMalformedOpcode ReadNat FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeGeneralMalformedDialogue.
Import IndexExecution SipHashExecution NativeGeneralPrefixStop.
Theorem generated_main key0 key1 frames ch chars sep tail prefix bad suffix bs ns :
 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 TokenByteExecution.separator sep -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid frames ->
 NativeBudgetPlan.domain (map snd frames) ->
 exists replies final logical,
 length replies=length frames /\ Protocol.dialogue Protocol.initial (map snd frames) replies logical [] /\ Guarantees.safe logical /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(NativeGeneralPrefixStop.wire frames++(ch::chars++sep::tail))[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralPrefixStop.wire frames++(ch::chars++sep::tail)|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(ch::chars++sep::tail)|}]++NativeGeneralPrefixStop.schedule_tail frames replies Protocol.handshake_output (ch::chars++sep::tail)++[{|flushedOutput:=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies)++Protocol.reply_bytes Protocol.ERR /\ stdin final=tail.
Proof.
 intros Hch Hnosep Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad Hkey0 Hkey1 Hvalid Hdomain.
 set(argument_cap:=NativeRequestBounds.maximum(map snd frames)).
 destruct(NativeStartupCompact.main_to_commands key0 key1(NativeGeneralPrefixStop.wire frames++(ch::chars++sep::tail))bs ns Hkey0 Hkey1)
 as(ready & Hstate & Htop & Hmeta32 & Hsip1 & Hzero & Herror & Hmeta & Htoken & Hprint & Hstop & Hhistory & Hinput & Houtput & Hmain & Hempty).
 assert(Hboundary:NativeDialogueComposition.boundary ready Protocol.initial) by (constructor;assumption).
 assert(Hextra:NativeGeneralSession.extra argument_cap ready Protocol.initial).
 { split.
   - constructor.
     + lia.
     + lia.
     + exact Guarantees.initial_safe.
     + exact Htop.
     + reflexivity.
     + apply ClassLookup.empty. exact(NativeState.empty_classes _ Hempty).
     + exact LogicalRegistryBounds.initial_unique.
     + apply NativeNameCompact.initial_compact. exact(NativeState.empty_names _ Hempty).
   - exact(NativeBudgetFrame.initial_fields ready argument_cap Hempty). }
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++NativeGeneralPrefixStop.wire frames++(ch::chars++sep::tail)|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralPrefixStop.wire frames++(ch::chars++sep::tail)|}]).
 destruct(NativeGeneralPrefixStop.generated_finite argument_cap frames (ch::chars++sep::tail) tail ready Protocol.initial observations (NativeMalformedOpcodeStop.malformed ch chars sep tail prefix bad suffix Hch Hnosep Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad) Hvalid Hboundary Hextra
   (NativeBudgetPlan.initial_capacity (map snd frames) Hdomain) Hinput)
 as(final & replies & logical & HreplyLength & Hrun & Hdialogue & Hout & Hin & Hstopflag).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact HreplyLength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hstopflag|].
 split;[etransitivity;[exact Hmain|exact Hcommands]|]. split;assumption.
Qed.
End NativeGeneralMalformedDialogue.
