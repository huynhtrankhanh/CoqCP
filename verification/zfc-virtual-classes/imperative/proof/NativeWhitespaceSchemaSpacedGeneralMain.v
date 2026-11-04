From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeBasicSession NativeGeneralSession
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceEOFDialogue FormulaTopology ClassLookup LogicalRegistryBounds CommandLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaSpacedGeneralMain.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral.
Theorem generated_main key0 key1 items ending bs ns :
 Forall TokenByteExecution.separator ending ->
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid_item items ->
 NativeBudgetPlan.domain (map req items) ->
 exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items) replies logical [] /\ Guarantees.safe logical /\
 NativeState.represents final logical /\ meta_value final 8=0 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire items ending)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire items ending|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items ending|}]++schedule items replies ending Protocol.handshake_output)) /\
 stdout final=Protocol.handshake_output++concat(map Protocol.reply_bytes replies) /\ stdin final=[].
Proof.
 intros Hending Hkey0 Hkey1 Hvalid Hdomain.
 set(argument_cap:=NativeRequestBounds.maximum(map req items)).
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire items ending)bs ns Hkey0 Hkey1)
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
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire items ending|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items ending|}]).
 destruct(NativeWhitespaceSchemaSpacedGeneral.generated_finite argument_cap items ending ready Protocol.initial observations Hending Hvalid Hboundary Hextra
   (NativeBudgetPlan.initial_capacity (map req items) Hdomain) Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[etransitivity;[exact Hmain|exact Hcommands]|]. split;assumption.
Qed.
End NativeWhitespaceSchemaSpacedGeneralMain.
