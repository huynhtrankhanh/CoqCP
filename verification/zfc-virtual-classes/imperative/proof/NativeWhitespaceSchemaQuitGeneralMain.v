From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeGeneralSession NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaQuitGeneral
 NativeGeneralArbitraryTailCommand NativeGeneralWhitespaceTailCommand NativeWhitespaceQuit NativeBudgetPlan NativeRequestBounds NativeBudgetFrame NativeNameCompact NativeStartupCompact NativeDialogueComposition ClassLookup LogicalRegistryBounds CommandLoop CommandQuit QuitLoop Dialogue SeedBootstrap.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaQuitGeneralMain.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaQuitGeneral.
Theorem generated_main key0 key1 items quit_prefix suffix bs ns :
 Z.of_nat key0<=maximum -> Z.of_nat key1<=maximum -> Forall valid_item items -> Forall TokenByteExecution.separator quit_prefix ->
 NativeBudgetPlan.domain (map req items++[NativeSession.quit]) ->
 exists replies final logical,
 length replies=length items /\ Protocol.dialogue Protocol.initial (map req items++[NativeSession.quit]) (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial key0 key1(wire items quit_prefix suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire items quit_prefix suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items quit_prefix suffix|}]++
 schedule items replies quit_prefix suffix Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=suffix.
Proof.
 intros Hkey0 Hkey1 Hvalid HquitPrefix Hdomain.
 set(argument_cap:=NativeRequestBounds.maximum(map req items++[NativeSession.quit])).
 destruct(NativeStartupCompact.main_to_commands key0 key1(wire items quit_prefix suffix)bs ns Hkey0 Hkey1)
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
 set(observations:=[{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes key0 key1++wire items quit_prefix suffix|};
   {|flushedOutput:=Protocol.handshake_output;unreadInput:=wire items quit_prefix suffix|}]).
 destruct(NativeWhitespaceSchemaQuitGeneral.generated_finite argument_cap items ready Protocol.initial quit_prefix suffix observations Hvalid HquitPrefix Hboundary Hextra
   (NativeBudgetPlan.initial_capacity (map req items++[NativeSession.quit]) Hdomain) Hinput)
 as(final & replies & logical & Hlength & Hrun & Hdialogue & Hfinal & Hclear & Hout & Hin & HstopFinal).
 pose proof(DialogueExecution.generated_commands ready observations final _ bs ns Hrun) as Hcommands.
 rewrite Houtput in Hcommands,Hout.
 exists replies,final,logical. split;[exact Hlength|]. split;[exact Hdialogue|].
 split;[exact(Guarantees.initial_dialogue_safe _ _ _ _ Hdialogue)|]. split;[exact Hfinal|]. split;[exact Hclear|].
 split;[exact HstopFinal|]. split;[etransitivity;[exact Hmain|exact Hcommands]|]. split;assumption.
Qed.
End NativeWhitespaceSchemaQuitGeneralMain.
