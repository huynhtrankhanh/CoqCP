From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal EffectFrame MetaCellFrame ImmutableStorage ImmutableHandlers
 SchemaFrame SchemaCountStorage SchemaRepresentation SchemaProtocolFrame CommandStructure CommandChain CommandQuit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module CommandSchemaFrame.
Import IndexExecution SipHashExecution ObservedLocal.
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern funcdef_0__readNat funcdef_0__readToken funcdef_0__lookup
 funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize funcdef_0__classEqual funcdef_0__classMember
 funcdef_0__axiom funcdef_0__bindName funcdef_0__setness funcdef_0__schemaInstance funcdef_0__schemaCheck.
Theorem nodes_ro opcode : (opcode<=26)%nat -> opcode<>22%nat ->
 EffectFrame.local_ro arraydef_0__schemaNodes (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hbound HnotNode.
 pose proof (ImmutableStorage.readNat_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HreadNat.
 pose proof (ImmutableStorage.readToken_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HreadToken.
 pose proof (ImmutableStorage.lookup_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Hlookup.
 pose proof (ImmutableStorage.ok_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Hok.
 pose proof (ImmutableStorage.no_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Hno.
 pose proof (ImmutableStorage.intern_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Hintern.
 pose proof (ImmutableStorage.appendTheorem_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HappendTheorem.
 pose proof (ImmutableStorage.modusPonens_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HmodusPonens.
 pose proof (ImmutableStorage.generalize_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Hgeneralize.
 pose proof (ImmutableStorage.classEqual_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HclassEqual.
 pose proof (ImmutableStorage.classMember_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HclassMember.
 pose proof (ImmutableStorage.axiom_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Haxiom.
 pose proof (ImmutableStorage.setness_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as Hsetness.
 pose proof (ImmutableStorage.schemaInstance_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HschemaInstance.
 pose proof (ImmutableStorage.schemaCheck_ro arraydef_0__schemaNodes ImmutableStorage.schema_array_persistent) as HschemaCheck.
 pose proof SchemaFrame.bindName_nodes as HbindName.
 let rec cases count tag := lazymatch count with
 | O=>idtac
 | S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all: try lia.
 all: match goal with |- context [Z.of_nat ?tag]=>
  let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all: unfold CommandChain.handler_for;cbn beta iota.
 all: unfold CommandStructure.handler_1, CommandStructure.handler_2, CommandStructure.handler_3, CommandStructure.handler_4, CommandStructure.handler_5, CommandStructure.handler_6, CommandStructure.handler_7, CommandStructure.handler_8, CommandStructure.handler_9, CommandStructure.handler_10, CommandStructure.handler_11, CommandStructure.handler_12, CommandStructure.handler_13, CommandStructure.handler_14, CommandStructure.handler_15, CommandStructure.handler_16, CommandStructure.handler_17, CommandStructure.handler_18, CommandStructure.handler_19, CommandStructure.handler_20, CommandStructure.handler_21, CommandStructure.handler_23, CommandStructure.handler_24, CommandStructure.handler_25, CommandStructure.handler_26.
 all: EffectFrame.ro.
Qed.
Theorem count_ro opcode : (opcode<=26)%nat -> opcode<>22%nat ->
 MetaCellFrame.local_ro 16%nat (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hbound HnotNode.
 pose proof SchemaCountStorage.readNat_ro as HreadNat.
 pose proof SchemaCountStorage.readToken_ro as HreadToken.
 pose proof SchemaCountStorage.lookup_ro as Hlookup.
 pose proof SchemaCountStorage.ok_ro as Hok.
 pose proof SchemaCountStorage.no_ro as Hno.
 pose proof SchemaCountStorage.intern_ro as Hintern.
 pose proof SchemaCountStorage.appendTheorem_ro as HappendTheorem.
 pose proof SchemaCountStorage.modusPonens_ro as HmodusPonens.
 pose proof SchemaCountStorage.generalize_ro as Hgeneralize.
 pose proof SchemaCountStorage.classEqual_ro as HclassEqual.
 pose proof SchemaCountStorage.classMember_ro as HclassMember.
 pose proof SchemaCountStorage.axiom_ro as Haxiom.
 pose proof SchemaCountStorage.setness_ro as Hsetness.
 pose proof SchemaCountStorage.schemaInstance_ro as HschemaInstance.
 pose proof SchemaCountStorage.schemaCheck_ro as HschemaCheck.
 pose proof SchemaCountStorage.bindName_ro as HbindName.
 let rec cases count tag := lazymatch count with
 | O=>idtac
 | S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all: try lia.
 all: match goal with |- context [Z.of_nat ?tag]=>
  let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all: unfold CommandChain.handler_for;cbn beta iota.
 all: unfold CommandStructure.handler_1, CommandStructure.handler_2, CommandStructure.handler_3, CommandStructure.handler_4, CommandStructure.handler_5, CommandStructure.handler_6, CommandStructure.handler_7, CommandStructure.handler_8, CommandStructure.handler_9, CommandStructure.handler_10, CommandStructure.handler_11, CommandStructure.handler_12, CommandStructure.handler_13, CommandStructure.handler_14, CommandStructure.handler_15, CommandStructure.handler_16, CommandStructure.handler_17, CommandStructure.handler_18, CommandStructure.handler_19, CommandStructure.handler_20, CommandStructure.handler_21, CommandStructure.handler_23, CommandStructure.handler_24, CommandStructure.handler_25, CommandStructure.handler_26.
 all: MetaCellFrame.ro.
Qed.
Lemma local_count {V} `{EqDecision V}
 (code:Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V) withLocalVariablesReturnValue unit)
 f final observations afterObservations :
 MetaCellFrame.local_ro 16%nat code -> execLocalObserved code (f,observations)=Some (tt,(final,afterObservations)) ->
 meta_value (machine final) 16=meta_value (machine f) 16.
Proof.
 intros Hro Hrun. destruct f as [s bs ns].
 apply (MetaCellFrame.observed_preserves 16%nat (eliminateLocalVariables bs ns code) s observations tt (machine final) afterObservations).
 - apply MetaCellFrame.eliminate_ro;exact Hro.
 - rewrite (ObservedLocal.eliminate_correct code bs ns s observations),Hrun. reflexivity.
Qed.
Theorem generated_preserves opcode (f final:CommandQuitExecution.Frame) observations afterObservations before request reply after :
 (opcode<=26)%nat -> opcode<>22%nat -> Protocol.opcode request=opcode ->
 execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)) (f,observations)=Some (tt,(final,afterObservations)) ->
 SchemaRepresentation.represents (machine f) before -> Protocol.step before request reply after ->
 SchemaRepresentation.represents (machine final) after.
Proof.
 intros Hbound HnotNode Hopcode Hrun Hrep Hstep.
 eapply SchemaProtocolFrame.preserves;[exact Hrep|exact Hstep|now rewrite Hopcode| |].
 - exact (local_count (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)) f final observations afterObservations (count_ro opcode Hbound HnotNode) Hrun).
 - exact (ImmutableHandlers.local_observed_preserves arraydef_0__schemaNodes (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)) f final observations afterObservations (nodes_ro opcode Hbound HnotNode) Hrun).
Qed.
End CommandSchemaFrame.
