From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ReadOne ReadTwo Intern ReplyOK ReplyNO
 Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation
 NativeState SchemaProtocolFrame ObservedLocal EffectFrame MetaCellFrame PrintingFrame ImmutableStorage ImmutableHandlers
 RenameStorage AxiomStorage SchemaEvaluationPreservation SchemaInstanceStorage CommandStructure CommandChain CommandQuit CommandSchemaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeStateFrames.
Import IndexExecution SipHashExecution.
(** The mutable formula arena may grow while all registries keep their raw
    storage. Semantic schema transport additionally uses the protocol step. *)
Record registries (before after:Machine) : Prop := Registries {
 binding_count : meta_value after 4=meta_value before 4;
 name_count : meta_value after 5=meta_value before 5;
 schema_count : meta_value after 16=meta_value before 16;
 names : memory after arraydef_0__names=memory before arraydef_0__names;
 bindings : memory after arraydef_0__bindings=memory before arraydef_0__bindings;
 schemas : memory after arraydef_0__schemaNodes=memory before arraydef_0__schemaNodes
}.
Lemma refl native : registries native native.
Proof. constructor;reflexivity. Qed.
Lemma trans before middle after : registries before middle -> registries middle after -> registries before after.
Proof. intros [Hb Hn Hs Hna Hba Hsa] [Hb' Hn' Hs' Hna' Hba' Hsa'];constructor;congruence. Qed.
Lemma read_one native ch chars value sep tail :
 (17<length(memory native arraydef_0__meta))%nat ->
 registries native (ReadOne.argument_state native ch chars value sep tail).
Proof.
 intro Hmeta. constructor.
 - rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). reflexivity.
 - rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). reflexivity.
 - rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). reflexivity.
 - apply ReadOne.argument_other;discriminate.
 - apply ReadOne.argument_other;discriminate.
 - apply ReadOne.argument_other;discriminate.
Qed.
Lemma read_two native ch chars a middle b last tail :
 (17<length(memory native arraydef_0__meta))%nat ->
 registries native (ReadTwo.second_state native ch chars a middle b last tail).
Proof.
 intro Hmeta. constructor.
 - rewrite ReadTwo.second_meta_other by (try exact Hmeta;lia). reflexivity.
 - rewrite ReadTwo.second_meta_other by (try exact Hmeta;lia). reflexivity.
 - rewrite ReadTwo.second_meta_other by (try exact Hmeta;lia). reflexivity.
 - apply ReadTwo.second_other;discriminate.
 - apply ReadTwo.second_other;discriminate.
 - apply ReadTwo.second_other;discriminate.
Qed.
Lemma intern before after : InternExecution.logical_frame before after -> registries before after.
Proof.
 intros [Ha [Hc Hio]]. constructor.
 - apply Hc;lia.
 - apply Hc;lia.
 - apply Hc;lia.
 - apply Ha;discriminate.
 - apply Ha;discriminate.
 - apply Ha;discriminate.
Qed.
Lemma reply_ok native index : registries native (ReplyOKExecution.reply_state native index).
Proof.
 constructor;try (unfold meta_value;rewrite ReplyOKExecution.reply_other by discriminate;reflexivity);
 apply ReplyOKExecution.reply_other;discriminate.
Qed.
Lemma reply_no native : registries native (ReplyNOExecution.reply_state native).
Proof. constructor;reflexivity. Qed.
Lemma names_preserved before after logical : registries before after ->
 NameRepresentation.represents before logical -> NameRepresentation.represents after logical.
Proof.
 intros Hframe Hrep. unfold NameRepresentation.represents in *.
 rewrite (binding_count _ _ Hframe),(name_count _ _ Hframe),(names _ _ Hframe),(bindings _ _ Hframe).
 exact Hrep.
Qed.
Theorem finish native final before request reply after :
 NativeState.represents native before -> registries native final ->
 Protocol.step before request reply after -> Protocol.opcode request<>22%nat ->
 Protocol.bindings after=Protocol.bindings before ->
 NativeRepresentation.canonical_arena final (Protocol.formulas after) ->
 ClassStorage.represents final (Protocol.formulas after) (Protocol.classes after) ->
 HistoryRefinement.represents final after -> NativeState.represents final after.
Proof.
 intros Hnative Hframe Hstep HnotNode Hbindings Hformulas Hclasses Hhistory.
 constructor;[exact Hformulas|exact Hclasses|exact Hhistory| |].
 - rewrite Hbindings. eapply names_preserved;[exact Hframe|exact (NativeState.name_representation _ _ Hnative)].
 - eapply SchemaProtocolFrame.preserves;
   [exact (NativeState.schema_representation _ _ Hnative)|exact Hstep|exact HnotNode|
    exact (schema_count _ _ Hframe)|exact (schemas _ _ Hframe)].
Qed.

(** Independent name-table metadata is protected by every handler except the
    three name-binding commands and class certification. *)
Module Counts.
Import MetaCellFrame.
Definition registry_cell cell := cell=4%nat \/ cell=5%nat.
Lemma rename_protected cell : registry_cell cell -> RenameStorage.Cells.protected cell.
Proof. unfold registry_cell,RenameStorage.Cells.protected;intros Hcell;repeat split;lia. Qed.
Lemma print_ro cell {R} (code : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :
  array_ro cell (PrintingFrame.translate_print code).
Proof.
  induction code as [value|effect cont IH]; [constructor|].
  destruct effect as [effect|array slot|array slot value|array size zero].
  - cbn [PrintingFrame.translate_print translateArrays withArraysReturnValueDoBasicEffectArrayType array_ro].
    split; [destruct effect; constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [discriminate|]. intro response. apply IH.
Qed.
#[local] Hint Resolve print_ro : cell_frames.
Theorem intern_ro cell (Hcell:registry_cell cell) bs ns :
 MetaCellFrame.array_ro cell (funcdef_0__intern bs ns).
Proof. exact (RenameStorage.Cells.intern_ro cell (rename_protected cell Hcell) bs ns). Qed.
Local Opaque funcdef_0__intern.
Theorem tokenByte_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__tokenByte bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__readToken bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (tokenByte_ro cell Hcell) as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__readNat bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (readToken_ro cell Hcell) as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__lookup bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro.
Qed.
Local Opaque funcdef_0__lookup.
Theorem ok_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__ok bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body.
  apply local_bind.
  - apply string_ro. intro ch. ro.
  - intros [].
    change (local_ro cell
      ((numberLocalGet _ _ _ vardef_0__ok_value >>= fun value =>
        liftToWithLocalVariables (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned
          (fun _ => false) (update (fun _ => 0%Z) vardef_0_PrintInt64_unsigned_num value))))
      >>= fun _ => writeChar _ _ _ (coerceInt 10 8) >>= fun _ =>
        flush _ _ _ >>= fun _ => Done _ _ _ tt)).
    apply local_bind.
    + apply local_bind; [ro|intro value; apply local_lift; apply print_ro; tauto].
    + intros []. ro.
Qed.
Local Opaque funcdef_0__ok.
Theorem no_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__no bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro.
Qed.
Local Opaque funcdef_0__no.
Theorem appendTheorem_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__appendTheorem bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (ok_ro cell Hcell) as H_ok.
  unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem modusPonens_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__modusPonens bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (appendTheorem_ro cell Hcell) as H_appendTheorem.
  pose proof (no_ro cell Hcell) as H_no.
  unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro.
Qed.
Local Opaque funcdef_0__modusPonens.
Theorem generalize_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__generalize bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (intern_ro cell Hcell) as H_intern.
  pose proof (appendTheorem_ro cell Hcell) as H_appendTheorem.
  unfold funcdef_0__generalize. apply eliminate_ro. unfold funcdef_0__generalize_body. ro.
Qed.
Local Opaque funcdef_0__generalize.
Theorem setness_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__setness bs ns).
Proof.
  unfold registry_cell in Hcell.
  pose proof (RenameStorage.Cells.predicate_ro cell (rename_protected cell Hcell)) as Hdep0.
  pose proof (intern_ro cell Hcell) as Hdep1.
  unfold funcdef_0__setness. apply eliminate_ro. unfold funcdef_0__setness_body. ro.
Qed.
Local Opaque funcdef_0__setness.
Theorem schemaCheck_ro cell (Hcell:registry_cell cell) bs ns : array_ro cell (funcdef_0__schemaCheck bs ns).
Proof.
  unfold registry_cell in Hcell.
  unfold funcdef_0__schemaCheck. apply eliminate_ro. unfold funcdef_0__schemaCheck_body. ro.
Qed.
Local Opaque funcdef_0__schemaCheck.
End Counts.
Definition nonbinding opcode := opcode<>9%nat /\ opcode<>14%nat /\ opcode<>20%nat /\ opcode<>23%nat.
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern funcdef_0__readNat funcdef_0__readToken funcdef_0__lookup
 funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize funcdef_0__classEqual funcdef_0__classMember
 funcdef_0__axiom funcdef_0__bindName funcdef_0__setness funcdef_0__schemaInstance funcdef_0__schemaCheck.
Theorem arrays_ro watched (Hprotected:ImmutableStorage.persistent_array watched) opcode : (opcode<=26)%nat -> opcode<>22%nat -> nonbinding opcode ->
 EffectFrame.local_ro watched (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hbound HnotNode [H9 [H14 [H20 H23]]].
 pose proof (ImmutableStorage.readNat_ro watched Hprotected) as HreadNat.
 pose proof (ImmutableStorage.readToken_ro watched Hprotected) as HreadToken.
 pose proof (ImmutableStorage.lookup_ro watched Hprotected) as Hlookup.
 pose proof (ImmutableStorage.ok_ro watched Hprotected) as Hok.
 pose proof (ImmutableStorage.no_ro watched Hprotected) as Hno.
 pose proof (ImmutableStorage.intern_ro watched Hprotected) as Hintern.
 pose proof (ImmutableStorage.appendTheorem_ro watched Hprotected) as HappendTheorem.
 pose proof (ImmutableStorage.modusPonens_ro watched Hprotected) as HmodusPonens.
 pose proof (ImmutableStorage.generalize_ro watched Hprotected) as Hgeneralize.
 pose proof (ImmutableStorage.classEqual_ro watched Hprotected) as HclassEqual.
 pose proof (ImmutableStorage.classMember_ro watched Hprotected) as HclassMember.
 pose proof (ImmutableStorage.axiom_ro watched Hprotected) as Haxiom.
 pose proof (ImmutableStorage.setness_ro watched Hprotected) as Hsetness.
 pose proof (ImmutableStorage.schemaInstance_ro watched Hprotected) as HschemaInstance.
 pose proof (ImmutableStorage.schemaCheck_ro watched Hprotected) as HschemaCheck.
 let rec cases count tag := lazymatch count with
 | O=>idtac
 | S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all: try lia.
 all: match goal with |- context [Z.of_nat ?tag]=>
  let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all: unfold CommandChain.handler_for;cbn beta iota.
 all: unfold CommandStructure.handler_1, CommandStructure.handler_2, CommandStructure.handler_3, CommandStructure.handler_4, CommandStructure.handler_5, CommandStructure.handler_6, CommandStructure.handler_7, CommandStructure.handler_8, CommandStructure.handler_9, CommandStructure.handler_10, CommandStructure.handler_11, CommandStructure.handler_12, CommandStructure.handler_13, CommandStructure.handler_14, CommandStructure.handler_15, CommandStructure.handler_16, CommandStructure.handler_17, CommandStructure.handler_18, CommandStructure.handler_19, CommandStructure.handler_20, CommandStructure.handler_21, CommandStructure.handler_23, CommandStructure.handler_24, CommandStructure.handler_25, CommandStructure.handler_26.
 all: unfold ImmutableStorage.persistent_array in Hprotected.
 all: EffectFrame.ro.
Qed.
Theorem counts_ro cell (Hcell:Counts.registry_cell cell) opcode : (opcode<=26)%nat -> opcode<>22%nat -> nonbinding opcode ->
 MetaCellFrame.local_ro cell (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode)).
Proof.
 intros Hbound HnotNode [H9 [H14 [H20 H23]]].
 pose proof (Counts.readNat_ro cell Hcell) as HreadNat.
 pose proof (Counts.readToken_ro cell Hcell) as HreadToken.
 pose proof (Counts.lookup_ro cell Hcell) as Hlookup.
 pose proof (Counts.ok_ro cell Hcell) as Hok.
 pose proof (Counts.no_ro cell Hcell) as Hno.
 pose proof (Counts.intern_ro cell Hcell) as Hintern.
 pose proof (Counts.appendTheorem_ro cell Hcell) as HappendTheorem.
 pose proof (Counts.modusPonens_ro cell Hcell) as HmodusPonens.
 pose proof (Counts.generalize_ro cell Hcell) as Hgeneralize.
 pose proof (SchemaEvaluationPreservation.classEqual_cells cell (Counts.rename_protected cell Hcell)) as HclassEqual.
 pose proof (SchemaEvaluationPreservation.classMember_cells cell (Counts.rename_protected cell Hcell)) as HclassMember.
 pose proof (AxiomStorage.cells_ro cell (Counts.rename_protected cell Hcell) ltac:(unfold Counts.registry_cell in Hcell;lia)) as Haxiom.
 pose proof (Counts.setness_ro cell Hcell) as Hsetness.
 pose proof (SchemaInstanceStorage.cells cell ltac:(unfold SchemaInstanceStorage.protected_cell;split;[exact (Counts.rename_protected cell Hcell)|unfold Counts.registry_cell in Hcell;repeat split;lia])) as HschemaInstance.
 pose proof (Counts.schemaCheck_ro cell Hcell) as HschemaCheck.
 let rec cases count tag := lazymatch count with
 | O=>idtac
 | S ?rest=>let next:=fresh "opcode" in destruct tag as [|next];[idtac|cases rest next]
 end in cases 27%nat opcode.
 all: try lia.
 all: match goal with |- context [Z.of_nat ?tag]=>
  let value:=eval compute in (Z.of_nat tag) in change (Z.of_nat tag) with value end.
 all: unfold CommandChain.handler_for;cbn beta iota.
 all: unfold CommandStructure.handler_1, CommandStructure.handler_2, CommandStructure.handler_3, CommandStructure.handler_4, CommandStructure.handler_5, CommandStructure.handler_6, CommandStructure.handler_7, CommandStructure.handler_8, CommandStructure.handler_9, CommandStructure.handler_10, CommandStructure.handler_11, CommandStructure.handler_12, CommandStructure.handler_13, CommandStructure.handler_14, CommandStructure.handler_15, CommandStructure.handler_16, CommandStructure.handler_17, CommandStructure.handler_18, CommandStructure.handler_19, CommandStructure.handler_20, CommandStructure.handler_21, CommandStructure.handler_23, CommandStructure.handler_24, CommandStructure.handler_25, CommandStructure.handler_26.
 all: unfold Counts.registry_cell in Hcell.
 all: MetaCellFrame.ro.
Qed.
Lemma local_cell {V} `{EqDecision V} cell
 (code:Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V) withLocalVariablesReturnValue unit)
 f final observations afterObservations :
 MetaCellFrame.local_ro cell code ->
 ObservedLocal.execLocalObserved code (f,observations)=Some(tt,(final,afterObservations)) ->
 meta_value (machine final) cell=meta_value (machine f) cell.
Proof.
 intros Hro Hrun. destruct f as [native bs ns].
 apply (MetaCellFrame.observed_preserves cell (eliminateLocalVariables bs ns code) native observations tt (machine final) afterObservations).
 - apply MetaCellFrame.eliminate_ro;exact Hro.
 - rewrite (ObservedLocal.eliminate_correct code bs ns native observations),Hrun. reflexivity.
Qed.
Theorem generated_registries opcode (f final:CommandQuitExecution.Frame) observations afterObservations :
 (opcode<=26)%nat -> opcode<>22%nat -> nonbinding opcode ->
 ObservedLocal.execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (f,observations)=Some(tt,(final,afterObservations)) ->
 registries (machine f) (machine final).
Proof.
 intros Hbound HnotNode Hnonbinding Hrun. constructor.
 - eapply local_cell;[exact (counts_ro 4%nat (or_introl eq_refl) opcode Hbound HnotNode Hnonbinding)|exact Hrun].
 - eapply local_cell;[exact (counts_ro 5%nat (or_intror eq_refl) opcode Hbound HnotNode Hnonbinding)|exact Hrun].
 - exact (CommandSchemaFrame.local_count _ f final observations afterObservations (CommandSchemaFrame.count_ro opcode Hbound HnotNode) Hrun).
 - eapply ImmutableHandlers.local_observed_preserves;
   [exact (arrays_ro arraydef_0__names ImmutableStorage.name_array_persistent opcode Hbound HnotNode Hnonbinding)|exact Hrun].
 - eapply ImmutableHandlers.local_observed_preserves;
   [exact (arrays_ro arraydef_0__bindings ImmutableStorage.binding_array_persistent opcode Hbound HnotNode Hnonbinding)|exact Hrun].
 - eapply ImmutableHandlers.local_observed_preserves;
   [exact (CommandSchemaFrame.nodes_ro opcode Hbound HnotNode)|exact Hrun].
Qed.
Lemma accepted_bindings before request reply after :
 nonbinding (Protocol.opcode request) -> Protocol.accepted before request reply after ->
 Protocol.bindings after=Protocol.bindings before.
Proof.
 intros [H9 [H14 [H20 H23]]] Haccepted. inversion Haccepted;subst;
 cbn [Protocol.bindings Protocol.with_history];try reflexivity;
 exfalso;first [solve [apply H9;reflexivity]|solve [apply H14;reflexivity]|
   solve [apply H20;reflexivity]|solve [apply H23;reflexivity]].
Qed.
Lemma step_bindings before request reply after :
 nonbinding (Protocol.opcode request) -> Protocol.step before request reply after ->
 Protocol.bindings after=Protocol.bindings before.
Proof.
 intros Hnonbinding Hstep. inversion Hstep;subst.
 - match goal with Hretained:Protocol.retained_storage ?middle after |- _ =>
     destruct Hretained as [_ [_ [_ [_ [Hsame _]]]]];rewrite Hsame end.
   eapply accepted_bindings;eassumption.
 - match goal with Hretained:Protocol.retained_storage before after |- _ =>
     exact (proj1 (proj2 (proj2 (proj2 (proj2 Hretained))))) end.
Qed.
Theorem generated_preserves opcode (f final:CommandQuitExecution.Frame) observations afterObservations before request reply after :
 (opcode<=26)%nat -> opcode<>22%nat -> nonbinding opcode -> Protocol.opcode request=opcode ->
 ObservedLocal.execLocalObserved (CommandChain.handler_for funcdef_0__readNat (Z.of_nat opcode))
   (f,observations)=Some(tt,(final,afterObservations)) ->
 NativeState.represents (machine f) before -> Protocol.step before request reply after ->
 NativeRepresentation.canonical_arena (machine final) (Protocol.formulas after) ->
 ClassStorage.represents (machine final) (Protocol.formulas after) (Protocol.classes after) ->
 HistoryRefinement.represents (machine final) after -> NativeState.represents (machine final) after.
Proof.
 intros Hbound HnotNode Hnonbinding Hopcode Hrun Hnative Hstep Hformulas Hclasses Hhistory.
 eapply finish;[exact Hnative|eapply generated_registries;eassumption|exact Hstep|now rewrite Hopcode|
  eapply step_bindings;[now rewrite Hopcode|exact Hstep]|exact Hformulas|exact Hclasses|exact Hhistory].
Qed.
End NativeStateFrames.
