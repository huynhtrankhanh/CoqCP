From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash EffectFrame MetaCellFrame InternalIO InternalIOProcedures
 RenameStorage AxiomStorage SchemaEvaluationFrames SchemaEvaluationPreservation HistoryRefinement NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceStorage.
Import IndexExecution SipHashExecution.
Definition protected_array watched := SchemaEvaluationFrames.persistent watched /\
 arraydef_0__schemaMarks<>watched /\ arraydef_0__schemaValues<>watched.
Lemma mark_arrays watched : arraydef_0__schemaMarks<>watched -> forall bs ns,
 EffectFrame.array_ro watched (funcdef_0__schemaMark bs ns).
Proof. intros Hmarks bs ns. unfold funcdef_0__schemaMark. apply EffectFrame.eliminate_ro. unfold funcdef_0__schemaMark_body. EffectFrame.ro. Qed.
Local Opaque funcdef_0__schemaMark funcdef_0__schemaClass funcdef_0__schemaShiftClass funcdef_0__classEqual funcdef_0__classMember funcdef_0__intern funcdef_0__axiom.
Theorem arrays watched : protected_array watched -> forall bs ns,
 EffectFrame.array_ro watched (funcdef_0__schemaInstance bs ns).
Proof.
 intros [Hprotected [Hmarks Hvalues]] bs ns.
 pose proof (mark_arrays watched Hmarks) as Hmark.
 pose proof (SchemaEvaluationFrames.schemaShift_arrays watched Hprotected) as Hshift.
 pose proof (SchemaEvaluationFrames.schemaClass_arrays watched (proj1 (proj1 Hprotected)) (proj2 Hprotected)) as Hclass.
 pose proof (SchemaEvaluationFrames.classEqual_arrays watched (proj1 Hprotected)) as Hequal.
 pose proof (SchemaEvaluationFrames.classMember_arrays watched (proj1 Hprotected)) as Hmember.
 pose proof (AxiomStorage.arrays_ro watched (proj1 Hprotected)) as Haxiom.
 pose proof (RenameStorage.Arrays.intern_ro watched (proj1 Hprotected)) as Hintern.
 destruct Hprotected as [Hprotected Hclasses]. unfold RenameStorage.Arrays.persistent_array in Hprotected.
 unfold funcdef_0__schemaInstance. apply EffectFrame.eliminate_ro. unfold funcdef_0__schemaInstance_body. EffectFrame.ro.
Qed.
Definition protected_cell cell := RenameStorage.Cells.protected cell /\ cell<>2%nat /\ cell<>13%nat /\ cell<>18%nat.
Local Transparent funcdef_0__schemaMark.
Lemma mark_cells cell bs ns : MetaCellFrame.array_ro cell (funcdef_0__schemaMark bs ns).
Proof. unfold funcdef_0__schemaMark. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__schemaMark_body. MetaCellFrame.ro. Qed.
Local Opaque funcdef_0__schemaMark.
Theorem cells cell : protected_cell cell -> forall bs ns,
 MetaCellFrame.array_ro cell (funcdef_0__schemaInstance bs ns).
Proof.
 intros [Hprotected [H2 [H13 H18]]] bs ns.
 pose proof (mark_cells cell) as Hmark.
 pose proof (SchemaEvaluationPreservation.schemaShift_cells cell Hprotected H2) as Hshift.
 pose proof (SchemaEvaluationPreservation.schemaClass_cells cell (proj1 Hprotected) H2 (proj1 (proj2 (proj2 Hprotected)))) as Hclass.
 pose proof (SchemaEvaluationPreservation.classEqual_cells cell Hprotected) as Hequal.
 pose proof (SchemaEvaluationPreservation.classMember_cells cell Hprotected) as Hmember.
 pose proof (AxiomStorage.cells_ro cell Hprotected H13) as Haxiom.
 pose proof (RenameStorage.Cells.intern_ro cell Hprotected) as Hintern.
 unfold RenameStorage.Cells.protected in Hprotected.
 unfold funcdef_0__schemaInstance. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__schemaInstance_body. MetaCellFrame.ro.
Qed.
Local Transparent funcdef_0__schemaClass funcdef_0__schemaShiftClass funcdef_0__schemaMark.
Lemma class_io bs ns : InternalIO.array_ro (funcdef_0__schemaClass bs ns).
Proof. unfold funcdef_0__schemaClass. apply InternalIO.eliminate_ro. unfold funcdef_0__schemaClass_body. InternalIO.ro. Qed.
Local Opaque funcdef_0__schemaClass.
Lemma shift_io bs ns : InternalIO.array_ro (funcdef_0__schemaShiftClass bs ns).
Proof.
 pose proof class_io as Hclass. pose proof InternalIOProcedures.rename_io as Hrename.
 unfold funcdef_0__schemaShiftClass. apply InternalIO.eliminate_ro. unfold funcdef_0__schemaShiftClass_body. InternalIO.ro.
Qed.
Local Opaque funcdef_0__schemaShiftClass.
Lemma mark_io bs ns : InternalIO.array_ro (funcdef_0__schemaMark bs ns).
Proof. unfold funcdef_0__schemaMark. apply InternalIO.eliminate_ro. unfold funcdef_0__schemaMark_body. InternalIO.ro. Qed.
Local Opaque funcdef_0__schemaMark.
Theorem io bs ns : InternalIO.array_ro (funcdef_0__schemaInstance bs ns).
Proof.
 pose proof class_io as Hclass. pose proof shift_io as Hshift. pose proof mark_io as Hmark.
 pose proof InternalIOProcedures.classEqual_io as Hequal. pose proof InternalIOProcedures.classMember_io as Hmember.
 pose proof InternalIOProcedures.axiom_io as Haxiom. pose proof InternalIOProcedures.intern_io as Hintern.
 unfold funcdef_0__schemaInstance. apply InternalIO.eliminate_ro. unfold funcdef_0__schemaInstance_body. InternalIO.ro.
Qed.
Theorem registries s bs ns final observations after logical :
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,after)) ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 HistoryRefinement.represents final logical /\ NameRepresentation.represents final (Protocol.bindings logical) /\ InternalIO.preserves s final.
Proof.
 intros Hrun Hhistory Hnames.
 assert (Harrays:forall watched,protected_array watched -> memory final watched=memory s watched).
 { intros watched Hprotected. eapply EffectFrame.observed_preserves;[apply arrays;exact Hprotected|exact Hrun]. }
 assert (Hcells:forall slot,protected_cell slot -> meta_value final slot=meta_value s slot).
 { intros slot Hprotected. eapply MetaCellFrame.observed_preserves;[apply cells;exact Hprotected|exact Hrun]. }
 assert (Htheorems:memory final arraydef_0__theorems=memory s arraydef_0__theorems).
 { apply Harrays. unfold protected_array,SchemaEvaluationFrames.persistent,RenameStorage.Arrays.persistent_array. repeat split;discriminate. }
 assert (HnamesArray:memory final arraydef_0__names=memory s arraydef_0__names).
 { apply Harrays. unfold protected_array,SchemaEvaluationFrames.persistent,RenameStorage.Arrays.persistent_array. repeat split;discriminate. }
 assert (Hbindings:memory final arraydef_0__bindings=memory s arraydef_0__bindings).
 { apply Harrays. unfold protected_array,SchemaEvaluationFrames.persistent,RenameStorage.Arrays.persistent_array. repeat split;discriminate. }
 split.
 - unfold HistoryRefinement.represents. rewrite Htheorems,Hcells by (unfold protected_cell,RenameStorage.Cells.protected;repeat split;lia). exact Hhistory.
 - split.
   + unfold NameRepresentation.represents. rewrite HnamesArray,Hbindings,!Hcells by (unfold protected_cell,RenameStorage.Cells.protected;repeat split;lia). exact Hnames.
   + eapply InternalIO.observed_preserves;[apply io|exact Hrun].
Qed.
End SchemaInstanceStorage.
