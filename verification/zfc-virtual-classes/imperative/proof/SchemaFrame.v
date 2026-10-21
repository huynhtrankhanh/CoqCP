From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash MetaCellFrame EffectFrame ImmutableStorage SchemaCountStorage SchemaMetadata.
From stdpp Require Import numbers list.
Module SchemaFrame.
Import IndexExecution SipHashExecution.
Theorem preserves code s observations final after_observations expressions :
  MetaCellFrame.array_ro 16%nat code -> EffectFrame.array_ro arraydef_0__schemaNodes code ->
  execObserved code (s,observations) = Some (tt,(final,after_observations)) ->
  SchemaMetadata.represents s expressions -> SchemaMetadata.represents final expressions.
Proof.
  intros Hcount Hnodes Hrun Hrep. eapply SchemaMetadata.transport; [| |exact Hrep].
  - exact (MetaCellFrame.observed_preserves 16 code s observations tt final after_observations Hcount Hrun).
  - exact (EffectFrame.observed_preserves arraydef_0__schemaNodes code s observations tt final after_observations Hnodes Hrun).
Qed.
Theorem readNat_preserves s bs ns observations final after_observations expressions :
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(final,after_observations)) ->
  SchemaMetadata.represents s expressions -> SchemaMetadata.represents final expressions.
Proof.
  intros Hrun Hrep. exact (preserves _ _ _ _ _ _ (SchemaCountStorage.readNat_ro bs ns)
    (ImmutableStorage.readNat_ro _ ImmutableStorage.schema_array_persistent bs ns) Hrun Hrep).
Qed.
Theorem readToken_preserves s bs ns observations final after_observations expressions :
  execObserved (funcdef_0__readToken bs ns) (s,observations) = Some (tt,(final,after_observations)) ->
  SchemaMetadata.represents s expressions -> SchemaMetadata.represents final expressions.
Proof.
  intros Hrun Hrep. exact (preserves _ _ _ _ _ _ (SchemaCountStorage.readToken_ro bs ns)
    (ImmutableStorage.readToken_ro _ ImmutableStorage.schema_array_persistent bs ns) Hrun Hrep).
Qed.
Local Opaque funcdef_0__lookup funcdef_0__ok funcdef_0__no.
Lemma bindName_nodes bs ns : EffectFrame.array_ro arraydef_0__schemaNodes (funcdef_0__bindName bs ns).
Proof.
  pose proof (ImmutableStorage.lookup_ro _ ImmutableStorage.schema_array_persistent) as Hlookup.
  pose proof (ImmutableStorage.ok_ro _ ImmutableStorage.schema_array_persistent) as Hok.
  pose proof (ImmutableStorage.no_ro _ ImmutableStorage.schema_array_persistent) as Hno.
  unfold funcdef_0__bindName. apply EffectFrame.eliminate_ro. unfold funcdef_0__bindName_body. EffectFrame.ro.
Qed.
Theorem bindName_preserves s bs ns observations final after_observations expressions :
  execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(final,after_observations)) ->
  SchemaMetadata.represents s expressions -> SchemaMetadata.represents final expressions.
Proof.
  intros Hrun Hrep. exact (preserves _ _ _ _ _ _ (SchemaCountStorage.bindName_ro bs ns) (bindName_nodes bs ns) Hrun Hrep).
Qed.
End SchemaFrame.
