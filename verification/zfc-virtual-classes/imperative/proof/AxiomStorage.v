From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameStorage EffectFrame MetaCellFrame InternalIO InternalIOProcedures
  ClassStorage HistoryRefinement NameRepresentation SchemaMetadata SemanticFrames.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Lia.
Module AxiomStorage.
Import IndexExecution SipHashExecution.
Definition logical_frame s t :=
  (forall name, RenameStorage.Arrays.persistent_array name -> memory t name=memory s name) /\
  (forall cell, RenameStorage.Cells.protected cell -> cell<>13%nat -> meta_value t cell=meta_value s cell) /\
  InternalIO.preserves s t.
Local Opaque funcdef_0__intern funcdef_0__rename.
Lemma arrays_ro watched (Hprotected : RenameStorage.Arrays.persistent_array watched) bs ns :
  EffectFrame.array_ro watched (funcdef_0__axiom bs ns).
Proof.
  pose proof (RenameStorage.Arrays.intern_ro watched Hprotected) as Hintern.
  pose proof (RenameStorage.Arrays.rename_ro watched Hprotected) as Hrename.
  unfold RenameStorage.Arrays.persistent_array in Hprotected.
  unfold funcdef_0__axiom. apply EffectFrame.eliminate_ro. unfold funcdef_0__axiom_body. EffectFrame.ro.
Qed.
Lemma cells_ro cell (Hprotected : RenameStorage.Cells.protected cell) (Hflag : cell<>13%nat) bs ns :
  MetaCellFrame.array_ro cell (funcdef_0__axiom bs ns).
Proof.
  pose proof (RenameStorage.Cells.intern_ro cell Hprotected) as Hintern.
  pose proof (RenameStorage.Cells.rename_ro cell Hprotected) as Hrename.
  unfold RenameStorage.Cells.protected in Hprotected.
  unfold funcdef_0__axiom. apply MetaCellFrame.eliminate_ro. unfold funcdef_0__axiom_body. MetaCellFrame.ro.
Qed.
Theorem generated_frame s bs ns final observations after :
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,after)) -> logical_frame s final.
Proof.
  intro Hrun. split.
  - intros name Hprotected. eapply EffectFrame.observed_preserves; [apply arrays_ro;exact Hprotected|exact Hrun].
  - split.
    + intros cell Hprotected Hflag. eapply MetaCellFrame.observed_preserves; [apply cells_ro;assumption|exact Hrun].
    + eapply InternalIO.observed_preserves; [apply InternalIOProcedures.axiom_io|exact Hrun].
Qed.
Lemma classes_transport s t fs extra classes : logical_frame s t -> ClassStorage.represents s fs classes ->
  ClassStorage.represents t (fs++extra) classes.
Proof.
  intros [Ha [Hc Hio]] Hclasses. eapply SemanticFrames.classes_extend;
    [apply Hc;[unfold RenameStorage.Cells.protected;lia|lia]|apply Ha;repeat split;discriminate|exact Hclasses].
Qed.
Lemma history_transport s t logical : logical_frame s t -> HistoryRefinement.represents s logical ->
  HistoryRefinement.represents t logical.
Proof.
  intros [Ha [Hc Hio]] Hhistory. eapply SemanticFrames.history_transport;
    [apply Hc;[unfold RenameStorage.Cells.protected;lia|lia]|apply Ha;repeat split;discriminate|exact Hhistory].
Qed.
Lemma names_transport s t bindings : logical_frame s t -> NameRepresentation.represents s bindings ->
  NameRepresentation.represents t bindings.
Proof.
  intros [Ha [Hc Hio]] [Hcount [Hbytes [Hbindinglimit [Hlimit Hrep]]]].
  assert (Hnames : memory t arraydef_0__names=memory s arraydef_0__names) by (apply Ha;repeat split;discriminate).
  assert (Hbindings : memory t arraydef_0__bindings=memory s arraydef_0__bindings) by (apply Ha;repeat split;discriminate).
  unfold NameRepresentation.represents. rewrite Hnames,Hbindings.
  rewrite Hc by (try (unfold RenameStorage.Cells.protected);lia). split;[exact Hcount|].
  rewrite Hc by (try (unfold RenameStorage.Cells.protected);lia). auto.
Qed.
Lemma schemas_transport s t expressions : logical_frame s t -> SchemaMetadata.represents s expressions ->
  SchemaMetadata.represents t expressions.
Proof.
  intros [Ha [Hc Hio]] Hschemas. eapply SchemaMetadata.transport;
    [apply Hc;[unfold RenameStorage.Cells.protected;lia|lia]|apply Ha;repeat split;discriminate|exact Hschemas].
Qed.
End AxiomStorage.
