From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import EffectFrame MetaCellFrame Index SipHash InternalIO InternalIOProcedures ClassStorage HistoryRefinement NameRepresentation SchemaMetadata SemanticFrames.
From Stdlib Require Import Lia.
From stdpp Require Import numbers list.
Module RenameStorage.
Module Arrays.
Import EffectFrame.
Definition persistent_array watched :=
  arraydef_0__meta <> watched /\ arraydef_0__sipState <> watched /\
  arraydef_0__formulaBuckets <> watched /\ arraydef_0__formulaLinks <> watched /\
  arraydef_0__renameMemo <> watched /\ arraydef_0__renameMemoScratch <> watched /\
  arraydef_0__formulas <> watched /\ arraydef_0__frames <> watched.
Theorem sipRound_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__sipRound bs ns).
Proof. unfold persistent_array in Hprotected. unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__sipWord bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (sipRound_ro watched Hprotected) as Hround. unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__formulaHash bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (sipRound_ro watched Hprotected) as Hround. pose proof (sipWord_ro watched Hprotected) as Hword.
  unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehash_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__rehashFormulas bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (formulaHash_ro watched Hprotected) as Hhash. unfold funcdef_0__rehashFormulas.
  apply eliminate_ro. unfold funcdef_0__rehashFormulas_body. ro.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__intern bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (formulaHash_ro watched Hprotected) as Hhash. pose proof (rehash_ro watched Hprotected) as Hresize.
  unfold funcdef_0__intern. apply eliminate_ro. unfold funcdef_0__intern_body. ro.
Qed.

Local Opaque funcdef_0__intern.
Theorem push_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__push bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__push. apply eliminate_ro. unfold funcdef_0__push_body. ro.
Qed.
Local Opaque funcdef_0__push.
Theorem renameIndex_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameIndex bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__renameIndex. apply eliminate_ro. unfold funcdef_0__renameIndex_body. ro.
Qed.
Local Opaque funcdef_0__renameIndex.
Theorem renameCacheGet_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameCacheGet bs ns).
Proof. unfold persistent_array in Hprotected. pose proof (formulaHash_ro watched Hprotected) as Hhash. unfold funcdef_0__renameCacheGet. apply eliminate_ro. unfold funcdef_0__renameCacheGet_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem renameCacheGrow_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameCacheGrow bs ns).
Proof. unfold persistent_array in Hprotected. pose proof (formulaHash_ro watched Hprotected) as Hhash. unfold funcdef_0__renameCacheGrow. apply eliminate_ro. unfold funcdef_0__renameCacheGrow_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem renameCachePut_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameCachePut bs ns).
Proof. unfold persistent_array in Hprotected. pose proof (formulaHash_ro watched Hprotected) as Hhash. pose proof (renameCacheGrow_ro watched Hprotected) as Hgrow. unfold funcdef_0__renameCachePut. apply eliminate_ro. unfold funcdef_0__renameCachePut_body. ro. Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem rename_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__rename bs ns).
Proof. pose proof (renameCacheGet_ro watched Hprotected) as HrenameCacheGet.  pose proof (renameCachePut_ro watched Hprotected) as HrenameCachePut.  unfold persistent_array in Hprotected.
  pose proof (push_ro watched Hprotected) as Hdep0.
  pose proof (renameIndex_ro watched Hprotected) as Hdep1.
  pose proof (intern_ro watched Hprotected) as Hdep2.
  unfold funcdef_0__rename. apply eliminate_ro. unfold funcdef_0__rename_body. ro.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__predicate bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (rename_ro watched Hprotected) as Hdep0.
  pose proof (intern_ro watched Hprotected) as Hdep1.
  unfold funcdef_0__predicate. apply eliminate_ro. unfold funcdef_0__predicate_body. ro.
Qed.
Local Opaque funcdef_0__predicate.
End Arrays.
Module Cells.
Import MetaCellFrame.
Definition protected cell := cell <> 0%nat /\ cell <> 1%nat /\ cell <> 8%nat /\ cell <> 10%nat /\
  cell <> 20%nat /\ cell <> 21%nat /\ cell <> 28%nat /\
  cell <> 29%nat /\ cell <> 30%nat /\ cell <> 31%nat.
Theorem sipRound_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__sipRound bs ns).
Proof. unfold protected in Hprotected. unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__sipWord bs ns).
Proof. unfold protected in Hprotected.
  pose proof (sipRound_ro cell Hprotected) as Hround. unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__formulaHash bs ns).
Proof. unfold protected in Hprotected.
  pose proof (sipRound_ro cell Hprotected) as Hround. pose proof (sipWord_ro cell Hprotected) as Hword.
  unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehash_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__rehashFormulas bs ns).
Proof. unfold protected in Hprotected.
  pose proof (formulaHash_ro cell Hprotected) as Hhash. unfold funcdef_0__rehashFormulas.
  apply eliminate_ro. unfold funcdef_0__rehashFormulas_body. ro.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__intern bs ns).
Proof. unfold protected in Hprotected.
  pose proof (formulaHash_ro cell Hprotected) as Hhash. pose proof (rehash_ro cell Hprotected) as Hresize.
  unfold funcdef_0__intern. apply eliminate_ro. unfold funcdef_0__intern_body. ro.
Qed.

Local Opaque funcdef_0__intern.
Theorem push_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__push bs ns).
Proof. unfold protected in Hprotected.
  unfold funcdef_0__push. apply eliminate_ro. unfold funcdef_0__push_body. ro.
Qed.
Local Opaque funcdef_0__push.
Theorem renameIndex_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__renameIndex bs ns).
Proof. unfold protected in Hprotected.
  unfold funcdef_0__renameIndex. apply eliminate_ro. unfold funcdef_0__renameIndex_body. ro.
Qed.
Local Opaque funcdef_0__renameIndex.
Theorem renameCacheGet_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__renameCacheGet bs ns).
Proof. unfold protected in Hprotected. pose proof (formulaHash_ro cell Hprotected) as Hhash. unfold funcdef_0__renameCacheGet. apply eliminate_ro. unfold funcdef_0__renameCacheGet_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem renameCacheGrow_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__renameCacheGrow bs ns).
Proof. unfold protected in Hprotected. pose proof (formulaHash_ro cell Hprotected) as Hhash. unfold funcdef_0__renameCacheGrow. apply eliminate_ro. unfold funcdef_0__renameCacheGrow_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem renameCachePut_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__renameCachePut bs ns).
Proof. unfold protected in Hprotected. pose proof (formulaHash_ro cell Hprotected) as Hhash. pose proof (renameCacheGrow_ro cell Hprotected) as Hgrow. unfold funcdef_0__renameCachePut. apply eliminate_ro. unfold funcdef_0__renameCachePut_body. ro. Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem rename_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__rename bs ns).
Proof. pose proof (renameCacheGet_ro cell Hprotected) as HrenameCacheGet.  pose proof (renameCachePut_ro cell Hprotected) as HrenameCachePut.  unfold protected in Hprotected.
  pose proof (push_ro cell Hprotected) as Hdep0.
  pose proof (renameIndex_ro cell Hprotected) as Hdep1.
  pose proof (intern_ro cell Hprotected) as Hdep2.
  unfold funcdef_0__rename. apply eliminate_ro. unfold funcdef_0__rename_body. ro.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_ro cell (Hprotected : protected cell) bs ns : array_ro cell (funcdef_0__predicate bs ns).
Proof. unfold protected in Hprotected.
  pose proof (rename_ro cell Hprotected) as Hdep0.
  pose proof (intern_ro cell Hprotected) as Hdep1.
  unfold funcdef_0__predicate. apply eliminate_ro. unfold funcdef_0__predicate_body. ro.
Qed.
Local Opaque funcdef_0__predicate.
End Cells.
Import IndexExecution SipHashExecution.
Theorem rename_arrays s bs ns final observations after watched : Arrays.persistent_array watched ->
  execObserved (funcdef_0__rename bs ns) (s,observations) = Some (tt,(final,after)) -> memory final watched = memory s watched.
Proof. intros Hprotected. apply EffectFrame.observed_preserves. now apply Arrays.rename_ro. Qed.
Theorem predicate_arrays s bs ns final observations after watched : Arrays.persistent_array watched ->
  execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,after)) -> memory final watched = memory s watched.
Proof. intros Hprotected. apply EffectFrame.observed_preserves. now apply Arrays.predicate_ro. Qed.
Theorem rename_cells s bs ns final observations after cell : Cells.protected cell ->
  execObserved (funcdef_0__rename bs ns) (s,observations) = Some (tt,(final,after)) -> meta_value final cell = meta_value s cell.
Proof. intros Hprotected. apply MetaCellFrame.observed_preserves. now apply Cells.rename_ro. Qed.
Theorem predicate_cells s bs ns final observations after cell : Cells.protected cell ->
  execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,after)) -> meta_value final cell = meta_value s cell.
Proof. intros Hprotected. apply MetaCellFrame.observed_preserves. now apply Cells.predicate_ro. Qed.
Definition logical_frame s t :=
  (forall name, Arrays.persistent_array name -> memory t name = memory s name) /\
  (forall cell, Cells.protected cell -> meta_value t cell = meta_value s cell) /\
  InternalIO.preserves s t.
Theorem rename_frame s bs ns final observations after :
  execObserved (funcdef_0__rename bs ns) (s,observations) = Some (tt,(final,after)) -> logical_frame s final.
Proof.
  intros Hrun. split; [intros name Hname; eapply rename_arrays; eassumption|]. split.
  - intros cell Hcell. eapply rename_cells; eassumption.
  - eapply InternalIOProcedures.rename_preserves; exact Hrun.
Qed.
Theorem predicate_frame s bs ns final observations after :
  execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,after)) -> logical_frame s final.
Proof.
  intros Hrun. split; [intros name Hname; eapply predicate_arrays; eassumption|]. split.
  - intros cell Hcell. eapply predicate_cells; eassumption.
  - eapply InternalIOProcedures.predicate_preserves; exact Hrun.
Qed.
Lemma classes_transport s t fs extra classes : logical_frame s t -> ClassStorage.represents s fs classes ->
  ClassStorage.represents t (fs ++ extra) classes.
Proof.
  intros [Ha [Hc Hio]] Hclasses. eapply SemanticFrames.classes_extend; [apply Hc; unfold Cells.protected; lia|apply Ha; repeat split; discriminate|exact Hclasses].
Qed.
Lemma history_transport s t logical : logical_frame s t -> HistoryRefinement.represents s logical -> HistoryRefinement.represents t logical.
Proof.
  intros [Ha [Hc Hio]] Hhistory. eapply SemanticFrames.history_transport; [apply Hc; unfold Cells.protected; lia|apply Ha; repeat split; discriminate|exact Hhistory].
Qed.
Lemma names_transport s t bindings : logical_frame s t -> NameRepresentation.represents s bindings -> NameRepresentation.represents t bindings.
Proof.
  intros [Ha [Hc Hio]] [Hcount [Hbytes [Hbindinglimit [Hlimit Hrep]]]].
  assert (Hnames : memory t arraydef_0__names = memory s arraydef_0__names) by (apply Ha; repeat split; discriminate).
  assert (Hbindings : memory t arraydef_0__bindings = memory s arraydef_0__bindings) by (apply Ha; repeat split; discriminate).
  unfold NameRepresentation.represents. rewrite Hnames,Hbindings.
  rewrite Hc by (unfold Cells.protected; lia). split; [exact Hcount|].
  rewrite Hc by (unfold Cells.protected; lia). auto.
Qed.
Lemma schemas_transport s t expressions : logical_frame s t -> SchemaMetadata.represents s expressions -> SchemaMetadata.represents t expressions.
Proof.
  intros [Ha [Hc Hio]] Hschemas. eapply SchemaMetadata.transport; [apply Hc; unfold Cells.protected; lia|apply Ha; repeat split; discriminate|exact Hschemas].
Qed.
End RenameStorage.
