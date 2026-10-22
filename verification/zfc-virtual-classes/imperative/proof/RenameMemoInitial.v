From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Stack FrameReplace Representation RenameStack RenameFrames RenameMemoBounds
  RenameMemoInit RenameMemoControl RenameMemoInvariant RenameMemoMeaning RenameMemoStorage RenameMemoStack
  RenameMemoContinuation RenameMemoState ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoInitial.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Lemma initialized_storage s : RenameMemoInvariant.storage_frame s (initialized s).
Proof.
  split; [intros; now apply initialized_other|]. split; [intros; now apply initialized_meta_other|].
  split; [apply initialized_meta_length|]. split; [now rewrite initialized_other by discriminate|]. apply initialized_io.
Qed.
Theorem prepared_state (f : Frame) fs rho root base source value :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  (0<length (memory (machine f) arraydef_0__sipState))%nat -> 0<meta_value (machine f) 20 ->
  meta_value (machine f) 8=0 -> NativeRepresentation.canonical_arena (machine f) fs ->
  nth_error fs root=Some source -> nth_error fs 0=Some SetTheory.falsity ->
  nums f vardef_0__rename_initialDepth=Z.of_nat base -> word (Z.of_nat base) ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoState.represents (machine (prepared (setMachine f (initialized (machine f))) root)) fs rho 16
    [RenameStack.visit source base] value (RenameStack.renamed rho base source).
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Hsource Hzero Hbase Hbaseword Hfuel.
  assert (Hrootword : word (Z.of_nat root)).
  { unfold RenameMemoBounds.fuel in Hfuel. rewrite Nat2Z.inj_add,!Nat2Z.inj_mul in Hfuel.
    unfold word,maximum in *. cbn in Hfuel. nia. }
  assert (Hcache : RenameMemoInvariant.valid (initialized (machine f)) 16 (RenameMemoMeaning.entry_meaning fs rho))
    by now apply RenameMemoInvariant.initialized.
  assert (Hinitarena : NativeRepresentation.canonical_arena (initialized (machine f)) fs).
  { apply RenameMemoStorage.canonical_arena with (s:=machine f); [apply initialized_storage|exact Harena]. }
  assert (Hinitmeta : (10<length (memory (initialized (machine f)) arraydef_0__meta))%nat)
    by (rewrite initialized_meta_length; lia).
  assert (Hempty : RenameFrames.represents (initialized (machine f)) fs [])
    by (apply RenameFrames.empty; now apply initialized_stack).
  change (RenameMemoState.represents
    (StackExecution.push_state (initialized (machine f)) 0 (Z.of_nat root) (nums f vardef_0__rename_initialDepth))
    fs rho 16 [RenameStack.visit source base] value (RenameStack.renamed rho base source)).
  rewrite Hbase. apply RenameMemoState.scheduled.
  - now apply RenameMemoStack.push_valid.
  - now apply FrameReplace.push_arena.
  - apply RenameFrames.push_visit with (stack:=[]); try assumption.
    + unfold maximum; cbn; lia.
    + now rewrite Nat2Z.id.
  - apply RenameMemoContinuation.initial.
  - exact Hzero.
Qed.
Theorem prepared_arguments (f : Frame) root variable :
  variable<>vardef_0__rename_width -> variable<>vardef_0__rename_pairs -> variable<>vardef_0__rename_budget ->
  nums (prepared (setMachine f (initialized (machine f))) root) variable=nums f variable.
Proof.
  intros Hwidth Hpairs Hbudget. unfold prepared. destruct f.
  cbv beta iota zeta delta [machine nums bools setMachine setNum]. now repeat rewrite updated_other by assumption.
Qed.
End RenameMemoInitial.
