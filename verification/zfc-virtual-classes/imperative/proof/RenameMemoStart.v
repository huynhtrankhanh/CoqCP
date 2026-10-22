From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Stack FormulaTopology Representation RenameStack RenameMemoBounds
  RenameMemoInit RenameMemoControl RenameMemoInitial RenameMemoStack RenameMemoState RenameMemoMeaning
  RenameMemoSchedule RenameMemoArenaWork RenameMemoWork RenameMemoScheduleRelation RenameMemoEventSchedule
  RenameMemoDomain RenameMemoIndexBounds RenameMemoTransition ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoStart.
Import IndexExecution SipHashExecution ObservedLocal.
Definition frame (f : RenameMemoInit.Frame) root :=
  RenameMemoControl.prepared (setMachine f (RenameMemoInit.initialized (machine f))) root.
Definition model root base := RenameMemoSchedule.config [] [] [RenameMemoSchedule.visit root base] 0 0.
Lemma prepared_live (f : RenameMemoInit.Frame) root :
  (31<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine (frame f root)) 30=0.
Proof.
  intro Hmeta. change (meta_value (StackExecution.push_state (RenameMemoInit.initialized (machine f)) 0
    (Z.of_nat root) (nums f vardef_0__rename_initialDepth)) 30=0).
  pose proof (RenameMemoStack.push_frame (RenameMemoInit.initialized (machine f)) 0
    (Z.of_nat root) (nums f vardef_0__rename_initialDepth)) as [_ [Hmetadata _]].
  rewrite Hmetadata by lia. now apply RenameMemoInit.initialized_count.
Qed.
Theorem prepared_coupled (f : RenameMemoInit.Frame) fs source root base :
  (31<length (memory (machine f) arraydef_0__meta))%nat -> nth_error fs root=Some source ->
  RenameMemoEventSchedule.coupled fs root (machine (frame f root)) fs 16
    [RenameStack.visit source base] (model root base) (length fs).
Proof.
  intros Hmeta Hlookup. constructor.
  - constructor; [constructor; [lia|exact Hlookup]|constructor].
  - intros query Hin. contradiction.
  - rewrite prepared_live by exact Hmeta. cbn [model RenameMemoSchedule.completed length]. lia.
  - cbn [model RenameMemoSchedule.stack RenameMemoSchedule.active RenameMemoSchedule.visited length]. lia.
Qed.
Theorem source_identity fs : RenameMemoEventSchedule.source_prefix fs fs.
Proof. intros node p Hlookup. exact Hlookup. Qed.
Theorem source_graph (f : RenameMemoInit.Frame) fs source root :
  NativeRepresentation.canonical_arena (machine f) fs -> nth_error fs root=Some source ->
  FormulaTopology.ordered (machine f) (length fs) ->
  RenameMemoScheduleRelation.coherent fs root (RenameMemoArenaWork.graph (machine f) (S root)) /\
  RenameMemoWork.older (RenameMemoArenaWork.graph (machine f) (S root)).
Proof.
  intros Harena Hlookup Hordered.
  assert (Hroot : (root<length fs)%nat) by (apply nth_error_Some; congruence).
  split; [now apply RenameMemoScheduleRelation.canonical_coherent|].
  apply RenameMemoArenaWork.graph_older. intros parent child Hparent Hchild.
  apply Hordered; [lia|exact Hchild].
Qed.
Theorem source_domain source root base bound : RenameMemoIndexBounds.formula_bound bound source ->
  RenameMemoDomain.source_domain bound (base+RenameMemoTransition.height source) [RenameStack.visit source base] /\
  RenameMemoSchedule.invariant root base (model root base).
Proof. intro Hbound. split; [now apply RenameMemoDomain.initial|apply RenameMemoSchedule.initial]. Qed.
Theorem prepared_parameters (f : RenameMemoInit.Frame) root :
  nums (frame f root) vardef_0__rename_mode=nums f vardef_0__rename_mode /\
  nums (frame f root) vardef_0__rename_shift=nums f vardef_0__rename_shift /\
  nums (frame f root) vardef_0__rename_arg=nums f vardef_0__rename_arg /\
  nums (frame f root) vardef_0__rename_initialDepth=nums f vardef_0__rename_initialDepth.
Proof. unfold frame. repeat split; apply RenameMemoInitial.prepared_arguments; discriminate. Qed.
Theorem prepared_state (f : RenameMemoInit.Frame) fs rho root base source value :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  (0<length (memory (machine f) arraydef_0__sipState))%nat -> 0<meta_value (machine f) 20 ->
  meta_value (machine f) 8=0 -> NativeRepresentation.canonical_arena (machine f) fs ->
  nth_error fs root=Some source -> nth_error fs 0=Some SetTheory.falsity ->
  nums f vardef_0__rename_initialDepth=Z.of_nat base -> word (Z.of_nat base) ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  RenameMemoState.represents (machine (frame f root)) fs rho 16
    [RenameStack.visit source base] value (RenameStack.renamed rho base source) /\
  RenameMemoEventSchedule.coupled fs root (machine (frame f root)) fs 16
    [RenameStack.visit source base] (model root base) (length fs).
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Hsource Hzero Hbase Hbaseword Hfuel. split.
  - now apply RenameMemoInitial.prepared_state.
  - now apply prepared_coupled.
Qed.
Theorem reached_initial graph root base : RenameMemoSchedule.reached graph root base 0 (model root base).
Proof. apply RenameMemoSchedule.reached_initial. Qed.
End RenameMemoStart.
