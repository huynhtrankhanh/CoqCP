From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift Stack HashTable FrameReplace FormulaEncoding FormulaTopology Representation RenameStack RenameFrames
  RenameMemoBounds RenameMemoWork RenameMemoSchedule RenameMemoScheduleRelation RenameMemoEventSchedule
  RenameMemoScheduleResources RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoDomain
  RenameMemoState RenameMemoStep RenameMemoInvariant RenameMemoMeaning RenameMemoHit RenameMemoLoop
  RenameMemoInit RenameMemoControl RenameMemoStart RenameMemoArenaWork RenameMemoTopology ObservedLocal RenameMemoIndexStep SchemaEvaluationIndexBounds.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoIndexRun.
Import IndexExecution SipHashExecution IndexSemantics RenameMemoInit ObservedLocal.
Section ArenaBound.
Variable arena_bound:nat.
Definition arguments (f : Frame) m shift arg :=
  nums f vardef_0__rename_mode=mode_number m /\ nums f vardef_0__rename_shift=Z.of_nat shift /\
  nums f vardef_0__rename_arg=Z.of_nat arg.
Definition related source_fs root m shift arg bound ceiling target (f : Frame) model :=
  exists fs count tasks value,
    RenameMemoState.represents (machine f) fs (renaming m shift arg) count tasks value target /\
    RenameMemoEventSchedule.coupled source_fs root (machine f) fs count tasks model (length source_fs) /\
    RenameMemoEventSchedule.source_prefix source_fs fs /\ RenameMemoDomain.source_domain bound ceiling tasks /\
    arguments f m shift arg /\ FormulaTopology.ordered (machine f) (length fs) /\
    SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) arena_bound.
Lemma parameters f after m shift arg : RenameMemoHit.parameters f after -> arguments f m shift arg -> arguments after m shift arg.
Proof.
  intros Hparameters [Hmode [Hshift Harg]]. unfold arguments.
  rewrite (Hparameters vardef_0__rename_mode), (Hparameters vardef_0__rename_shift), (Hparameters vardef_0__rename_arg)
    by (cbn; tauto). auto.
Qed.
Theorem ready source_fs root m shift arg bound ceiling target f model :
  related source_fs root m shift arg bound ceiling target f model ->
  (10<length (memory (machine f) arraydef_0__meta))%nat /\
  (RenameMemoSchedule.stack model=[] -> meta_value (machine f) 10=0).
Proof.
  intros (fs & count & tasks & value & Hstate & Hcoupled & Hprefix & Hdomain & Harguments & Htopology & HrawArena).
  exact (RenameMemoScheduleResources.ready (machine f) fs (renaming m shift arg) count tasks value target model (length source_fs)
    Hstate (RenameMemoEventSchedule.accounting _ _ _ _ _ _ _ _ Hcoupled)).
Qed.
Theorem advance source_fs root base graph m shift arg bound ceiling target :
  RenameMemoScheduleRelation.coherent source_fs root graph -> RenameMemoWork.older graph ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length source_fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum -> Z.of_nat ceiling<=maximum ->
  (bound+RenameMemoIndexBounds.increment m shift arg<=arena_bound)%nat ->
  forall steps f model, RenameMemoSchedule.reached graph root base steps model ->
    related source_fs root m shift arg bound ceiling target f model -> RenameMemoSchedule.stack model<>[] ->
    forall observations, exists after next,
      execLocalObserved RenameMemoControl.iteration (f,observations)=Some (KeepGoing,(after,observations)) /\
      RenameMemoSchedule.move graph model next /\ related source_fs root m shift arg bound ceiling target after next.
Proof.
  intros Hcoherent Hgraph Hfuel Hroom Hshiftword Hargword Hindices Hceiling HtargetBound steps f model Hreach
    (fs & count & tasks & value & Hstate & Hcoupled & Hprefix & Hdomain & Harguments & Htopology & HrawArena) Hnonempty observations.
  pose proof (RenameMemoEventSchedule.accounting _ _ _ _ _ _ _ _ Hcoupled) as Haccount.
  assert (Htasks : tasks<>[]).
  { intro Hempty. pose proof (RenameMemoScheduleResources.stack_account _ _ _ _ _ Haccount) as Hlength.
    rewrite Hempty in Hlength. destruct (RenameMemoSchedule.stack model); [contradiction|discriminate]. }
  destruct tasks as [|task tasks]; [contradiction|].
  pose proof (RenameMemoScheduleResources.resources (machine f) fs (task::tasks) model (length source_fs) graph root base steps m shift arg count bound ceiling
    Haccount Hgraph Hreach Hfuel Hroom Hshiftword Hargword Hdomain Hindices Hceiling) as Hresources.
  destruct Harguments as [Hmode [Hshift Harg]].
  destruct (RenameMemoIndexStep.Step.generated f fs m shift arg count task tasks value target bound arena_bound Hmode Hshift Harg Hstate Hresources HrawArena (proj1 Hdomain) HtargetBound observations)
    as (after & next_fs & next_tasks & next_value & size & Hrun & HnextIndices & Hpost).
  destruct Hpost as (Hstate' & Hextends & Hgrowth & Hparameters & Hdecrease & Htransition & Hevent).
  assert (Hrootword : word (Z.of_nat root)).
  { destruct (RenameMemoResourceBounds.grid_word root Hfuel) as [Hwidth [Hword _]].
    change (Z.of_nat (S root)<maximum) in Hword. unfold word. lia. }
  destruct (RenameMemoEventSchedule.event_preserves source_fs root graph (machine f) fs count
    (machine after) next_fs size (task::tasks) next_tasks model (length source_fs) Hcoherent Hgraph Hprefix Hrootword
    (RenameMemoInvariant.entries_indexed _ _ _ (RenameMemoState.cache _ _ _ _ _ _ _ Hstate)) Hcoupled Hevent)
    as [next_model [Hmove Hcoupled']].
  exists after,next_model. split; [exact Hrun|]. split; [exact Hmove|].
  exists next_fs,size,next_tasks,next_value. split; [exact Hstate'|]. split; [exact Hcoupled'|]. split.
  - destruct Hextends as [extra ->]. now apply RenameMemoEventSchedule.source_prefix_extend.
  - split.
    + now apply RenameMemoDomain.preserved with (rho:=renaming m shift arg) (stack:=task::tasks) (value:=value) (result:=next_value).
    + split; [apply parameters with (f:=f); [exact Hparameters|now repeat split]|].
      split;[|exact HnextIndices]. apply RenameMemoTopology.preserves with (s:=machine f) (fs:=fs); try assumption.
      * exact (RenameMemoState.arena _ _ _ _ _ _ _ Hstate).
      * exact (RenameMemoState.arena _ _ _ _ _ _ _ Hstate').
Qed.
Theorem complete source_fs root base graph m shift arg bound ceiling target s bs ns :
  RenameMemoScheduleRelation.coherent source_fs root graph -> RenameMemoWork.older graph ->
  (31<length (memory s arraydef_0__meta))%nat -> ns vardef_0__rename_node=Z.of_nat root ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length source_fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum -> Z.of_nat ceiling<=maximum ->
  (bound+RenameMemoIndexBounds.increment m shift arg<=arena_bound)%nat ->
  related source_fs root m shift arg bound ceiling target
    (RenameMemoStart.frame {|machine:=s;bools:=bs;nums:=ns|} root) (RenameMemoStart.model root base) ->
  forall observations, exists (final : Frame) next count,
    execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(machine final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next /\
    RenameMemoInvariant.valid (machine final) count (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) /\
    word (meta_value (machine final) 0) /\ nth_error next (Z.to_nat (meta_value (machine final) 0))=Some target /\
    RenameMemoEventSchedule.source_prefix source_fs next /\ meta_value (machine final) 8=0 /\ meta_value (machine final) 10=0 /\
    (length next<=length source_fs+S root*S root)%nat /\ FormulaTopology.ordered (machine final) (length next) /\
    SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) arena_bound.
Proof.
  intros Hcoherent Hgraph Hmeta Hnode Hfuel Hroom Hshift Harg Hindices Hceiling HtargetBound Hinitial observations.
  destruct (RenameMemoLoop.generated graph root base (related source_fs root m shift arg bound ceiling target)
    Hgraph (ready source_fs root m shift arg bound ceiling target)
    (advance source_fs root base graph m shift arg bound ceiling target Hcoherent Hgraph Hfuel Hroom Hshift Harg Hindices Hceiling HtargetBound)
    s bs ns Hmeta Hnode Hfuel Hinitial observations)
    as (final & finished & steps & Hrun & Hrelated & Hempty & Hreach).
  destruct Hrelated as (next & count & tasks & value & Hstate & Hcoupled & Hprefix & Hdomain & Harguments & Htopology & HrawArena).
  pose proof (RenameMemoEventSchedule.accounting _ _ _ _ _ _ _ _ Hcoupled) as Haccount.
  assert (Htasks : tasks=[]).
  {
    pose proof (RenameMemoScheduleResources.stack_account _ _ _ _ _ Haccount) as Hlength.
    rewrite Hempty in Hlength. destruct tasks; [reflexivity|discriminate]. }
  subst tasks. destruct (RenameMemoState.finished _ _ _ _ _ _ Hstate) as [Hword Hvalue].
  exists final,next,count. split; [exact Hrun|]. split; [exact (RenameMemoState.arena _ _ _ _ _ _ _ Hstate)|].
  split; [exact (RenameMemoState.cache _ _ _ _ _ _ _ Hstate)|]. split; [exact Hword|]. split; [exact Hvalue|].
  split; [exact Hprefix|]. split; [exact (RenameMemoInvariant.error_clear _ _ _ (RenameMemoState.cache _ _ _ _ _ _ _ Hstate))|].
  split.
  - exact (proj1 (RenameMemoState.frames _ _ _ _ _ _ _ Hstate)).
  - split; [|split;[exact Htopology|exact HrawArena]]. pose proof (RenameMemoScheduleResources.arena_account _ _ _ _ _ Haccount) as Hmass.
    pose proof (RenameMemoSchedule.fresh_bound _ _ _ (RenameMemoSchedule.reached_invariant _ _ _ _ _ Hgraph Hreach)). lia.
Qed.
(* Complete execution of the actual generated native procedure, from its
   concrete initialization. All premises concern the input and finite machine
   resource bounds; no execution, invariant-preservation or consistency premise
   is assumed. *)
Theorem generated s bs ns fs source root base m shift arg bound :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs root=Some source -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__rename_node=Z.of_nat root -> ns vardef_0__rename_initialDepth=Z.of_nat base ->
  ns vardef_0__rename_mode=mode_number m -> ns vardef_0__rename_shift=Z.of_nat shift -> ns vardef_0__rename_arg=Z.of_nat arg ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) -> RenameMemoIndexBounds.formula_bound bound source ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum ->
  Z.of_nat (base+RenameMemoTransition.height source)<=maximum ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) arena_bound ->
  (bound+RenameMemoIndexBounds.increment m shift arg<=arena_bound)%nat ->
  forall observations, exists (final : Frame) next count,
    execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(machine final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next /\
    RenameMemoInvariant.valid (machine final) count (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) /\
    word (meta_value (machine final) 0) /\
    nth_error next (Z.to_nat (meta_value (machine final) 0))=Some (RenameStack.renamed (renaming m shift arg) base source) /\
    RenameMemoEventSchedule.source_prefix fs next /\ meta_value (machine final) 8=0 /\ meta_value (machine final) 10=0 /\
    (length next<=length fs+S root*S root)%nat /\ FormulaTopology.ordered (machine final) (length next) /\
    SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) arena_bound.
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Htopology Hlookup Hfalse Hnode Hbase Hmode Hshift Harg Hfuel Hroom
    Hshiftword Hargword Hbound Hindices Hceiling HrawInitial HtargetBound observations.
  set (f := ({|machine:=s;bools:=bs;nums:=ns|} : Frame)).
  destruct (RenameMemoStart.source_graph f fs source root Harena Hlookup Htopology) as [Hcoherent Hgraph].
  assert (Hbaseword : word (Z.of_nat base)) by (unfold word; lia).
  destruct (RenameMemoStart.prepared_state f fs (renaming m shift arg) root base source SetTheory.falsity
    Hmeta Hsip Hpositive Herror Harena Hlookup Hfalse Hbase Hbaseword Hfuel) as [Hstate Hcoupled].
  destruct (RenameMemoStart.source_domain source root base bound Hbound) as [Hdomain Hmodel].
  assert (Hinitial : related fs root m shift arg bound (base+RenameMemoTransition.height source)
    (RenameStack.renamed (renaming m shift arg) base source) (RenameMemoStart.frame f root) (RenameMemoStart.model root base)).
  { exists fs,16%nat,[RenameStack.visit source base],SetTheory.falsity. split; [exact Hstate|]. split; [exact Hcoupled|].
    split; [apply RenameMemoStart.source_identity|]. split; [exact Hdomain|].
    destruct (RenameMemoStart.prepared_parameters f root) as [Hmode' [Hshift' [Harg' Hbase']]].
    split.
    - unfold arguments. rewrite Hmode',Hshift',Harg'. exact (conj Hmode (conj Hshift Harg)).
    - split.
      + change (FormulaTopology.ordered
          (StackExecution.push_state (RenameMemoInit.initialized s) 0 (Z.of_nat root) (ns vardef_0__rename_initialDepth)) (length fs)).
        intros parent child Hparent Hchild. apply Htopology; [exact Hparent|].
        unfold HashTableInvariant.tuple_at in Hchild. rewrite FrameReplace.push_other in Hchild by discriminate.
        rewrite RenameMemoInit.initialized_other in Hchild by discriminate. exact Hchild.
      + change (SchemaEvaluationIndexBounds.raw_arena
          (StackExecution.push_state (RenameMemoInit.initialized s) 0 (Z.of_nat root) (ns vardef_0__rename_initialDepth)) (length fs) arena_bound).
        eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
        rewrite FrameReplace.push_other by discriminate. apply RenameMemoInit.initialized_other;discriminate. }
  exact (complete fs root base (RenameMemoArenaWork.graph s (S root)) m shift arg bound (base+RenameMemoTransition.height source)
    (RenameStack.renamed (renaming m shift arg) base source) s bs ns Hcoherent Hgraph Hmeta Hnode Hfuel Hroom
    Hshiftword Hargword Hindices Hceiling HtargetBound Hinitial observations).
Qed.
End ArenaBound.
Theorem generated_bounded s bs ns fs source root base m shift arg bound :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs root=Some source -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__rename_node=Z.of_nat root -> ns vardef_0__rename_initialDepth=Z.of_nat base ->
  ns vardef_0__rename_mode=mode_number m -> ns vardef_0__rename_shift=Z.of_nat shift -> ns vardef_0__rename_arg=Z.of_nat arg ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) -> SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum ->
  Z.of_nat (base+RenameMemoTransition.height source)<=maximum ->
  forall observations, exists (final : Frame) next count,
    execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(machine final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next /\
    RenameMemoInvariant.valid (machine final) count (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) /\
    word (meta_value (machine final) 0) /\
    nth_error next (Z.to_nat (meta_value (machine final) 0))=Some (RenameStack.renamed (renaming m shift arg) base source) /\
    RenameMemoEventSchedule.source_prefix fs next /\ meta_value (machine final) 8=0 /\ meta_value (machine final) 10=0 /\
    (length next<=length fs+S root*S root)%nat /\ FormulaTopology.ordered (machine final) (length next) /\
    SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) (bound+RenameMemoIndexBounds.increment m shift arg).
Proof.
 intros Hmeta Hsip Hpositive Herror Harena Htopology Hlookup Hfalse Hnode Hbase Hmode Hshift Harg Hfuel Hroom
   Hshiftword Hargword Hraw Hindices Hceiling observations.
 assert (HsourceBound:RenameMemoIndexBounds.formula_bound bound source).
 { apply (SchemaEvaluationIndexBounds.formula_lookup bound fs root source);[|exact Hlookup].
   exact (SchemaEvaluationIndexBounds.canonical_raw_formulas s fs bound Harena Htopology Hraw). }
 refine (generated (bound+RenameMemoIndexBounds.increment m shift arg)%nat s bs ns fs source root base m shift arg bound
   Hmeta Hsip Hpositive Herror Harena Htopology Hlookup Hfalse Hnode Hbase Hmode Hshift Harg Hfuel Hroom
   Hshiftword Hargword HsourceBound Hindices Hceiling _ ltac:(lia) observations).
 exact (SchemaEvaluationIndexBounds.raw_arena_mono s (length fs) bound
   (bound+RenameMemoIndexBounds.increment m shift arg) ltac:(lia) Hraw).
Qed.
End RenameMemoIndexRun.
