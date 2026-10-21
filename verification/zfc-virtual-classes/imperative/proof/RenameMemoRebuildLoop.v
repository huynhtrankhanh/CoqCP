From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity
  RenameMemoVacant RenameMemoBuffers RenameMemoProbe RenameMemoRebuild RenameMemoRebuildInvariant ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoRebuildLoop.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoBuffers RenameMemoRebuild RenameMemoRebuildInvariant.
Local Opaque hash_state.
Record invariant (original current : Machine) (processed count size : nat)
  (hash : RenameMemoTable.key->nat) (meaning : RenameMemoTable.key->Z->Prop) : Prop := {
  inv_ready : ready current count size;
  inv_preserved : preserved original current;
  inv_live : RenameMemoCapacity.live (scratch current) size=RenameMemoCapacity.live (RenameMemoLookup.table original) processed;
  inv_meaning : RenameMemoTable.represents (scratch current) size meaning;
  inv_indexed : RenameMemoPlacement.indexed_by (scratch current) size hash;
  inv_covered : covered original current processed size;
  inv_hash : forall query, hash query=RenameMemoLookup.hash_start current query size
}.
Theorem invariant_room original current processed count size hash meaning : (processed<=count)%nat -> (count<size)%nat ->
  invariant original current processed count size hash meaning -> (RenameMemoCapacity.live (scratch current) size<size)%nat.
Proof.
  intros Hprocessed Hsize [_ _ Hlive _ _ _ _]. rewrite Hlive.
  pose proof (RenameMemoCapacity.live_bound (RenameMemoLookup.table original) processed). lia.
Qed.
Theorem invariant_step original current processed count size hash meaning : (processed<count)%nat -> (count<size)%nat ->
  RenameMemoTable.represents (RenameMemoLookup.table original) count meaning ->
  invariant original current processed count size hash meaning ->
  invariant original (step_state current processed size) (S processed) count size hash meaning.
Proof.
  intros Hprocessed Hsize Hsource Hinv.
  pose proof (invariant_room original current processed count size hash meaning ltac:(lia) Hsize Hinv) as Hroom.
  destruct Hinv as [Hready Hpreserved Hlive Hmeaning Hindexed Hcovered Hhash].
  pose proof (step_preserved current processed count size Hready Hroom) as Hstep.
  pose proof (preserved_table original current Hpreserved) as Htable.
  constructor.
  - exact (preserved_ready current _ count size Hstep Hready).
  - exact (preserved_trans original current _ Hpreserved Hstep).
  - rewrite step_live with (count:=count) by assumption. rewrite Hlive,Htable. reflexivity.
  - apply step_represents with (count:=count); try assumption. intros Hoccupied.
    rewrite Htable in Hoccupied |- *. now apply Hsource.
  - now apply step_indexed with (count:=count).
  - now apply step_covered with (count:=count).
  - intro query. rewrite (preserved_hash current _ size query Hstep). apply Hhash.
Qed.
Theorem generated_loop fuel (f : Frame) original start count size hash meaning observations :
  (start+fuel=count)%nat -> (count<size)%nat -> nums f vardef_0__renameCacheGrow_size=Z.of_nat size ->
  RenameMemoTable.represents (RenameMemoLookup.table original) count meaning ->
  invariant original (machine f) start count size hash meaning ->
  exists final, execLocalObserved (loop fuel (rebuild_body (Z.of_nat count))) (f,observations)=Some (tt,(final,observations)) /\
    RenameMemoProbe.parameters f final /\ invariant original (machine final) count count size hash meaning.
Proof.
  induction fuel as [|fuel IH] in f,start|-*.
  - intros Hcount Hsize Hlocals Hsource Hinv. assert (start=count) as -> by lia.
    exists f. split; [reflexivity|]. split; [split; reflexivity|exact Hinv].
  - intros Hcount Hsize Hlocals Hsource Hinv.
    pose proof (invariant_room original (machine f) start count size hash meaning ltac:(lia) Hsize Hinv) as Hroom.
    destruct (generated_step f (Z.of_nat count) fuel count size start observations (inv_ready _ _ _ _ _ _ _ Hinv)
      ltac:(lia) ltac:(lia) Hlocals Hroom) as [after [Hstep [Hparameters Hmachine]]].
    assert (Hnext : invariant original (machine after) (S start) count size hash meaning).
    { rewrite Hmachine. exact (invariant_step original (machine f) start count size hash meaning ltac:(lia) Hsize Hsource Hinv). }
    assert (Hlocals' : nums after vardef_0__renameCacheGrow_size=Z.of_nat size).
    { destruct Hparameters as [Hold Hnew]. congruence. }
    destruct (IH after (S start) ltac:(lia) Hsize Hlocals' Hsource Hnext) as [final [Hrun [Hparameters' Hfinal]]].
    exists final. split.
    + rewrite loop_S,ObservedLocal.local_bind,Hstep. exact Hrun.
    + split; [|exact Hfinal]. now apply RenameMemoProbe.parameters_trans with (g:=after).
Qed.
Lemma empty_live table size : (forall index, (index<size)%nat -> RenameMemoTable.occupied (table index)=0) ->
  RenameMemoCapacity.live table size=0%nat.
Proof.
  induction size as [|size IH]; [reflexivity|]. intros Hempty. cbn [RenameMemoCapacity.live].
  rewrite IH by (intros; apply Hempty; lia). rewrite bool_decide_true by (apply Hempty; lia). reflexivity.
Qed.
Theorem initial_invariant s count size meaning : ready s count size ->
  (forall index, (index<size)%nat -> scratch s index=(0,0,0,0)) ->
  invariant s s 0 count size (fun query=>RenameMemoLookup.hash_start s query size) meaning.
Proof.
  intros Hready Hempty. constructor.
  - exact Hready.
  - apply preserved_refl.
  - apply empty_live. intros index Hindex. rewrite Hempty by exact Hindex. reflexivity.
  - intros index Hindex Hoccupied. rewrite Hempty in Hoccupied by exact Hindex. contradiction.
  - intros index Hindex Hoccupied. rewrite Hempty in Hoccupied by exact Hindex. contradiction.
  - intros index Hindex. lia.
  - reflexivity.
Qed.
Theorem generated_rebuild (f : Frame) count size meaning observations :
  (count<size)%nat -> nums f vardef_0__renameCacheGrow_size=Z.of_nat size -> ready (machine f) count size ->
  (forall index, (index<size)%nat -> scratch (machine f) index=(0,0,0,0)) ->
  RenameMemoTable.represents (RenameMemoLookup.table (machine f)) count meaning ->
  exists final, execLocalObserved (rebuilding (Z.of_nat count)) (f,observations)=Some (tt,(final,observations)) /\
    RenameMemoProbe.parameters f final /\ invariant (machine f) (machine final) count count size
      (fun query=>RenameMemoLookup.hash_start (machine f) query size) meaning.
Proof.
  intros Hsize Hlocals Hready Hempty Hmeaning. rewrite rebuilding_is_loop,Nat2Z.id.
  exact (generated_loop count f (machine f) 0 count size _ meaning observations eq_refl Hsize Hlocals Hmeaning
    (initial_invariant (machine f) count size meaning Hready Hempty)).
Qed.
End RenameMemoRebuildLoop.
