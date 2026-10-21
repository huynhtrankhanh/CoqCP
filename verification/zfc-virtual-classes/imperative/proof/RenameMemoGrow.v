From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity
  RenameMemoBuffers RenameMemoProbe RenameMemoRebuild RenameMemoRebuildInvariant RenameMemoRebuildLoop
  RenameMemoResize RenameMemoBufferFacts RenameMemoPrefix ObservedLocal Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoGrow.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoBuffers RenameMemoRebuild RenameMemoRebuildInvariant
  RenameMemoRebuildLoop RenameMemoBufferFacts.
Local Opaque funcdef_0__formulaHash hash_state.
Definition finalized rebuilt size:=store_meta (copied rebuilt size) 29 (Z.of_nat size).
Theorem generated_execution s bs ns count observations meaning :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> meta_value s 29=Z.of_nat count -> (0<count)%nat ->
  Z.of_nat count<=9223372036854775807 -> (count<=length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  exists rebuilt, execObserved (funcdef_0__renameCacheGrow bs ns) (s,observations)=Some (tt,(finalized rebuilt (2*count),observations)) /\
    invariant (cleared s (2*count)) rebuilt count count (2*count)
      (fun query=>RenameMemoLookup.hash_start (cleared s (2*count)) query (2*count)) meaning.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hmemo Hmeaning.
  set (size:=(2*count)%nat).
  assert (Hnewword : Z.of_nat size<=maximum).
  { unfold size. rewrite <-RenameMemoResize.double_value. exact (proj2 (RenameMemoResize.double_word count Hword)). }
  assert (Hsize : (count<size)%nat) by (unfold size; lia).
  set (initial:=({|machine:=s;bools:=bs;nums:=ns|}:Frame)).
  set (start:=RenameMemoResize.start_frame initial count).
  set (fclear:=setMachine start (cleared s size)).
  assert (Hclear : execLocalObserved (clearing (Z.of_nat size)) (start,observations)=Some (tt,(fclear,observations))).
  { exact (generated_clear_observed start size observations (RenameMemoResize.scratch_capacity s size)). }
  assert (Hready : ready (machine fclear) count size).
  { apply cleared_ready; try assumption; lia. }
  assert (Hclearmeaning : RenameMemoTable.represents (RenameMemoLookup.table (machine fclear)) count meaning).
  { change (RenameMemoTable.represents (RenameMemoLookup.table (cleared s size)) count meaning). now rewrite cleared_table. }
  destruct (generated_rebuild fclear count size meaning observations Hsize eq_refl Hready
    (cleared_empty s size) Hclearmeaning) as [frebuilt [Hrebuild [Hparameters Hinv]]].
  assert (Hrsize : nums frebuilt vardef_0__renameCacheGrow_size=Z.of_nat size).
  { exact (proj2 Hparameters). }
  pose proof (inv_ready _ _ _ _ _ _ _ Hinv) as Hrready.
  destruct Hrready as [Hrmeta [Hrsip [Hrpositive [Hrmemo [Hrscratch [Hrnonzero [Hrword Hrerror]]]]]]].
  set (copyStart:=RenameMemoResize.copy_start frebuilt size).
  set (fcopied:=setMachine copyStart (copied (machine frebuilt) size)).
  assert (Hcopy : execLocalObserved (copying (Z.of_nat size)) (copyStart,observations)=Some (tt,(fcopied,observations))).
  { apply generated_copy_observed.
    - change (size<=length (memory (RenameMemoResize.memo_grown (machine frebuilt) size) arraydef_0__renameMemoScratch))%nat.
      rewrite RenameMemoResize.memo_grown_other by discriminate. exact Hrscratch.
    - apply RenameMemoResize.memo_capacity. }
  assert (Hpmeta : (31<length (memory (machine fcopied) arraydef_0__meta))%nat).
  { change (31<length (memory (copied (machine frebuilt) size) arraydef_0__meta))%nat.
    rewrite copied_other by discriminate. exact Hrmeta. }
  pose proof (RenameMemoResize.generated_composition clearing rebuilding copying initial fclear frebuilt fcopied count
    observations Hmeta Hcount Hword Hclear eq_refl eq_refl Hrebuild Hrsize Hrerror Hrmeta Hcopy Hrsize Hpmeta) as Hbody.
  rewrite <-actual_body in Hbody.
  exists (machine frebuilt). split; [|exact Hinv].
  unfold funcdef_0__renameCacheGrow. rewrite ObservedLocal.eliminate_correct.
  change (optionBind (execLocalObserved funcdef_0__renameCacheGrow_body (initial,observations))
    (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))=Some (tt,(finalized (machine frebuilt) (2*count),observations))).
  rewrite Hbody. reflexivity.
Qed.
Lemma finalized_other s size name : name<>arraydef_0__meta -> name<>arraydef_0__renameMemo ->
  memory (finalized s size) name=memory s name.
Proof. intros Hmeta Hmemo. unfold finalized. rewrite store_meta_other by exact Hmeta. now apply copied_other. Qed.
Lemma finalized_meta s size cell : cell<>29%nat -> meta_value (finalized s size) cell=meta_value s cell.
Proof. intro Hcell. unfold finalized. rewrite meta_store_other by exact Hcell. apply copied_meta. Qed.
Lemma finalized_meta_length s size : length (memory (finalized s size) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold finalized. rewrite store_meta_length. now rewrite copied_other by discriminate. Qed.
Lemma finalized_capacity s size : (size<=length (memory (finalized s size) arraydef_0__renameMemo))%nat.
Proof. unfold finalized. rewrite store_meta_other by discriminate. apply copied_capacity. Qed.
Lemma finalized_size s size : (29<length (memory s arraydef_0__meta))%nat -> meta_value (finalized s size) 29=Z.of_nat size.
Proof. intro Hmeta. unfold finalized. apply meta_store_same. now rewrite copied_other by discriminate. Qed.
Lemma finalized_entry s size index : (index<size)%nat -> RenameMemoLookup.table (finalized s size) index=scratch s index.
Proof. intro Hindex. unfold RenameMemoLookup.table at 1. unfold finalized. rewrite store_meta_other by discriminate. now apply copied_entry. Qed.
Lemma finalized_hash s size query : RenameMemoLookup.hash_start (finalized s size) query size=RenameMemoLookup.hash_start s query size.
Proof. unfold RenameMemoLookup.hash_start. now rewrite !finalized_meta by lia. Qed.
Lemma finalized_io s size : stdin (finalized s size)=stdin s /\ stdout (finalized s size)=stdout s.
Proof. unfold finalized. exact (copied_io s size). Qed.
Lemma finalized_live s size : RenameMemoCapacity.live (RenameMemoLookup.table (finalized s size)) size=
  RenameMemoCapacity.live (scratch s) size.
Proof. apply RenameMemoCapacity.live_ext. apply finalized_entry. Qed.
Theorem finalized_meaning s size meaning : RenameMemoTable.represents (scratch s) size meaning ->
  RenameMemoTable.represents (RenameMemoLookup.table (finalized s size)) size meaning.
Proof.
  intro Hmeaning. exact (RenameMemoPrefix.represents_prefix (scratch s) (RenameMemoLookup.table (finalized s size)) size meaning
    ltac:(intros; symmetry; now apply finalized_entry) Hmeaning).
Qed.
Theorem finalized_indexed s size hash : (0<size)%nat -> RenameMemoPlacement.indexed_by (scratch s) size hash ->
  (forall query, hash query=RenameMemoLookup.hash_start s query size) -> RenameMemoLookup.indexed (finalized s size) size.
Proof.
  intros Hsize Hindexed Hhash.
  assert (Hprefix : RenameMemoPlacement.indexed_by (RenameMemoLookup.table (finalized s size)) size hash).
  { exact (RenameMemoPrefix.indexed_prefix (scratch s) (RenameMemoLookup.table (finalized s size)) size hash Hsize
      ltac:(intros; symmetry; now apply finalized_entry)
      ltac:(intro query; rewrite Hhash; now apply RenameMemoLookup.hash_start_bound) Hindexed). }
  intros index Hindex Hoccupied. destruct (Hprefix index Hindex Hoccupied) as [distance [Hdistance Hpath]].
  exists distance. split; [exact Hdistance|]. rewrite finalized_hash,<-Hhash. exact Hpath.
Qed.
Definition storage_frame s t :=
  (forall name, name<>arraydef_0__meta -> name<>arraydef_0__sipState -> name<>arraydef_0__renameMemo ->
    name<>arraydef_0__renameMemoScratch -> memory t name=memory s name) /\
  (forall cell, cell<>21%nat -> cell<>28%nat -> cell<>29%nat -> meta_value t cell=meta_value s cell) /\
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory t arraydef_0__sipState)=length (memory s arraydef_0__sipState) /\
  stdin t=stdin s /\ stdout t=stdout s.
Record postcondition s t count meaning : Prop := {
  post_capacity : meta_value t 29=Z.of_nat (2*count);
  post_allocated : (2*count<=length (memory t arraydef_0__renameMemo))%nat;
  post_frame : storage_frame s t;
  post_nonfatal : meta_value t 8=0;
  post_live : RenameMemoCapacity.live (RenameMemoLookup.table t) (2*count)=RenameMemoCapacity.live (RenameMemoLookup.table s) count;
  post_meaning : RenameMemoTable.represents (RenameMemoLookup.table t) (2*count) meaning;
  post_indexed : RenameMemoLookup.indexed t (2*count);
  post_covered : forall index, (index<count)%nat -> RenameMemoTable.occupied (RenameMemoLookup.table s index)<>0 ->
    exists slot, (slot<2*count)%nat /\ RenameMemoLookup.table t slot=RenameMemoProbe.normalize (RenameMemoLookup.table s index)
}.
Theorem finalized_invariant s rebuilt count meaning :
  invariant (cleared s (2*count)) rebuilt count count (2*count)
    (fun query=>RenameMemoLookup.hash_start (cleared s (2*count)) query (2*count)) meaning ->
  postcondition s (finalized rebuilt (2*count)) count meaning.
Proof.
  intros [Hready Hpreserved Hlive Hmeaning Hindexed Hcovered Hhash].
  destruct Hready as [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]].
  destruct Hpreserved as [Ha [Hm [Hl [Hs [Hc [Hi Ho]]]]]].
  constructor.
  - apply finalized_size. lia.
  - apply finalized_capacity.
  - unfold storage_frame. split.
    + intros name Hmet Hsipstate Hmem Hscratchname. rewrite finalized_other by assumption.
      rewrite Ha by assumption. now rewrite cleared_other by assumption.
    + split.
      * intros cell H21 H28 H29. rewrite finalized_meta by exact H29. rewrite Hm by assumption. apply cleared_meta.
      * split; [rewrite finalized_meta_length,Hl; now rewrite cleared_other by discriminate|].
        split; [rewrite finalized_other by discriminate; rewrite Hs; now rewrite cleared_other by discriminate|].
        destruct (finalized_io rebuilt (2*count)) as [Hfi Hfo].
        destruct (cleared_io s (2*count)) as [Hci Hco]. split; congruence.
  - rewrite finalized_meta by lia. exact Herror.
  - rewrite finalized_live,Hlive,cleared_table. reflexivity.
  - now apply finalized_meaning.
  - exact (finalized_indexed rebuilt (2*count) _ Hsize Hindexed Hhash).
  - intros index Hindex Hoccupied. unfold covered in Hcovered. rewrite cleared_table in Hcovered.
    destruct (Hcovered index Hindex Hoccupied) as [slot [Hslot Hentry]]. exists slot. split; [exact Hslot|].
    rewrite finalized_entry by exact Hslot. exact Hentry.
Qed.
Theorem generated_invariant s bs ns count observations meaning :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> meta_value s 29=Z.of_nat count -> (0<count)%nat ->
  Z.of_nat count<=9223372036854775807 -> (count<=length (memory s arraydef_0__renameMemo))%nat ->
  RenameMemoTable.represents (RenameMemoLookup.table s) count meaning ->
  exists final, execObserved (funcdef_0__renameCacheGrow bs ns) (s,observations)=Some (tt,(final,observations)) /\
    postcondition s final count meaning.
Proof.
  intros Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hmemo Hmeaning.
  destruct (generated_execution s bs ns count observations meaning Hmeta Hsip Hpositive Herror Hcount Hnonzero Hword Hmemo Hmeaning)
    as [rebuilt [Hrun Hinv]]. exists (finalized rebuilt (2*count)). split; [exact Hrun|]. now apply finalized_invariant.
Qed.
End RenameMemoGrow.
