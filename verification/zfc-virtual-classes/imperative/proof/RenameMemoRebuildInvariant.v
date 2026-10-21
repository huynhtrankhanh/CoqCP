From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity
  RenameMemoVacant RenameMemoBuffers RenameMemoProbe RenameMemoRebuild.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoRebuildInvariant.
Import IndexExecution SipHashExecution RenameMemoBuffers RenameMemoRebuild.
Local Opaque hash_state.
Definition preserved s t :=
  (forall name, name<>arraydef_0__meta -> name<>arraydef_0__sipState -> name<>arraydef_0__renameMemoScratch -> memory t name=memory s name) /\
  (forall cell, cell<>21%nat -> cell<>28%nat -> meta_value t cell=meta_value s cell) /\
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  length (memory t arraydef_0__sipState)=length (memory s arraydef_0__sipState) /\
  length (memory t arraydef_0__renameMemoScratch)=length (memory s arraydef_0__renameMemoScratch) /\
  stdin t=stdin s /\ stdout t=stdout s.
Lemma preserved_refl s : preserved s s.
Proof. repeat split; reflexivity. Qed.
Lemma preserved_trans s t u : preserved s t -> preserved t u -> preserved s u.
Proof.
  intros [Ha [Hm [Hl [Hs [Hc [Hi Ho]]]]]] [Ha' [Hm' [Hl' [Hs' [Hc' [Hi' Ho']]]]]].
  split; [intros; now rewrite Ha',Ha by assumption|]. split; [intros; now rewrite Hm',Hm by assumption|]. repeat split; congruence.
Qed.
Lemma allocation_available s source size : (0<size)%nat -> (RenameMemoCapacity.live (scratch s) size < size)%nat ->
  exists slot, allocation s source size=Some slot.
Proof. intros Hsize Hroom. apply RenameMemoVacant.vacant_room; [now apply RenameMemoLookup.hash_start_bound|exact Hroom]. Qed.
Theorem step_preserved s source count size : ready s count size -> (RenameMemoCapacity.live (scratch s) size<size)%nat ->
  preserved s (step_state s source size).
Proof.
  intros [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]] Hroom.
  destruct (allocation_available s source size Hsize Hroom) as [slot Halloc]. unfold step_state.
  destruct bool_decide; [apply preserved_refl|]. rewrite Halloc.
  split.
  - intros name Hm Hs Hc. rewrite scratch_other by exact Hc. now apply hashed_other.
  - split.
    + intros cell H21 H28. unfold meta_value at 1. rewrite scratch_other by discriminate.
      change (meta_value (hashed s (RenameMemoLookup.table s source)) cell=meta_value s cell). now apply hashed_meta.
    + split; [rewrite scratch_other by discriminate; apply hashed_meta_length|].
      split; [rewrite scratch_other by discriminate; apply hashed_sip_length|].
      split; [rewrite scratch_length,hashed_other by discriminate; reflexivity|]. split; reflexivity.
Qed.
Lemma preserved_table s t : preserved s t -> RenameMemoLookup.table t=RenameMemoLookup.table s.
Proof. intros [Harrays _]. unfold RenameMemoLookup.table. now rewrite Harrays by discriminate. Qed.
Lemma preserved_hash s t size query : preserved s t -> RenameMemoLookup.hash_start t query size=RenameMemoLookup.hash_start s query size.
Proof. intros [_ [Hmeta _]]. unfold RenameMemoLookup.hash_start. now rewrite !Hmeta by lia. Qed.
Lemma preserved_ready s t count size : preserved s t -> ready s count size -> ready t count size.
Proof.
  intros [Ha [Hm [Hl [Hs [Hc [Hi Ho]]]]]] [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]].
  unfold ready. rewrite Hl,Hs,Hc. rewrite Ha by discriminate. rewrite !Hm by lia. repeat split; assumption.
Qed.
Lemma written_pointwise s slot e index : (slot<length (memory s arraydef_0__renameMemoScratch))%nat ->
  scratch (write_scratch s slot (RenameMemoProbe.normalize e)) index=
  RenameMemoTable.put (scratch s) slot (RenameMemoProbe.normalize e) index.
Proof.
  intro Hslot. unfold RenameMemoTable.put. destruct (numbers.Nat.eq_dec index slot) as [->|Hother].
  - now apply scratch_at_same.
  - now apply scratch_at_other.
Qed.
Theorem step_pointwise s source size slot : (0<size)%nat ->
  (size<=length (memory s arraydef_0__renameMemoScratch))%nat ->
  RenameMemoTable.occupied (RenameMemoLookup.table s source)<>0 -> allocation s source size=Some slot ->
  forall index, scratch (step_state s source size) index=
    RenameMemoTable.put (scratch s) slot (RenameMemoProbe.normalize (RenameMemoLookup.table s source)) index.
Proof.
  intros Hsize Hscratch Hoccupied Halloc index. unfold step_state. rewrite bool_decide_false by exact Hoccupied. rewrite Halloc.
  rewrite written_pointwise,hashed_scratch; [reflexivity|]. rewrite hashed_other by discriminate.
  pose proof (proj1 (RenameMemoVacant.vacant_sound (scratch s) size (start_slot s source size) size slot Hsize
    (RenameMemoLookup.hash_start_bound s (entry_key (RenameMemoLookup.table s source)) size Hsize) Halloc)). lia.
Qed.
Theorem step_live s source count size : ready s count size -> (RenameMemoCapacity.live (scratch s) size<size)%nat ->
  RenameMemoCapacity.live (scratch (step_state s source size)) size=
    (RenameMemoCapacity.live (scratch s) size + if bool_decide (RenameMemoTable.occupied (RenameMemoLookup.table s source)=0%Z) then 0 else 1)%nat.
Proof.
  intros [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]] Hroom.
  destruct (Z.eq_dec (RenameMemoTable.occupied (RenameMemoLookup.table s source)) 0) as [Hempty|Hoccupied].
  - unfold step_state. rewrite bool_decide_true by exact Hempty. lia.
  - rewrite bool_decide_false by exact Hoccupied.
    destruct (allocation_available s source size Hsize Hroom) as [slot Halloc].
    transitivity (RenameMemoCapacity.live (RenameMemoTable.put (scratch s) slot
      (RenameMemoProbe.normalize (RenameMemoLookup.table s source))) size).
    + apply RenameMemoCapacity.live_ext. intros index Hindex. now apply step_pointwise.
    + unfold RenameMemoProbe.normalize. pose proof (RenameMemoVacant.vacant_live (scratch s) size (start_slot s source size) slot
        (entry_key (RenameMemoLookup.table s source)) (RenameMemoTable.value (RenameMemoLookup.table s source)) Hsize
        (RenameMemoLookup.hash_start_bound s _ size Hsize) Halloc) as Hnew.
      match goal with |- ?left = _ =>
        assert (Hactual : left=S (RenameMemoCapacity.live (scratch s) size)) by exact Hnew;
        rewrite Hactual; lia end.
Qed.
Theorem step_represents s source count size meaning : ready s count size ->
  (RenameMemoCapacity.live (scratch s) size<size)%nat ->
  RenameMemoTable.represents (scratch s) size meaning ->
  (RenameMemoTable.occupied (RenameMemoLookup.table s source)<>0 ->
    meaning (entry_key (RenameMemoLookup.table s source)) (RenameMemoTable.value (RenameMemoLookup.table s source))) ->
  RenameMemoTable.represents (scratch (step_state s source size)) size meaning.
Proof.
  intros [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]] Hroom Hmeaning Hentry.
  destruct (Z.eq_dec (RenameMemoTable.occupied (RenameMemoLookup.table s source)) 0) as [Hempty|Hoccupied].
  - unfold step_state. rewrite bool_decide_true by exact Hempty. exact Hmeaning.
  - destruct (allocation_available s source size Hsize Hroom) as [slot Halloc].
    apply RenameMemoPlacement.represents_ext with
      (table:=RenameMemoTable.put (scratch s) slot (RenameMemoProbe.normalize (RenameMemoLookup.table s source))).
    + intro index. symmetry. now apply step_pointwise.
    + exact (RenameMemoTable.put_represents (scratch s) size meaning slot (entry_key (RenameMemoLookup.table s source))
        (RenameMemoTable.value (RenameMemoLookup.table s source)) Hmeaning (Hentry Hoccupied)).
Qed.
Theorem step_indexed s source count size hash : ready s count size ->
  (RenameMemoCapacity.live (scratch s) size<size)%nat -> RenameMemoPlacement.indexed_by (scratch s) size hash ->
  (forall query, hash query=RenameMemoLookup.hash_start s query size) ->
  RenameMemoPlacement.indexed_by (scratch (step_state s source size)) size hash.
Proof.
  intros [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]] Hroom Hindexed Hhash.
  destruct (Z.eq_dec (RenameMemoTable.occupied (RenameMemoLookup.table s source)) 0) as [Hempty|Hoccupied].
  - unfold step_state. rewrite bool_decide_true by exact Hempty. exact Hindexed.
  - destruct (allocation_available s source size Hsize Hroom) as [slot Halloc].
    apply RenameMemoPlacement.indexed_ext with
      (table:=RenameMemoTable.put (scratch s) slot (RenameMemoProbe.normalize (RenameMemoLookup.table s source))).
    + intro index. symmetry. now apply step_pointwise.
    + exact (RenameMemoVacant.vacant_indexed (scratch s) size hash (entry_key (RenameMemoLookup.table s source))
        (RenameMemoTable.value (RenameMemoLookup.table s source)) (start_slot s source size) slot Hsize
        (RenameMemoLookup.hash_start_bound s _ size Hsize) ltac:(symmetry; apply Hhash) Hindexed Halloc).
Qed.
Theorem step_keeps_occupied s source count size old : ready s count size ->
  (RenameMemoCapacity.live (scratch s) size<size)%nat -> RenameMemoTable.occupied (scratch s old)<>0 ->
  scratch (step_state s source size) old=scratch s old.
Proof.
  intros [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]] Hroom Hold.
  destruct (Z.eq_dec (RenameMemoTable.occupied (RenameMemoLookup.table s source)) 0) as [Hempty|Hoccupied].
  - unfold step_state. rewrite bool_decide_true by exact Hempty. reflexivity.
  - destruct (allocation_available s source size Hsize Hroom) as [slot Halloc].
    rewrite step_pointwise with (slot:=slot) by assumption. exact (RenameMemoVacant.vacant_preserves_entry (scratch s) size (start_slot s source size) slot
      (entry_key (RenameMemoLookup.table s source)) (RenameMemoTable.value (RenameMemoLookup.table s source)) old
      Hsize (RenameMemoLookup.hash_start_bound s _ size Hsize) Halloc Hold).
Qed.
Definition covered (source current : Machine) processed size :=
  forall index, (index<processed)%nat -> RenameMemoTable.occupied (RenameMemoLookup.table source index)<>0 ->
    exists slot, (slot<size)%nat /\ scratch current slot=RenameMemoProbe.normalize (RenameMemoLookup.table source index).
Theorem step_covered original s source count size : ready s count size ->
  (RenameMemoCapacity.live (scratch s) size<size)%nat -> covered original s source size ->
  RenameMemoLookup.table s=RenameMemoLookup.table original -> covered original (step_state s source size) (S source) size.
Proof.
  intros Hready Hroom Hcovered Hsource index Hindex Hoccupied.
  destruct Hready as [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hsize [Hword Herror]]]]]]].
  destruct (Nat.eq_dec index source) as [->|Hother].
  - assert (Hcurrent : RenameMemoTable.occupied (RenameMemoLookup.table s source)<>0) by (now rewrite Hsource).
    destruct (allocation_available s source size Hsize Hroom) as [slot Halloc].
    pose proof (proj1 (RenameMemoVacant.vacant_sound (scratch s) size (start_slot s source size) size slot Hsize
      (RenameMemoLookup.hash_start_bound s _ size Hsize) Halloc)) as Hslot.
    exists slot. split; [exact Hslot|]. rewrite step_pointwise with (slot:=slot) by assumption.
    unfold RenameMemoTable.put. destruct (numbers.Nat.eq_dec slot slot); [now rewrite Hsource|contradiction].
  - destruct (Hcovered index ltac:(lia) Hoccupied) as [slot [Hslot Hentry]]. exists slot. split; [exact Hslot|].
    rewrite step_keeps_occupied with (count:=count); [exact Hentry| |exact Hroom|].
    + unfold ready. repeat split; assumption.
    + rewrite Hentry. cbn [RenameMemoProbe.normalize RenameMemoTable.occupied]. discriminate.
Qed.
End RenameMemoRebuildInvariant.
