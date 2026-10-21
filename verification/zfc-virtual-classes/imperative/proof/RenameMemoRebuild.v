From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayFacts RenameMemoTable RenameMemoLookup RenameMemoPlacement
  RenameMemoCapacity RenameMemoVacant RenameMemoBuffers RenameMemoProbe ObservedLocal Observation LocalObservation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoRebuild.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoBuffers.
Definition outer_with (scan : Z -> LocalAction unit) total remaining : LocalAction LoopOutcome := ltac:(
  let code := eval unfold rebuild_body,rebuilding in (rebuild_body total remaining) in
  let code := eval cbn beta zeta in code in
  match code with context [bind (numberLocalGet _ _ _ vardef_0__renameCacheGrow_size) ?next] =>
    let candidate := eval cbn beta in (next 0%Z) in
    lazymatch candidate with loop _ _ =>
      let abstracted := eval pattern next in code in
      lazymatch abstracted with ?family _ => exact (family scan) end
    end
  end).
Lemma outer_actual total remaining : rebuild_body total remaining = outer_with
  (fun size=>loop (Z.to_nat size) (RenameMemoProbe.probe_body total remaining)) total remaining.
Proof. reflexivity. Qed.
Definition hashed s (e : RenameMemoTable.entry) := hash_state s 5 (RenameMemoTable.node e) (RenameMemoTable.depth e).
Definition start_frame (f : Frame) size e :=
  setNum (setNum (setMachine f (hashed (machine f) e)) vardef_0__renameCacheGrow_slot
    (meta_value (hashed (machine f) e) 28 mod Z.of_nat size)) vardef_0__renameCacheGrow_placed 0.
Local Opaque funcdef_0__formulaHash hash_state.
Theorem generated_empty (f : Frame) total remaining source e observations :
  total - Z.of_nat remaining - 1 = Z.of_nat source ->
  (source < length (memory (machine f) arraydef_0__renameMemo))%nat ->
  RenameMemoLookup.table (machine f) source = e -> RenameMemoTable.occupied e = 0 ->
  execLocalObserved (rebuild_body total remaining) (f,observations) = Some (KeepGoing,(f,observations)).
Proof.
  intros Hsource Hmemo Hentry Hempty. destruct f as [s bs ns]. cbn [machine] in *. unfold rebuild_body,rebuilding.
  unfold RenameMemoLookup.table in Hentry.
  repeat first [progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |progress cbn [optionBind fst snd]
    |progress rewrite Hsource |progress rewrite Nat2Z.id
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine]; now rewrite Nat2Z.id)
    |match goal with Hrawentry : @List.nth _ _ _ _ = ?entry |-
        context [@List.nth ?T ?index ?entries ?zero] =>
      let Hraw:=fresh "Hraw" in assert (Hraw : @List.nth T index entries zero=entry) by exact Hrawentry;
      rewrite Hraw; clear Hraw end
    |progress rewrite Hentry
    |progress change (RenameMemoTable.occupied e = 0) in Hempty
    |match goal with |- context [bool_decide ?P] => progress rewrite (bool_decide_false P) by
       (unfold RenameMemoTable.occupied in Hempty; congruence) end
    |progress cbn [dropWithinLoop execLocalObserved]
  ]. reflexivity.
Qed.
Theorem generated_entry_composition scan (f after : Frame) total remaining source size e observations :
  total - Z.of_nat remaining - 1 = Z.of_nat source ->
  (source < length (memory (machine f) arraydef_0__renameMemo))%nat ->
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat -> 0 < meta_value (machine f) 20 -> (0 < size)%nat ->
  nums f vardef_0__renameCacheGrow_size = Z.of_nat size -> RenameMemoLookup.table (machine f) source = e ->
  RenameMemoTable.occupied e <> 0 ->
  execLocalObserved (scan (Z.of_nat size)) (start_frame f size e,observations) = Some (tt,(after,observations)) ->
  nums after vardef_0__renameCacheGrow_placed = 1 ->
  execLocalObserved (outer_with scan total remaining) (f,observations) = Some (KeepGoing,(after,observations)).
Proof.
  intros Hsource Hmemo Hmeta Hsip Hpositive Hnonzero Hsize Hentry Hoccupied Hscan Hplaced.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold outer_with.
  unfold RenameMemoLookup.table in Hentry.
  repeat first [progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |progress cbn [optionBind fst snd]
    |progress rewrite Hsource |progress rewrite Nat2Z.id
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];
       lazymatch name with
       |arraydef_0__renameMemo=>now rewrite Nat2Z.id
       |arraydef_0__meta=>repeat rewrite RenameMemoLookup.hash_meta_length;
          eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta]
       end)
    |match goal with Hrawentry : @List.nth _ _ _ _ = ?entry |-
        context [@List.nth ?T ?index ?entries ?zero] =>
      let Hraw:=fresh "Hraw" in assert (Hraw : @List.nth T index entries zero=entry) by exact Hrawentry;
      rewrite Hraw; clear Hraw end
    |progress rewrite Hentry |progress rewrite Hsize
    |progress rewrite RenameMemoLookup.hash_observed by
       (cbn [machine setMachine setNum]; first [exact Hsip|exact Hpositive|lia])
    |progress replace (Z.to_nat 28) with 28%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by
          (unfold RenameMemoTable.occupied in Hoccupied; congruence)
       |progress rewrite (bool_decide_false P) by
          (unfold RenameMemoTable.occupied in Hoccupied; congruence)] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools
       Imperative.update decide decide_rel modIntUnsigned
       variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGrow varsfuncdef_0__renameCacheGrow_rec
       variableIndexEqualityDecidablevarsfuncdef_0__formulaHash varsfuncdef_0__formulaHash_rec]
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (scan ?n) ?state] =>
       let expression:=constr:(@execLocalObserved I T EI V EV R (scan n) state) in
       let Hrun:=fresh "Hrun" in assert (Hrun : expression=Some (tt,(after,observations))) by exact Hscan;
       rewrite Hrun; clear Hrun end
    |progress cbn [dropWithinLoop execLocalObserved]
  ]. reflexivity.
Qed.
Definition entry_key (e : RenameMemoTable.entry) := (RenameMemoTable.node e,RenameMemoTable.depth e).
Definition start_slot s index size := RenameMemoLookup.hash_start s (entry_key (RenameMemoLookup.table s index)) size.
Definition allocation s index size := RenameMemoVacant.vacant (scratch s) size (start_slot s index size) size.
Definition step_state s index size := let e:=RenameMemoLookup.table s index in
  if bool_decide (RenameMemoTable.occupied e = 0) then s else
  match allocation s index size with
  |Some slot=>write_scratch (hashed s e) slot (RenameMemoProbe.normalize e)
  |None=>store_meta (hashed s e) 8 1 end.
Definition ready s count size :=
  (31 < length (memory s arraydef_0__meta))%nat /\
  (0 < length (memory s arraydef_0__sipState))%nat /\ 0 < meta_value s 20 /\
  (count <= length (memory s arraydef_0__renameMemo))%nat /\
  (size <= length (memory s arraydef_0__renameMemoScratch))%nat /\
  (0 < size)%nat /\ Z.of_nat size <= maximum /\ meta_value s 8 = 0.
Lemma hashed_other s e name : name <> arraydef_0__meta -> name <> arraydef_0__sipState -> memory (hashed s e) name = memory s name.
Proof. intros. unfold hashed. now apply hash_preserves_array. Qed.
Lemma hashed_meta s e cell : cell <> 21%nat -> cell <> 28%nat -> meta_value (hashed s e) cell = meta_value s cell.
Proof. intros. unfold hashed. now apply hash_preserves_meta. Qed.
Lemma hashed_meta_length s e : length (memory (hashed s e) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold hashed. apply RenameMemoLookup.hash_meta_length. Qed.
Local Transparent hash_state.
Lemma hashed_sip_length s e : length (memory (hashed s e) arraydef_0__sipState) = length (memory s arraydef_0__sipState).
Proof. unfold hashed,hash_state. rewrite !store_meta_other by discriminate. apply hash_work_length. Qed.
Local Opaque hash_state.
Lemma hashed_scratch s e : scratch (hashed s e) = scratch s.
Proof. unfold scratch. now rewrite hashed_other by discriminate. Qed.
Lemma hashed_table s e : RenameMemoLookup.table (hashed s e) = RenameMemoLookup.table s.
Proof. unfold RenameMemoLookup.table. now rewrite hashed_other by discriminate. Qed.
Lemma start_parameters f size e : RenameMemoProbe.parameters f (start_frame f size e).
Proof. destruct f. split; reflexivity. Qed.
Lemma start_slot_value f count size source : ready (machine f) count size ->
  nums (start_frame f size (RenameMemoLookup.table (machine f) source)) vardef_0__renameCacheGrow_slot =
    Z.of_nat (start_slot (machine f) source size).
Proof.
  intros [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hnonzero [Hword Herror]]]]]]].
  change (meta_value (hashed (machine f) (RenameMemoLookup.table (machine f) source)) 28 mod Z.of_nat size =
    Z.of_nat (start_slot (machine f) source size)).
  unfold hashed. rewrite hash_result by (try assumption; lia). unfold start_slot,RenameMemoLookup.hash_start,entry_key.
  rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.
Theorem generated_step (f : Frame) total remaining count size source observations :
  ready (machine f) count size -> total-Z.of_nat remaining-1=Z.of_nat source -> (source<count)%nat ->
  nums f vardef_0__renameCacheGrow_size=Z.of_nat size ->
  (RenameMemoCapacity.live (scratch (machine f)) size < size)%nat ->
  exists final, execLocalObserved (rebuild_body total remaining) (f,observations)=Some (KeepGoing,(final,observations)) /\
    RenameMemoProbe.parameters f final /\ machine final=step_state (machine f) source size.
Proof.
  intros Hready Hsource Hindex Hsize Hroom.
  destruct Hready as [Hmeta [Hsip [Hpositive [Hmemo [Hscratch [Hnonzero [Hword Herror]]]]]]].
  set (e:=RenameMemoLookup.table (machine f) source).
  destruct (Z.eq_dec (RenameMemoTable.occupied e) 0) as [Hempty|Hoccupied].
  - exists f. split.
    + exact (generated_empty f total remaining source e observations Hsource ltac:(lia) eq_refl Hempty).
    + split; [split; reflexivity|]. unfold step_state. fold e. rewrite bool_decide_true by exact Hempty. reflexivity.
  - destruct (RenameMemoVacant.vacant_room (scratch (machine f)) size (start_slot (machine f) source size)
      (RenameMemoLookup.hash_start_bound (machine f) (entry_key e) size Hnonzero) Hroom) as [slot Halloc].
    set (start:=start_frame f size e).
    assert (Hstartmachine : machine start=hashed (machine f) e) by reflexivity.
    assert (Hinitial : nums start vardef_0__renameCacheGrow_slot=Z.of_nat (start_slot (machine f) source size)).
    { exact (start_slot_value f count size source ltac:(repeat split; assumption)). }
    destruct (RenameMemoProbe.generated_scan_observed size start total remaining size (start_slot (machine f) source size) source e observations
      Hsource Hnonzero Hword (RenameMemoLookup.hash_start_bound (machine f) (entry_key e) size Hnonzero)
      ltac:(rewrite Hstartmachine,hashed_other by discriminate; exact Hscratch)
      ltac:(rewrite Hstartmachine,hashed_other by discriminate; lia) Hinitial ltac:(exact Hsize) eq_refl
      ltac:(rewrite Hstartmachine,hashed_table; reflexivity)) as [after [Hscan [Hparameters [Hplaced Hmachine]]]].
    rewrite Hstartmachine,hashed_scratch in Hplaced,Hmachine. rewrite Halloc in Hplaced,Hmachine.
    assert (HscanZ : execLocalObserved (loop (Z.to_nat (Z.of_nat size)) (RenameMemoProbe.probe_body total remaining))
      (start,observations)=Some (tt,(after,observations))) by (now rewrite Nat2Z.id).
    pose proof (generated_entry_composition (fun n=>loop (Z.to_nat n) (RenameMemoProbe.probe_body total remaining))
      f after total remaining source size e observations Hsource ltac:(lia) Hmeta Hsip Hpositive Hnonzero Hsize eq_refl Hoccupied HscanZ Hplaced) as Hbody.
    rewrite <-outer_actual in Hbody. exists after. split; [exact Hbody|]. split.
    + eapply RenameMemoProbe.parameters_trans; [apply start_parameters|exact Hparameters].
    + unfold step_state. fold e. rewrite bool_decide_false by exact Hoccupied. unfold allocation. rewrite Halloc. exact Hmachine.
Qed.
End RenameMemoRebuild.

