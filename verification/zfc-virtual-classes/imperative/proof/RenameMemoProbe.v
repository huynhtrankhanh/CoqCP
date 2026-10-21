From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayFacts RenameMemoTable RenameMemoVacant RenameMemoBuffers
  RenameMemoLookup ObservedLocal Observation LocalObservation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoProbe.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoBuffers.
Definition normalize (e : RenameMemoTable.entry) :=
  (RenameMemoTable.node e,RenameMemoTable.depth e,RenameMemoTable.value e,1%Z).
Definition advance (f : Frame) size slot :=
  setNum f vardef_0__renameCacheGrow_slot (Z.of_nat (RenameMemoTable.next size slot)).
Definition placed (f : Frame) slot e :=
  setNum (setMachine f (write_scratch (machine f) slot (normalize e))) vardef_0__renameCacheGrow_placed 1.
Definition probe_body total outer_remaining : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold rebuild_body,rebuilding in (rebuild_body total outer_remaining) in
  let code := eval cbn beta zeta in code in
  match code with context [loop _ ?body] => let body := eval cbn zeta in body in exact body end).
Theorem generated_probe (f : Frame) total outer_remaining remaining size slot source e target :
  total - Z.of_nat outer_remaining - 1 = Z.of_nat source ->
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  (source < length (memory (machine f) arraydef_0__renameMemo))%nat ->
  nums f vardef_0__renameCacheGrow_slot = Z.of_nat slot -> nums f vardef_0__renameCacheGrow_size = Z.of_nat size ->
  RenameMemoLookup.table (machine f) source = e -> scratch (machine f) slot = target ->
  execLocal (probe_body total outer_remaining remaining) f =
    if bool_decide (RenameMemoTable.occupied target = 0) then Some (Stop,placed f slot e)
    else Some (KeepGoing,advance f size slot).
Proof.
  intros Hsource Hpositive Hword Hslot Hscratch Hmemo Hindex Hsize Hentry Htarget.
  assert (Hincrement : word (Z.of_nat slot+1)) by (unfold word; lia).
  destruct e as [[[node depth] value] flag], target as [[[tn td] tv] occupied].
  destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold RenameMemoLookup.table in Hentry. unfold scratch in Htarget.
  destruct (Z.eq_dec occupied 0).
  all: unfold probe_body,rebuild_body,rebuilding; cbn zeta.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    retrieve numberLocalGet numberLocalSet store break addInt modIntUnsigned
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGrow varsfuncdef_0__renameCacheGrow_rec
    RenameMemoTable.occupied RenameMemoTable.node RenameMemoTable.depth RenameMemoTable.value
    placed normalize advance RenameMemoTable.next].
  all: repeat first [progress rewrite Hsource |progress rewrite Hindex |progress rewrite Hsize
    |progress rewrite (coerce_word _ Hincrement) |progress rewrite Nat2Z.id
    |progress rewrite nth_lt_default with (default:=(0,0,0,0))
    |match goal with Hrawentry : @List.nth _ _ _ _ = ?entry |-
        context [@List.nth ?T ?index ?entries ?zero] =>
      let Hraw := fresh "Hraw" in assert (Hraw : @List.nth T index entries zero = entry) by exact Hrawentry;
      rewrite Hraw; clear Hraw end
    |progress rewrite Hentry |progress rewrite Htarget
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by congruence
      |progress rewrite (bool_decide_false P) by congruence] end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
      retrieve numberLocalGet numberLocalSet store break addInt modIntUnsigned
      execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
      Imperative.update decide decide_rel
      variableIndexEqualityDecidablevarsfuncdef_0__renameCacheGrow varsfuncdef_0__renameCacheGrow_rec]
    |match goal with |- context [Nat.lt_dec ?i ?n] => destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |match goal with |- context [numbers.Z.eq_dec ?a ?b] => destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |case_decide; [|lia]].
  all: try reflexivity. all: rewrite Nat2Z.inj_mod,Nat2Z.inj_succ; reflexivity.
Qed.
Definition parameters (initial final : Frame) :=
  nums final vardef_0__renameCacheGrow_oldSize = nums initial vardef_0__renameCacheGrow_oldSize /\
  nums final vardef_0__renameCacheGrow_size = nums initial vardef_0__renameCacheGrow_size.
Lemma advance_parameters f size slot : parameters f (advance f size slot).
Proof. destruct f. split; reflexivity. Qed.
Lemma parameters_trans f g h : parameters f g -> parameters g h -> parameters f h.
Proof. unfold parameters. intros [H1 H2] [H1' H2']. split; congruence. Qed.
Theorem generated_scan fuel (f : Frame) total outer_remaining size slot source e :
  total - Z.of_nat outer_remaining - 1 = Z.of_nat source ->
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  (source < length (memory (machine f) arraydef_0__renameMemo))%nat ->
  nums f vardef_0__renameCacheGrow_slot = Z.of_nat slot -> nums f vardef_0__renameCacheGrow_size = Z.of_nat size ->
  nums f vardef_0__renameCacheGrow_placed = 0 -> RenameMemoLookup.table (machine f) source = e ->
  exists final, execLocal (loop fuel (probe_body total outer_remaining)) f = Some (tt,final) /\ parameters f final /\
    nums final vardef_0__renameCacheGrow_placed =
      match RenameMemoVacant.vacant (scratch (machine f)) size slot fuel with Some _=>1 |None=>0 end /\
    machine final = match RenameMemoVacant.vacant (scratch (machine f)) size slot fuel with
      |Some index=>write_scratch (machine f) index (normalize e) |None=>machine f end.
Proof.
  induction fuel as [|fuel IH] in f,slot|-*.
  - intros Hsource Hpositive Hword Hslot Hscratch Hmemo Hindex Hsize Hplaced Hentry.
    exists f. split; [reflexivity|]. split; [split; reflexivity|]. split; [exact Hplaced|reflexivity].
  - intros Hsource Hpositive Hword Hslot Hscratch Hmemo Hindex Hsize Hplaced Hentry.
    rewrite loop_S,execLocal_bind.
    rewrite (generated_probe f total outer_remaining fuel size slot source e (scratch (machine f) slot)
      Hsource Hpositive Hword Hslot Hscratch Hmemo Hindex Hsize Hentry eq_refl).
    cbn [RenameMemoVacant.vacant]. destruct (bool_decide (RenameMemoTable.occupied (scratch (machine f) slot) = 0)).
    + exists (placed f slot e). split; [reflexivity|]. split; [split; reflexivity|]. split; reflexivity.
    + cbn [optionBind fst snd].
      destruct (IH (advance f size slot) (RenameMemoTable.next size slot) Hsource Hpositive Hword
        (RenameMemoTable.next_bound size slot Hpositive) Hscratch Hmemo eq_refl ltac:(exact Hsize) ltac:(exact Hplaced) Hentry)
        as [final [Hrun [Hparameters [Hflag Hmachine]]]].
      exists final. split; [exact Hrun|]. split; [|split; assumption].
      eapply parameters_trans; [apply advance_parameters|exact Hparameters].
Qed.
Lemma scan_no_flush fuel total outer_remaining : InternalObservation.local_nf (loop fuel (probe_body total outer_remaining)).
Proof. apply InternalObservation.loop_nf. intro remaining. unfold probe_body,rebuild_body,rebuilding. InternalObservation.nf. Qed.
Theorem generated_scan_observed fuel (f : Frame) total outer_remaining size slot source e observations :
  total - Z.of_nat outer_remaining - 1 = Z.of_nat source ->
  (0 < size)%nat -> Z.of_nat size <= maximum -> (slot < size)%nat ->
  (size <= length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  (source < length (memory (machine f) arraydef_0__renameMemo))%nat ->
  nums f vardef_0__renameCacheGrow_slot = Z.of_nat slot -> nums f vardef_0__renameCacheGrow_size = Z.of_nat size ->
  nums f vardef_0__renameCacheGrow_placed = 0 -> RenameMemoLookup.table (machine f) source = e ->
  exists final, execLocalObserved (loop fuel (probe_body total outer_remaining)) (f,observations) = Some (tt,(final,observations)) /\ parameters f final /\
    nums final vardef_0__renameCacheGrow_placed =
      match RenameMemoVacant.vacant (scratch (machine f)) size slot fuel with Some _=>1 |None=>0 end /\
    machine final = match RenameMemoVacant.vacant (scratch (machine f)) size slot fuel with
      |Some index=>write_scratch (machine f) index (normalize e) |None=>machine f end.
Proof.
  intros Hsource Hpositive Hword Hslot Hscratch Hmemo Hindex Hsize Hplaced Hentry.
  destruct (generated_scan fuel f total outer_remaining size slot source e Hsource Hpositive Hword Hslot Hscratch Hmemo Hindex Hsize Hplaced Hentry)
    as [final [Hrun Hresult]]. exists final. split; [|exact Hresult].
  exact (LocalObservation.plain_observed _ f observations tt final (scan_no_flush fuel total outer_remaining) Hrun).
Qed.
End RenameMemoProbe.
