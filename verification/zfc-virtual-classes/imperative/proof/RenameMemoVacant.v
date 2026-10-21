From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoTable RenameMemoPlacement RenameMemoCapacity.
From Stdlib Require Import Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers.
Module RenameMemoVacant.
Import RenameMemoTable RenameMemoPlacement RenameMemoCapacity.
Fixpoint vacant (table : nat -> entry) size slot fuel : option nat := match fuel with
  |O=>None |S rest=>if bool_decide (occupied (table slot) = 0%Z) then Some slot else vacant table size (next size slot) rest end.
Theorem vacant_sound table size start fuel slot : (0 < size)%nat -> (start < size)%nat ->
  vacant table size start fuel = Some slot -> (slot < size)%nat /\ occupied (table slot) = 0%Z /\
  exists distance, (distance < fuel)%nat /\ accessible table size start slot distance.
Proof.
  induction fuel as [|fuel IH] in start|-*; [discriminate|]. intros Hsize Hstart. cbn [vacant].
  destruct (bool_decide (occupied (table start) = 0%Z)) eqn:Hempty.
  - intros Hslot. injection Hslot as <-. split; [exact Hstart|]. split; [now apply bool_decide_eq_true in Hempty|].
    exists 0%nat. split; [lia|constructor].
  - intros Hrun. destruct (IH (next size start) Hsize (next_bound size start Hsize) Hrun)
      as [Hslot [Hvacant [distance [Hdistance Hpath]]]].
    split; [exact Hslot|]. split; [exact Hvacant|]. exists (S distance). split; [lia|].
    constructor; [now apply bool_decide_eq_false in Hempty|exact Hpath].
Qed.
Lemma exhausted_occupied table size start fuel : (start < size)%nat -> vacant table size start fuel = None ->
  forall distance, (distance < fuel)%nat -> occupied (table (position size start distance)) <> 0%Z.
Proof.
  induction fuel as [|fuel IH] in start|-*; [intros; lia|]. intros Hstart Hnone distance Hdistance.
  cbn [vacant] in Hnone. destruct (bool_decide (occupied (table start) = 0%Z)) eqn:Hempty; [discriminate|].
  destruct distance as [|distance].
  - rewrite position_zero by exact Hstart. now apply bool_decide_eq_false in Hempty.
  - rewrite <-position_next. apply IH; [apply next_bound; lia|exact Hnone|lia].
Qed.
Theorem vacant_empty table size start target : (start < size)%nat -> (target < size)%nat ->
  occupied (table target) = 0%Z -> exists slot, vacant table size start size = Some slot.
Proof.
  intros Hstart Htarget Hempty. destruct (vacant table size start size) as [slot|] eqn:Hplace; [eauto|].
  destruct (position_covers size start target Hstart Htarget) as [distance [Hdistance Hposition]].
  pose proof (exhausted_occupied table size start size Hstart Hplace distance Hdistance) as Hoccupied.
  rewrite Hposition,Hempty in Hoccupied. contradiction.
Qed.
Theorem vacant_room table size start : (start < size)%nat -> (live table size < size)%nat ->
  exists slot, vacant table size start size = Some slot.
Proof. intros Hstart Hlive. destruct (live_empty table size Hlive) as [target [Htarget Hempty]]. now apply vacant_empty with (target:=target). Qed.
Theorem vacant_indexed table size hash k result start slot : (0 < size)%nat -> (start < size)%nat -> start = hash k ->
  indexed_by table size hash -> vacant table size start size = Some slot ->
  indexed_by (put table slot (fst k,snd k,result,1%Z)) size hash.
Proof.
  intros Hsize Hstart Hhash Hindexed Hvacant. destruct (vacant_sound table size start size slot Hsize Hstart Hvacant)
    as [Hslot [Hempty Hpath]]. apply put_indexed; try assumption. now rewrite <-Hhash.
Qed.
Theorem vacant_live table size start slot k result : (0 < size)%nat -> (start < size)%nat ->
  vacant table size start size = Some slot ->
  live (put table slot (fst k,snd k,result,1%Z)) size = S (live table size).
Proof.
  intros Hsize Hstart Hvacant. destruct (vacant_sound table size start size slot Hsize Hstart Hvacant) as [Hslot [Hempty Hpath]].
  rewrite live_put by exact Hslot. rewrite bool_decide_true by exact Hempty. lia.
Qed.
Theorem vacant_preserves_entry table size start slot k result old : (0 < size)%nat -> (start < size)%nat ->
  vacant table size start size = Some slot -> occupied (table old) <> 0%Z ->
  put table slot (fst k,snd k,result,1%Z) old = table old.
Proof.
  intros Hsize Hstart Hvacant Hoccupied. destruct (vacant_sound table size start size slot Hsize Hstart Hvacant) as [Hslot [Hempty Hpath]].
  unfold put. destruct Nat.eq_dec; [congruence|reflexivity].
Qed.
End RenameMemoVacant.
