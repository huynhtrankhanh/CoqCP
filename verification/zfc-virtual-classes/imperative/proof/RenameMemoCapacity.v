From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoTable RenameMemoPlacement.
From Stdlib Require Import Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers.
Module RenameMemoCapacity.
Import RenameMemoTable RenameMemoPlacement.
Open Scope nat_scope.
Definition position size start distance := (start + distance) mod size.
Lemma position_zero size start : start < size -> position size start 0 = start.
Proof. intros Hstart. unfold position. rewrite Nat.add_0_r. now apply Nat.mod_small. Qed.
Lemma position_next size start distance :
  position size (next size start) distance = position size start (S distance).
Proof. unfold position,next. rewrite Nat.Div0.add_mod_idemp_l. f_equal. lia. Qed.
Theorem position_covers size start target : start < size -> target < size ->
  exists distance, distance < size /\ position size start distance = target.
Proof.
  intros Hstart Htarget. destruct (Nat.le_dec start target) as [Hbefore|Hafter].
  - exists (target-start). split; [lia|]. unfold position. replace (start+(target-start)) with target by lia. now apply Nat.mod_small.
  - exists (size-start+target). split; [lia|]. unfold position.
    replace (start+(size-start+target)) with (target + 1 * size) by lia.
    rewrite Nat.Div0.mod_add. now apply Nat.mod_small.
Qed.
Theorem exhausted_occupied table size k start fuel : start < size ->
  place table size k start fuel = None ->
  forall distance, distance < fuel -> occupied (table (position size start distance)) <> 0%Z.
Proof.
  induction fuel as [|fuel IH] in start |- *; [intros; lia|].
  intros Hstart Hnone distance Hdistance. cbn [place] in Hnone.
  destruct (bool_decide (occupied (table start) = 0%Z)) eqn:Hempty; [discriminate|].
  destruct (bool_decide (matches (table start) k)) eqn:Hmatch; [discriminate|].
  destruct distance as [|distance].
  - rewrite position_zero by exact Hstart. now apply bool_decide_eq_false in Hempty.
  - rewrite <-position_next. apply IH; [apply next_bound; lia|exact Hnone|lia].
Qed.
Theorem empty_place table size k start target : start < size -> target < size -> occupied (table target) = 0%Z ->
  exists slot, place table size k start size = Some slot.
Proof.
  intros Hstart Htarget Hempty. destruct (place table size k start size) as [slot|] eqn:Hplace; [eauto|].
  destruct (position_covers size start target Hstart Htarget) as [distance [Hdistance Hposition]].
  pose proof (exhausted_occupied table size k start size Hstart Hplace distance Hdistance) as Hoccupied. rewrite Hposition,Hempty in Hoccupied. contradiction.
Qed.
Fixpoint live (table : nat -> entry) size := match size with
  | O => 0 | S rest => live table rest + if bool_decide (occupied (table rest) = 0%Z) then 0 else 1 end.
Lemma live_bound table size : live table size <= size.
Proof. induction size; [reflexivity|]. cbn [live]. destruct bool_decide; lia. Qed.
Lemma live_ext table other size : (forall index, index < size -> table index = other index) -> live table size = live other size.
Proof.
  induction size as [|size IH]; [reflexivity|]. intros Htable. cbn [live].
  rewrite Htable by lia. rewrite IH; [reflexivity|]. intros; apply Htable; lia.
Qed.
Theorem live_empty table size : live table size < size -> exists index, index < size /\ occupied (table index) = 0%Z.
Proof.
  induction size as [|size IH]; [cbn; lia|]. cbn [live].
  destruct (bool_decide (occupied (table size) = 0%Z)) eqn:Hempty.
  - intros Hlive. exists size. split; [lia|]. now apply bool_decide_eq_true in Hempty.
  - intros Hlive. destruct (IH ltac:(lia)) as [index [Hindex Hoccupied]]. exists index. split; [lia|exact Hoccupied].
Qed.
Theorem room_place table size k start : start < size -> live table size < size ->
  exists slot, place table size k start size = Some slot.
Proof. intros Hstart Hlive. destruct (live_empty table size Hlive) as [target [Htarget Hempty]]. now apply empty_place with (target:=target). Qed.
Theorem live_put table size slot k result : slot < size ->
  live (put table slot (fst k,snd k,result,1%Z)) size =
    live table size + if bool_decide (occupied (table slot) = 0%Z) then 1 else 0.
Proof.
  induction size as [|size IH] in slot |- *; [lia|]. intros Hslot.
  destruct (Nat.eq_dec slot size) as [->|Hdifferent].
  - cbn [live].
    assert (Hprefix : live (put table size (fst k,snd k,result,1%Z)) size = live table size).
    { apply live_ext. intros index Hindex. unfold put. destruct Nat.eq_dec; [lia|reflexivity]. }
    rewrite Hprefix.
    assert (Hentry : put table size (fst k,snd k,result,1%Z) size = (fst k,snd k,result,1%Z)).
    { unfold put. destruct Nat.eq_dec; [reflexivity|contradiction]. }
    rewrite Hentry.
    cbn [occupied snd]. rewrite bool_decide_false by discriminate.
    destruct (bool_decide (occupied (table size) = 0%Z)); lia.
  - cbn [live]. rewrite IH by lia.
    assert (Hentry : put table slot (fst k,snd k,result,1%Z) size = table size).
    { unfold put. destruct Nat.eq_dec; congruence. }
    rewrite Hentry. lia.
Qed.
End RenameMemoCapacity.
