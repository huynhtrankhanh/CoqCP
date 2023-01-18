From stdpp Require Import numbers list.

Fixpoint existsInRange (n : nat) (f : nat -> bool) :=
  match n with
  | 0 => false
  | S n => orb (f n) (existsInRange n f)
  end.

Lemma existsInRangeZero (f : nat -> bool) : existsInRange 0 f = false.
Proof. easy. Qed.

Lemma existsInRangeSucc (n : nat) (f : nat -> bool) : existsInRange (S n) f = orb (f n) (existsInRange n f).
Proof. easy. Qed.

Definition existsInRangeLogic (n : nat) (f : nat -> bool) := exists i, i < n /\ f i = true.

Lemma existsInRangeLogicZero (f : nat -> bool) : ~existsInRangeLogic 0 f.
Proof. unfold existsInRangeLogic. intro h. destruct h as [w h]. lia. Qed.

Lemma existsInRangeLogicSucc (n : nat) (f : nat -> bool) : existsInRangeLogic (S n) f <-> f n = true \/ existsInRangeLogic n f.
Proof.
  split.
  - intro h. unfold existsInRangeLogic in *. destruct h as [w h].
    assert (H : w = n \/ w < n). { lia. }
    destruct H.
    + rewrite <- H. intuition.
    + right. exists w. intuition.
  - intro h. unfold existsInRangeLogic in *. destruct h.
    + exists n. intuition.
    + destruct H as [w h]. exists w. intuition.
Qed.

Definition notExistsInRangeLogic (n : nat) (f : nat -> bool) := forall i, i < n -> ~f i.

Lemma notExistsInRangeLogicZero (f : nat -> bool) : notExistsInRangeLogic 0 f.
Proof. unfold notExistsInRangeLogic. intros i h. lia. Qed.

Lemma notExistsInRangeLogicSucc (n : nat) (f : nat -> bool) : notExistsInRangeLogic (S n) f <-> ~f n /\ notExistsInRangeLogic n f.
Proof.
  split.
  - intro h. unfold notExistsInRangeLogic in *. split.
    + apply (h n). lia.
    + intros i h1. apply (h i). lia.
  - intro h. unfold notExistsInRangeLogic in *. intros i h1.
    destruct h as [h2 h3].
    assert (H : i = n \/ i < n). { lia. }
    destruct H.
    + rewrite H. auto.
    + apply (h3 i). auto.
Qed.

Lemma existsInRangeMeaning (n : nat) (f : nat -> bool) : existsInRange n f <-> existsInRangeLogic n f.
Proof.
  induction n.
  - rewrite existsInRangeZero. split.
    + easy.
    + apply existsInRangeLogicZero.
  - rewrite existsInRangeLogicSucc, existsInRangeSucc. intuition.
    remember (f n) as h2.
    destruct h2.
    + left. easy.
    + right. tauto.
Qed.

Lemma notExistsInRangeMeaning (n : nat) (f : nat -> bool) : ~existsInRange n f <-> notExistsInRangeLogic n f.
Proof.
  induction n.
  - rewrite existsInRangeZero. split.
    + intro h. apply notExistsInRangeLogicZero.
    + intuition.
  - rewrite existsInRangeSucc, notExistsInRangeLogicSucc. intuition.
    remember (f n) as h.
    destruct h.
    + easy.
    + intuition.
Qed.
