From stdpp Require Import options numbers list.
From CoqCP Require Import Options ListRange Foldl Comparator SelectionSort.

Lemma pickSmallestInRangeFold {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i delta : nat) : foldl (fun accumulated current => if compare (nth current l default) (nth accumulated l default) then current else accumulated) i (range2 i (i + delta)) = pickSmallestInRange default compare i (i + delta) l.
Proof. easy. Qed.

Lemma pickSmallestInRangeInvariant {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i delta : nat) : i <= foldl (fun accumulated current => if compare (nth current l default) (nth accumulated l default) then current else accumulated) i (range2 i (i + delta)).
Proof.
  induction delta as [| delta IH].
  - rewrite Nat.add_0_r, range2LeftLeft. simpl. destruct (compare _); easy.
  - rewrite Nat.add_succ_r, range2LeftAdd, foldl_app, foldlSingleton. destruct (compare (nth (S (i + delta)) l default)).
    + lia.
    + assumption.
Qed.

Lemma iLessEqualPickSmallestInRange {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i delta : nat) : i <= pickSmallestInRange default compare i (i + delta) l.
Proof.
  unfold pickSmallestInRange. apply pickSmallestInRangeInvariant.
Qed.

Lemma pickSmallestInRangeLtIffNeq {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i delta : nat) : i < pickSmallestInRange default compare i (i + delta) l <-> i <> pickSmallestInRange default compare i (i + delta) l.
Proof.
  split; pose proof iLessEqualPickSmallestInRange default compare l i delta; intros; lia.
Qed.

Lemma pickSmallestInRangeSuccDelta {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i delta : nat) : pickSmallestInRange default compare i (i + S delta) l = pickSmallestInRange default compare i (i + delta) l \/ pickSmallestInRange default compare i (i + S delta) l = i + S delta.
Proof.
  remember (compare (nth (i + S delta) l default) (nth (pickSmallestInRange default compare i (i + delta) l) l default)) as H eqn:HeqH.
  destruct H.
  - right. unfold pickSmallestInRange. rewrite Nat.add_succ_r, range2LeftAdd, foldl_app, foldlSingleton. unfold pickSmallestInRange in HeqH. rewrite Nat.add_succ_r in HeqH. rewrite <- HeqH. reflexivity.
  - left. unfold pickSmallestInRange. rewrite Nat.add_succ_r, range2LeftAdd, foldl_app, foldlSingleton. unfold pickSmallestInRange in HeqH. rewrite Nat.add_succ_r in HeqH. rewrite <- HeqH. reflexivity.
Qed.

Lemma pickSmallestInRangeUpperBound {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i delta : nat) : pickSmallestInRange default compare i (i + delta) l <= i + delta.
Proof.
  induction delta.
  - unfold pickSmallestInRange. rewrite Nat.add_0_r, range2LeftLeft, foldlSingleton. destruct (compare _); easy.
  - rewrite Nat.add_succ_r. unfold pickSmallestInRange. rewrite range2LeftAdd, foldl_app, ?foldlSingleton. destruct (compare _); rewrite ?pickSmallestInRangeFold; lia.
Qed.

Lemma pickSmallestInRangeCompare {A : Type} (default : A) (comparator : Comparator A) (l : list A) (i delta inBetween : nat) (hInBetween : inBetween <= delta) : ~compare _ comparator (nth (i + inBetween) l default) (nth (pickSmallestInRange default (compare _ comparator) i (i + delta) l) l default).
Proof.
  revert inBetween hInBetween. induction delta as [| delta IHdelta]; intros inBetween hInBetween.
  - unfold pickSmallestInRange. rewrite Nat.add_0_r, range2LeftLeft, foldlSingleton. pose proof irreflexive _ comparator (nth i l default) as H. rewrite Is_true_false in H. rewrite H. rewrite Is_true_false. assert (H' : i + inBetween = i). { lia. } rewrite H'. assumption.
  - rewrite Nat.add_succ_r. unfold pickSmallestInRange in *. rewrite range2LeftAdd, foldl_app, ?foldlSingleton, pickSmallestInRangeFold. rewrite pickSmallestInRangeFold in IHdelta.
    remember (compare A comparator (nth (S (i + delta)) l default) (nth (pickSmallestInRange default (compare A comparator) i (i + delta) l) l default)) as H eqn:HeqH. destruct H.
    + assert (hSplit : inBetween = S delta \/ inBetween <= delta). { lia. }
      destruct hSplit as [H | H].
      * rewrite H, Nat.add_succ_r. apply (irreflexive _ comparator).
      * pose proof IHdelta inBetween H as H0. symmetry in HeqH. rewrite <- Is_true_true in HeqH. pose proof asymmetry _ _ _ _ HeqH as H1. apply (negativelyTransitive _ _ _ _ H0 H1).
    + assert (hSplit : inBetween = S delta \/ inBetween <= delta). { lia. }
      destruct hSplit as [H | H].
      * rewrite H, Nat.add_succ_r. symmetry in HeqH. rewrite <- Is_true_false in HeqH. tauto.
      * symmetry in HeqH. rewrite <- Is_true_false in HeqH. pose proof IHdelta inBetween H as H'. exact H'.
Qed.
