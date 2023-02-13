From stdpp Require Import options numbers list.
From CoqCP Require Import Options SelectionSort Comparator ListDecomposition Sorted SelectionSortProperties SwapUpdate PickSmallestInRangeProperties.

Lemma propertyPreservedAfterSwapping {A : Type} (default : A) (comparator : Comparator A) (l : list A) (property : list A -> Prop) (hPreserve : forall l1 l2 l3 a1 a2, compare _ comparator a2 a1 -> property (l1 ++ [a1] ++ l2 ++ [a2] ++ l3) -> property (l1 ++ [a2] ++ l2 ++ [a1] ++ l3)) (hProperty : property l) (i : nat) (hInBounds : i < length l) : property (swap l i (pickSmallestInRange default (compare _ comparator) i (length l - 1) l) default).
Proof.
  pose proof pickSmallestInRangeCompare default comparator l i (length l - 1 - i) 0 ltac:(lia) as H.
  assert (H1 : i + (length l - 1 - i) = length l - 1). { lia. }
  rewrite H1, Nat.add_0_r in H.
  remember (pickSmallestInRange default (compare A comparator) i (length l - 1) l) as j eqn:Heqj.
  pose proof pickSmallestInRangeUpperBound default (compare A comparator) l i (length l - 1 - i) as upperBound.
  rewrite H1, <- Heqj in upperBound.
  pose proof pickSmallestInRangeInvariant default (compare A comparator) l i (length l - 1 - i) as hLeq.
  rewrite pickSmallestInRangeFold, H1, <- Heqj in hLeq.
  assert (hSplit : i = j \/ i < j). { lia. }
  destruct hSplit as [H0 | H0].
  - rewrite H0, swapSelf. assumption.
  - pose proof proj1 (lessThanOrEqual comparator (nth i l default) (nth j l default)) H as H2. destruct H2 as [H2 | H2].
    + unfold swap. rewrite <- H2, updateSelf, H2, updateSelf. assumption.
    + rewrite (listDecomposition l i j ltac:(lia) ltac:(lia) default).
      assert (takeLength : i = length (take i l)). { rewrite take_length. lia. }
      assert (hRewrite : swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) i j default = swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) j default). { rewrite <- ?takeLength. easy. }
      rewrite hRewrite. clear hRewrite takeLength.
      assert (takeLength : j = length (take i l) + length (drop (S i) (take j l)) + 1).
      { rewrite take_length, drop_length, take_length.
        assert (subtask1 : i `min` length l = i). { lia. }
        assert (subtask2 : j `min` length l = j). { lia. }
        rewrite subtask1, subtask2. lia. }
      assert (hRewrite : property (swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) j default) = property (swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) (length (take i l) + length (drop (S i) (take j l)) + 1) default)). { rewrite <- ?takeLength. easy. }
      rewrite hRewrite, swapApp. clear hRewrite takeLength. apply hPreserve.
      * assumption.
      * rewrite <- (listDecomposition l i j ltac:(lia) ltac:(lia) default). assumption.
Qed.

Lemma propertyPreservedAfterPartialSorting {A : Type} (default : A) (comparator : Comparator A) (l : list A) (property : list A -> Prop) (hPreserve : forall l1 l2 l3 a1 a2, compare _ comparator a2 a1 -> property (l1 ++ [a1] ++ l2 ++ [a2] ++ l3) -> property (l1 ++ [a2] ++ l2 ++ [a1] ++ l3)) (hProperty : property l) (iterationCount : nat) (hIterationCount : iterationCount <= length l) : property (partialSelectionSort default (compare _ comparator) l iterationCount).
Proof.
  induction iterationCount as [| iterationCount IHiterationCount].
  - easy.
  - rewrite partialSelectionSortSucc.
    assert (hPosition : iterationCount <= pickSmallestInRange default (compare A comparator) iterationCount (length l - 1)
    (partialSelectionSort default (compare A comparator) l iterationCount)).
    { unfold pickSmallestInRange.
      assert (h : iterationCount + (length l - 1 - iterationCount) = length l - 1). { lia. }
      rewrite <- h. apply pickSmallestInRangeInvariant. }
    assert (hPosition2 : iterationCount = pickSmallestInRange default (compare A comparator) iterationCount (length l - 1)
    (partialSelectionSort default (compare A comparator) l iterationCount) \/ iterationCount < pickSmallestInRange default (compare A comparator) iterationCount (length l - 1)
    (partialSelectionSort default (compare A comparator) l iterationCount)). { lia. }
    destruct hPosition2 as [H | H].
    + rewrite <- H, swapSelf. pose proof IHiterationCount ltac:(lia). assumption.
    + pose proof IHiterationCount ltac:(lia) as hNext.
      rewrite <- (partialSelectionSortPreservesLength default (compare _ comparator) l iterationCount).
      apply propertyPreservedAfterSwapping.
      * tauto.
      * tauto.
      * pose proof pickSmallestInRangeUpperBound default (compare _ comparator) l iterationCount (length l - 1 - iterationCount) as H0.
        assert (H1 : iterationCount + (length l - 1 - iterationCount) = length l - 1).
        { lia. }
        rewrite H1 in H0.
        rewrite (partialSelectionSortPreservesLength default (compare _ comparator) l iterationCount).
        lia.
Qed.

Lemma propertyPreservedAfterSorting {A : Type} (default : A) (comparator : Comparator A) (l : list A) (property : list A -> Prop) (hPreserve : forall l1 l2 l3 a1 a2, compare _ comparator a2 a1 -> property (l1 ++ [a1] ++ l2 ++ [a2] ++ l3) -> property (l1 ++ [a2] ++ l2 ++ [a1] ++ l3)) (hProperty : property l) : property (selectionSort default (compare _ comparator) l).
Proof.
  rewrite <- selectionSortComplete. apply propertyPreservedAfterPartialSorting; try tauto; try lia.
Qed.
