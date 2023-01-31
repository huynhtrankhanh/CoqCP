From stdpp Require Import numbers list.
From CoqCP Require Import ListRange SwapUpdate SelectionSort Foldl Comparator PickSmallestInRangeProperties ListDecomposition.

Definition partialSelectionSort {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) := foldl (fun accumulated i => swap accumulated i (pickSmallestInRange default compare i (length l - 1) accumulated) default) l (range iterationCount).

Definition sorted {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) := forall i j, i < j -> j < length l -> ~compare (nth j l default) (nth i l default).

Definition prefixSorted {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (prefixLength : nat) := forall i j, i < j -> j < prefixLength -> ~compare (nth j l default) (nth i l default).

Definition partitioned {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (middle : nat) := forall toTheLeft toTheRight, toTheLeft <= middle -> toTheRight >= middle -> toTheRight < length l -> ~compare (nth toTheRight l default) (nth toTheLeft l default).

Lemma partialSelectionSortZero {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : partialSelectionSort default compare l 0 = l.
Proof.
  unfold partialSelectionSort. rewrite rangeZero. easy.
Qed.

Lemma partialSelectionSortSucc {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) : partialSelectionSort default compare l (S iterationCount) = swap (partialSelectionSort default compare l iterationCount) iterationCount (pickSmallestInRange default compare iterationCount (length l - 1) (partialSelectionSort default compare l iterationCount)) default.
Proof.
  unfold partialSelectionSort. rewrite rangeSucc, foldl_app. simpl. reflexivity.
Qed.

Lemma selectionSortComplete {A : Type} (default : A) (comparator : Comparator A) (l : list A) : partialSelectionSort default (compare A comparator) l (length l) = selectionSort default (compare A comparator) l.
Proof. easy. Qed.

Lemma selectionSortPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : length (selectionSort default compare l) = length l.
Proof.
  unfold selectionSort.
  remember (range _) as randomList.
  clear HeqrandomList. revert l.
  induction randomList; intros.
  - easy.
  - simpl. pose proof IHrandomList (swap l a (pickSmallestInRange default compare a (length l - 1) l) default) as H.
    rewrite ?swapPreservesLength in H. assumption.
Qed.

Lemma partialSelectionSortPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) : length (partialSelectionSort default compare l iterationCount) = length l.
Proof.
  unfold partialSelectionSort.
  remember (range _) as randomList.
  clear HeqrandomList. revert l.
  induction randomList; intros.
  - easy.
  - simpl. pose proof IHrandomList (swap l a (pickSmallestInRange default compare a (length l - 1) l) default) as H.
    rewrite ?swapPreservesLength in H. assumption.
Qed.

Lemma partialSelectionSortInvariant {A : Type} (default : A) (comparator : Comparator A) (l : list A) (i : nat) (hLt : i < length l) : prefixSorted default (compare _ comparator) (partialSelectionSort default (compare _ comparator) l (S i)) (S i) /\ partitioned default (compare _ comparator) (partialSelectionSort default (compare _ comparator) l (S i)) i.
Proof.
  induction i.
  - rewrite partialSelectionSortSucc, partialSelectionSortZero.
    split.
    + intros i j hIJ hJ. lia.
    + intros toTheLeft toTheRight hToTheLeft hToTheRight hLength.
      pose proof pickSmallestInRangeUpperBound default (compare A comparator) l 0 (length l - 1) as hUpperBound.
      rewrite Nat.add_0_l in hUpperBound.
      assert (hToTheLeftEq : toTheLeft = 0). { lia. }
      rewrite hToTheLeftEq. rewrite nthSwap; try lia.
      rewrite swapPreservesLength in hLength.
      pose proof pickSmallestInRangeCompare default comparator l 0 (length l - 1) toTheRight ltac:(lia) as H.
      rewrite Nat.add_0_l in H.
      assert (hCaseSplit : toTheRight = 0 \/ toTheRight <> 0). { lia. }
      destruct hCaseSplit as [hCaseSplit | hCaseSplit]; rewrite ?hCaseSplit; rewrite ?nthSwap; try lia; try apply irreflexive.
      assert (hCaseSplit' : toTheRight = pickSmallestInRange default (compare A comparator) 0 (length l - 1) l \/ toTheRight <> pickSmallestInRange default (compare A comparator) 0 (length l - 1) l). { lia. }
      destruct hCaseSplit' as [hCaseSplit' | hCaseSplit']; rewrite ?hCaseSplit', ?nthSwapVariant; try lia.
      * pose proof pickSmallestInRangeCompare default comparator l 0 (length l - 1) 0 ltac:(lia) as H0.
        rewrite ?Nat.add_0_l in H0. assumption.
      * rewrite nthSwapExcept; try lia. assumption.
  - rewrite partialSelectionSortSucc.
    remember (partialSelectionSort default (compare A comparator) l (S i)) as pastIteration.
    assert (hPastIterationSameLength : length pastIteration = length l).
    { rewrite HeqpastIteration, partialSelectionSortPreservesLength. reflexivity. }
    assert (hSimplify : S i + (length l - 1 - S i) = length l - 1). { lia. }
    pose proof pickSmallestInRangeUpperBound default (compare _ comparator) pastIteration (S i) (length l - 1 - S i) as hUpperBound.
    pose proof iLessEqualPickSmallestInRange default (compare _ comparator) pastIteration (S i) (length l - 1 - S i) as hLowerBound.
    rewrite hSimplify in *.
    split.
    + intros left right hLeftRight hRight.
      assert (hRightSuccI : right = S i \/ right < S i). { lia. }
      destruct hRightSuccI as [hRightSuccI | hRightSuccI].
      * rewrite hRightSuccI, nthSwap, nthSwapExcept; try lia.
        apply (proj2 (IHi ltac:(lia))); lia.
      * rewrite ?nthSwapExcept; try lia.
        exact (proj1 (IHi ltac:(lia)) left right ltac:(lia) ltac:(lia)).
    + intros left right hLeft hRight hRightLength.
      rewrite swapPreservesLength in hRightLength.
      assert (hLeftSplit : left = S i \/ left < S i). { lia. }
      destruct hLeftSplit as [hLeftSplit | hLeftSplit].
      * rewrite hLeftSplit, nthSwap; try lia.
        assert (hRightSplit : right = S i \/ right > S i). { lia. }
        destruct hRightSplit as [hRightSplit | hRightSplit].
        { rewrite hRightSplit, nthSwap; try lia; apply irreflexive. }
        { shelve. }
      * rewrite (nthSwapExcept _ _ _ _ left); try lia.
        assert (hRightSplit : right = S i \/ right > S i). { lia. }
        destruct hRightSplit as [hRightSplit | hRightSplit].
        { rewrite hRightSplit, nthSwap; try lia.
          apply (proj2 (IHi ltac:(lia))); lia. }
        { shelve. }
  Unshelve.
  { assert (hCaseSplit : right = pickSmallestInRange default (compare A comparator) (S i) (length l - 1) pastIteration \/ right <> pickSmallestInRange default (compare A comparator) (S i) (length l - 1) pastIteration). { lia. }
    destruct hCaseSplit as [hCaseSplit | hCaseSplit]; rewrite ?hCaseSplit.
    - rewrite nthSwapVariant; try lia.
      pose proof pickSmallestInRangeCompare default comparator pastIteration (S i) (length l - 1 - S i) 0 ltac:(lia) as H.
      rewrite hSimplify, Nat.add_0_r in H.
      assumption.
    - rewrite nthSwapExcept; try lia.
      pose proof pickSmallestInRangeCompare default comparator pastIteration (S i) (length l - 1 - S i) (right - S i) ltac:(lia) as H.
      assert (hSimplify' : S i + (right - S i) = right). { lia. }
      rewrite hSimplify, hSimplify' in H.
      assumption. }
  { assert (hCaseSplit : right = pickSmallestInRange default (compare A comparator) (S i) (length l - 1) pastIteration \/ right <> pickSmallestInRange default (compare A comparator) (S i) (length l - 1) pastIteration). { lia. }
    destruct hCaseSplit as [hCaseSplit | hCaseSplit]; rewrite ?hCaseSplit.
    - rewrite nthSwapVariant; try lia.
      apply (proj2 (IHi ltac:(lia))); lia.
    - rewrite nthSwapExcept; try lia.
      apply (proj2 (IHi ltac:(lia))); lia. }
Qed.

Lemma selectionSortCorrect {A : Type} (default : A) (comparator : Comparator A) (l : list A) : sorted default (compare _ comparator) (selectionSort default (compare _ comparator) l).
Proof.
  destruct l.
  - intros a b h1 h2. simpl in *. lia.
  - pose proof proj1 (partialSelectionSortInvariant default comparator (a :: l) (length l) ltac:(simpl; lia)).
    intros i j h1 h2.
    apply H.
    + assumption.
    + rewrite selectionSortPreservesLength in h2. simpl in h2. assumption.
Qed.

Lemma propertyPreservedAfterSwapping {A : Type} (default : A) (comparator : Comparator A) (l : list A) (property : list A -> Prop) (hPreserve : forall l1 l2 l3 a1 a2, compare _ comparator a2 a1 -> property (l1 ++ [a1] ++ l2 ++ [a2] ++ l3) -> property (l1 ++ [a2] ++ l2 ++ [a1] ++ l3)) (hProperty : property l) (i : nat) (hInBounds : i < length l) : property (swap l i (pickSmallestInRange default (compare _ comparator) i (length l - 1) l) default).
Proof.
  pose proof pickSmallestInRangeCompare default comparator l i (length l - 1 - i) 0 ltac:(lia) as H.
  assert (H1 : i + (length l - 1 - i) = length l - 1). { lia. }
  rewrite H1, Nat.add_0_r in H.
  remember (pickSmallestInRange default (compare A comparator) i (length l - 1) l) as j.
  pose proof pickSmallestInRangeUpperBound default (compare A comparator) l i (length l - 1 - i) as upperBound.
  rewrite H1, <- Heqj in upperBound.
  pose proof pickSmallestInRangeInvariant default (compare A comparator) l i (length l - 1 - i) as hLeq.
  rewrite pickSmallestInRangeFold, H1, <- Heqj in hLeq.
  assert (hSplit : i = j \/ i < j). { lia. }
  destruct hSplit.
  - rewrite H0, swapSelf. assumption.
  - pose proof proj1 (lessThanOrEqual comparator (nth i l default) (nth j l default)) H as H2. destruct H2.
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
  induction iterationCount.
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
    destruct hPosition2.
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
