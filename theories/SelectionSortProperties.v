From stdpp Require Import numbers list.
From CoqCP Require Import ListRange SwapUpdate SelectionSort Foldl Comparator PickSmallestInRangeProperties ListDecomposition Sorted ListsEqual.

Definition partialSelectionSort {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) := foldl (fun accumulated i => swap accumulated i (pickSmallestInRange default compare i (length l - 1) accumulated) default) l (range iterationCount).

Lemma partialSelectionSortZero {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : partialSelectionSort default compare l 0 = l.
Proof.
  unfold partialSelectionSort. rewrite rangeZero. easy.
Qed.

Lemma partialSelectionSortSucc {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) : partialSelectionSort default compare l (S iterationCount) = swap (partialSelectionSort default compare l iterationCount) iterationCount (pickSmallestInRange default compare iterationCount (length l - 1) (partialSelectionSort default compare l iterationCount)) default.
Proof.
  unfold partialSelectionSort. rewrite rangeSucc, foldl_app. simpl. reflexivity.
Qed.

Lemma selectionSortComplete {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : partialSelectionSort default compare l (length l) = selectionSort default compare l.
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

Lemma selectionSortPermutation {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : Permutation l (selectionSort default compare l).
Proof.
  rewrite <- selectionSortComplete.
  remember (length l) as iterationCount.
  assert (hIterationCount : iterationCount <= length l). { lia. }
  clear HeqiterationCount.
  induction iterationCount.
  - easy.
  - rewrite partialSelectionSortSucc.
    remember (partialSelectionSort default compare l iterationCount) as pastIteration.
    remember (pickSmallestInRange default compare iterationCount (length l - 1) pastIteration) as j.
    assert (hSimplify : iterationCount + (length l - 1 - iterationCount) = length l - 1). { lia. }
    assert (hJUpperBound : j <= length l - 1).
    { pose proof pickSmallestInRangeUpperBound default compare pastIteration iterationCount (length l - 1 - iterationCount) as H.
      rewrite hSimplify in *. lia. }
    assert (hJLowerBound : iterationCount = j \/ iterationCount < j).
    { pose proof iLessEqualPickSmallestInRange default compare pastIteration iterationCount (length l - 1 - iterationCount) as H.
      rewrite hSimplify in *. lia. }
    destruct hJLowerBound as [hJLowerBound | hJLowerBound].
    + rewrite hJLowerBound, swapSelf. apply IHiterationCount. lia.
    + assert (hLeq1 : iterationCount < length pastIteration). { rewrite HeqpastIteration, partialSelectionSortPreservesLength in *; lia. }
      assert (hLeq2 : j < length pastIteration). { rewrite HeqpastIteration, partialSelectionSortPreservesLength in *; lia. }
      rewrite swapDecomposition, IHiterationCount; try lia.
      assert (hPartial : Permutation pastIteration (take iterationCount pastIteration ++ [nth iterationCount pastIteration default] ++ drop (S iterationCount) (take j pastIteration) ++ [nth j pastIteration default] ++ drop (j + 1) pastIteration)).
      { epose proof (listDecomposition pastIteration iterationCount j ltac:(lia) ltac:(rewrite HeqpastIteration in *; assumption) default) as H.
        rewrite <- H. reflexivity. }
      transitivity (take iterationCount pastIteration ++ [nth iterationCount pastIteration default] ++ drop (S iterationCount) (take j pastIteration) ++ [nth j pastIteration default] ++ drop (j + 1) pastIteration); try assumption.
      remember (take iterationCount pastIteration) as A1.
      remember ([nth iterationCount pastIteration default]) as A2.
      remember (drop (S iterationCount) (take j pastIteration)) as A3.
      remember ([nth j pastIteration default]) as A4.
      remember (drop (j + 1) pastIteration) as A5.
      assert (hRewriteInner : Permutation (A2 ++ A3 ++ A4) (A4 ++ A3 ++ A2)).
      { rewrite (Permutation_app_comm A3 A2), (app_assoc A4 A2 A3), (Permutation_app_comm A4 A2), (Permutation_app_comm A3 A4), <- app_assoc. reflexivity. }
      assert (rebracket1 : A1 ++ A2 ++ A3 ++ A4 ++ A5 = A1 ++ (A2 ++ A3 ++ A4) ++ A5). { listsEqual. }
      assert (rebracket2 : A1 ++ A4 ++ A3 ++ A2 ++ A5 = A1 ++ (A4 ++ A3 ++ A2) ++ A5). { listsEqual. }
      rewrite rebracket1, rebracket2, hRewriteInner. reflexivity.
Qed.
