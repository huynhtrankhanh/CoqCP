From stdpp Require Import numbers list.
From CoqCP Require Import Options ListRange SwapUpdate BubbleSort Foldl Comparator PickSmallestInRangeProperties ListDecomposition Sorted ListsEqual.

Lemma bubbleSortPassPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : length (bubbleSortPass default compare l) = length l.
Proof.
  unfold bubbleSortPass.
  remember (seq 0 (length l - 1)) as a eqn:h'.
  clear h'.
  induction a as [| head a IH] in l |- *.
  - easy.
  - simpl. rewrite !IH.
    unfold compareAndSwap.
    destruct (compare _ _); now pose proof swapPreservesLength l.
Qed.

Lemma bubbleSortPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : length (bubbleSort default compare l) = length l.
Proof.
  unfold bubbleSort.
  remember (length l) as n eqn:h.
  assert (h' : length (bubbleSortAux default compare n l) = length l).
  { clear h.
    induction n as [| n IH] in l |- *.
    - easy.
    - simpl. now rewrite !IH, bubbleSortPassPreservesLength. }
  congruence.
Qed.

Lemma bubbleSortAuxInvariant {A : Type} (default : A) (comparator : Comparator A) (l : list A) (i : nat) (hLt : i < length l) : prefixSorted default (compare _ comparator) (bubbleSortAux default (compare _ comparator) (S i) l) (S i) /\ partitioned default (compare _ comparator) (bubbleSortAux default (compare _ comparator) (S i) l) i.
Proof.
  induction i as [| i IH].
  - simpl. split.
    + intros i j hIJ hJ. lia.
    + intros toTheLeft toTheRight hToTheLeft hToTheRight hLength.
      assert (hToTheLeftEq : toTheLeft = 0). { lia. }
      subst toTheLeft.
      rewrite bubbleSortPassPreservesLength in *.
      destruct (decide (toTheRight = 0)) as [hCase | hCase].
      * subst toTheRight. destruct comparator. easy.
      * admit.
Admitted.

Lemma bubbleSortCorrect {A : Type} (default : A) (comparator : Comparator A) (l : list A) : sorted default (compare _ comparator) (bubbleSort default (compare _ comparator) l).
Proof.
  destruct l as [| a l].
  - intros a b h1 h2. simpl in *. lia.
  - pose proof proj1 (bubbleSortAuxInvariant default comparator (a :: l) (length l) ltac:(simpl; lia)) as H.
    intros i j h1 h2.
    apply H.
    + assumption.
    + rewrite bubbleSortPreservesLength in h2. simpl in h2. assumption.
Qed.

Lemma bubbleSortPermutation {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) : Permutation l (bubbleSort default compare l).
Proof.
  unfold bubbleSort.
  remember (length l) as iterationCount eqn:HeqiterationCount.
  assert (hIterationCount : iterationCount <= length l). { lia. }
  clear HeqiterationCount.
  induction iterationCount as [| iterationCount IHiterationCount] in l, hIterationCount |- *.
  - easy.
  - simpl.
    remember (bubbleSortAux default compare iterationCount l) as pastIteration eqn:HeqpastIteration.
    pose proof (IHiterationCount l ltac:(lia)) as step.
    unfold bubbleSortPass.
    assert (hCompareAndSwapLength : forall t (m : list A), length m = length (compareAndSwap default compare m t)).
    { intros m t. unfold compareAndSwap. destruct (compare _ _); try easy. now rewrite swapPreservesLength. }
    assert (hFoldl : forall k, length l = length (foldl (compareAndSwap default compare) l (seq 0 k))).
    { clear HeqpastIteration pastIteration.
      intro k.
      induction k as [| k hK]; try easy.
      rewrite seq_S, Nat.add_0_l, foldl_app. simpl. now rewrite <- hCompareAndSwapLength. }
    assert (hGoal : forall k, k < length l -> Permutation l (foldl (compareAndSwap default compare) l (seq 0 k))).
    { intros k h.
      clear hIterationCount IHiterationCount HeqpastIteration step iterationCount.
      induction k as [| k IH] in l, h, hFoldl |- *.
      - easy.
      - rewrite seq_S, Nat.add_0_l, foldl_app. simpl.
        pose proof IH l hFoldl ltac:(lia) as bridge.
        assert (hS : forall l : list A, k + 1 < length l -> Permutation l (compareAndSwap default compare l k)).
        { intros m hK.
          unfold compareAndSwap.
          destruct (compare (nth (k + 1) m default) (nth k m default)); try easy.
          exact (swapPermutation default m k (k + 1) ltac:(lia) ltac:(lia)). }
        pose proof hFoldl k.
        pose proof hS (foldl (compareAndSwap default compare) l (seq 0 k)) ltac:(lia) as final.
        now rewrite <- final. }
    destruct (decide (length l = 0)) as [hNil | hNil].
    + rewrite hNil. easy.
    + pose proof hGoal (length l - 1) ltac:(lia) as inch.
      pose proof IHiterationCount (foldl (compareAndSwap default compare) l (seq 0 (length l - 1))) ltac:(rewrite <- hFoldl; lia) as more.
      rewrite <- more. apply hGoal. lia.
Qed.
