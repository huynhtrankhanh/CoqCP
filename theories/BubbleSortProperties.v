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

Lemma bubbleSortAuxPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) : length l = length (bubbleSortAux default compare iterationCount l).
Proof.
  induction iterationCount as [| n IH] in l |- *; try easy.
  simpl. now rewrite <- IH, bubbleSortPassPreservesLength.
Qed.

Lemma compareAndSwapPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i : nat) : length (compareAndSwap default compare l i) = length l.
Proof.
  unfold compareAndSwap.
  remember (compare _ _) as x.
  destruct x; now rewrite ?swapPreservesLength.
Qed.

Lemma bubbleSortPassPartialPreservesLength {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) : length (bubbleSortPassPartial default compare l iterationCount) = length l.
Proof.
  induction iterationCount as [| n IH].
  - easy.
  - unfold bubbleSortPassPartial in *. now rewrite seq_S, Nat.add_0_l, foldl_app, foldlSingleton, compareAndSwapPreservesLength. 
Qed.

Lemma bubblingUp {A : Type} (default : A) (comparator : Comparator A) (l : list A) (iterationCount : nat) (i : nat) (hI : i <= iterationCount) (hCap : iterationCount < length l) : ~compare _ comparator (nth iterationCount (bubbleSortPassPartial default (compare _ comparator) l iterationCount) default) (nth i (bubbleSortPassPartial default (compare _ comparator) l iterationCount) default).
Proof.
  induction iterationCount as [| n IH].
  - rewrite (ltac:(lia) : i = 0). apply irreflexive.
  - unfold bubbleSortPassPartial in *. rewrite seq_S, Nat.add_0_l, foldl_app, foldlSingleton.
    rewrite (ltac:(easy) : foldl _ _ _ = bubbleSortPassPartial _ _ _ _) in *.
    destruct (decide (i = S n)).
    + subst i. apply irreflexive.
    + pose proof IH ltac:(lia) as step.
      unfold compareAndSwap.
      remember (compare _ _ (nth (n + 1) _ _) _) as x eqn:hX.
      symmetry in hX. destruct x; rewrite <- ?Is_true_true, <- ?Is_true_false in *.
      { pose proof nthSwapVariant (bubbleSortPassPartial default (compare A comparator) l n) default (S n) n as partial.
        rewrite bubbleSortPassPartialPreservesLength in *.
        pose proof (partial ltac:(lia) ltac:(lia)) as close.
        rewrite ?(ltac:(lia) : S n = n + 1) in *. rewrite close.
        clear partial close.
        destruct (decide (i = n)).
        { subst i.
          pose proof nthSwap (bubbleSortPassPartial default (compare A comparator) l n) default n (n + 1) as partial.
          rewrite bubbleSortPassPartialPreservesLength in *.
          rewrite (partial ltac:(lia) ltac:(lia)).
          now apply asymmetry. }
        { pose proof nthSwapExcept (bubbleSortPassPartial default (compare A comparator) l n) default n (n + 1) i as partial.
          rewrite bubbleSortPassPartialPreservesLength in *.
          rewrite (partial ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). apply step. lia. } }
      { pose proof step ltac:(lia) as close.
        rewrite (ltac:(lia) : S n = n + 1) in *.
        exact (negativelyTransitive _ _ _ _ hX close). }
Qed.

Lemma moveBubbleSortPassOut {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount : nat) : bubbleSortAux default compare iterationCount (bubbleSortPass default compare l) = bubbleSortPass default compare (bubbleSortAux default compare iterationCount l).
Proof.
  induction iterationCount as [| n IH] in l |- *; try easy.
  simpl. now rewrite IH.
Qed.

Lemma nthCompareAndSwapExcept {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i j : nat) (hDiff1 : j <> i) (hDiff2 : j <> i + 1) (hLt : S i < length l) : nth j (compareAndSwap default compare l i) default = nth j l default.
Proof.
  unfold compareAndSwap.
  remember (compare _ _) as x.
  destruct x; try easy.
  rewrite nthSwapExcept; (done || lia).
Qed.

Lemma nthBubbleSortPassPartial {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (iterationCount i : nat) (h : S i < iterationCount) (hLt : S iterationCount < length l) : nth i (bubbleSortPassPartial default compare l iterationCount) default = nth i (bubbleSortPass default compare l) default.
Proof.
Admitted.

Lemma bubbleSortAuxInvariant {A : Type} (default : A) (comparator : Comparator A) (l : list A) (iterationCount : nat) (hIterationCount : iterationCount <= length l) : suffixSorted default (compare _ comparator) (bubbleSortAux default (compare _ comparator) iterationCount l) iterationCount /\ partitioned default (compare _ comparator) (bubbleSortAux default (compare _ comparator) iterationCount l) (length l - iterationCount).
Proof.
  induction iterationCount as [| iterationCount IHiterationCount] in l |- *.
  - split.
    + intros i j hIJ hI hJ. rewrite <- bubbleSortAuxPreservesLength in *. lia.
    + intros i j hI hJ hLength. rewrite <- bubbleSortAuxPreservesLength in *. lia.
  - pose proof IHiterationCount (bubbleSortPass default (compare A comparator) l) as [hS hP].
    split.
    + simpl in *.
      intros i j hIJ hI hJ. pose proof hS i j ltac:(lia) as partial.
      rewrite <- !bubbleSortAuxPreservesLength, !bubbleSortPassPreservesLength in *.
      destruct (decide (length l - iterationCount = i + 1)) as [hSplit | hSplit].
      * pose proof hP (length l - iterationCount - 1) j ltac:(lia) ltac:(lia) as partial2.
        rewrite <- !bubbleSortAuxPreservesLength, !bubbleSortPassPreservesLength in *.
        pose proof partial2 ltac:(lia) as close. rewrite (ltac:(lia) : length l - iterationCount - 1 = i) in close. easy.
      * exact (partial ltac:(lia) ltac:(lia)).
    + intros i j hI hJ hLength.
      rewrite <- ?bubbleSortAuxPreservesLength, ?bubbleSortPassPreservesLength in *.
      simpl.
      pose proof hP i j ltac:(lia) as partial.
      rewrite <- !bubbleSortAuxPreservesLength, !bubbleSortPassPreservesLength in *.
      destruct (decide (j = length l - S iterationCount)) as [hSplit | hSplit].
      * rewrite moveBubbleSortPassOut in *.
        clear partial.
        pose proof bubblingUp default comparator (bubbleSortAux default (compare A comparator) iterationCount l) j i ltac:(lia) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia).
      * exact (partial ltac:(lia) ltac:(lia)).
Admitted.

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
