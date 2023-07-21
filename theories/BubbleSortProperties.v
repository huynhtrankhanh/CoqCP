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

Lemma nthCompareAndSwapExcept {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i j : nat) (hDiff1 : j <> i) (hDiff2 : j <> i + 1) (hLt : S i < length l) : nth j (compareAndSwap default compare l i) default = nth j l default.
Proof.
  unfold compareAndSwap.
  remember (compare _ _) as x.
  destruct x; try easy.
  rewrite nthSwapExcept; (done || lia).
Qed.

Lemma nthBubbleSortPassPartial {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i j : nat) (hIJRelaxed : S i <= j) (hJ : j < length l) : nth i (bubbleSortPassPartial default compare l (S i)) default = nth i (bubbleSortPassPartial default compare l j) default.
Proof.
  destruct (decide (S i = j)); try now subst j.
  pose proof (ltac:(lia) : S i < j) as hIJ.
  induction j as [| j IH] in l, i, hIJ, hJ |- *.
  - pose proof (ltac:(lia) : i = 0). now subst i.
  - unfold bubbleSortPassPartial. rewrite (seq_S j 0), foldl_app, Nat.add_0_l, foldlSingleton, !(ltac:(easy) : foldl _ _ _ = bubbleSortPassPartial _ _ _ _), nthCompareAndSwapExcept; try (done || lia). 
    + destruct (decide (j = S i)); try now subst j. rewrite IH; (done || lia).
    + rewrite bubbleSortPassPartialPreservesLength; lia.
Qed.

Lemma nthBubbleSortPassPartial2 {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (i j : nat) (hIJ : i < j) (hJ : j < length l) : nth j (bubbleSortPassPartial default compare l i) default = nth j l default.
Proof.
  induction i as [| i IH] in l, j, hIJ, hJ |- *; try easy.
  unfold bubbleSortPassPartial. rewrite seq_S, foldl_app, foldlSingleton, Nat.add_0_l. rewrite (ltac:(easy) : foldl _ _ _ = bubbleSortPassPartial _ _ _ _) in *.
  rewrite nthCompareAndSwapExcept; try (rewrite ?bubbleSortPassPartialPreservesLength; lia). apply IH; lia.
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

Lemma nthBubbleSortPassJSucc {A : Type} (default : A) (comparator : Comparator A) (l : list A) (j : nat) (h : S j < length l) : ~(compare _ comparator) (nth j (bubbleSortPassPartial default (compare _ comparator) l j) default) (nth j (bubbleSortPassPartial default (compare _ comparator) l (S j)) default).
Proof.
  unfold bubbleSortPassPartial. rewrite seq_S, foldl_app, foldlSingleton, Nat.add_0_l.
  remember (foldl (compareAndSwap default _) l (seq 0 j)) as m eqn:hM.
  rewrite (ltac:(easy) : foldl _ _ _ = bubbleSortPassPartial _ _ _ _) in *.
  pose proof bubbleSortPassPartialPreservesLength default (compare _ comparator) l j as hPreserve.
  rewrite <- hM in hPreserve.
  unfold compareAndSwap.
  destruct (decide (compare _ comparator (nth (j + 1) m default) (nth j m default))) as [hSplit | hSplit].
  - rewrite Is_true_true in hSplit. rewrite hSplit, nthSwap; try lia. apply asymmetry. now rewrite <- Is_true_true in *.
  - rewrite Is_true_false in hSplit. rewrite hSplit. apply irreflexive.
Qed.

Lemma compareAndSwapPreservesPartitioned {A : Type} (default : A) (comparator : Comparator A) (l : list A) (partitionPoint i : nat) (hPartitioned : partitioned default (compare A comparator) l partitionPoint) (hPartitionPoint : partitionPoint < length l) (hI : S i < length l) : partitioned default (compare A comparator) (compareAndSwap default (compare A comparator) l i) partitionPoint.
Proof.
  intros left right hLeft hRight hCap.
  destruct (decide (left = right)) as [hEq | hEq].
  { subst left. apply irreflexive. }
  destruct (decide (left = i)) as [hLeftI | hLeftI].
  { pose proof (ltac:(lia) : right = i + 1 \/ right > i + 1) as [h1 | h1].
    - subst left right. unfold compareAndSwap.
      remember (compare _ _ (nth (i + 1) l default) _) as expr eqn:hExpr.
      symmetry in hExpr. destruct expr; rewrite <- ?Is_true_true, <- ?Is_true_false in *; try easy.
      rewrite !nthSwap, !nthSwapVariant; now (lia || apply asymmetry).
    - subst left. unfold compareAndSwap.
      remember (compare _ _ (nth (i + 1) l default) _) as expr eqn:hExpr.
      symmetry in hExpr. destruct expr; rewrite <- ?Is_true_true, <- ?Is_true_false in *.
      + rewrite nthSwap; try lia. rewrite nthSwapExcept; try lia.
        rewrite compareAndSwapPreservesLength in *.
        pose proof hPartitioned i right ltac:(lia) ltac:(lia) ltac:(lia) as step.
        exact (negativelyTransitive _ _ _ _ step (asymmetry _ _ _ _ hExpr)).
      + rewrite compareAndSwapPreservesLength in *.
        exact (hPartitioned i right ltac:(lia) ltac:(lia) ltac:(lia)). }
  destruct (decide (left = i + 1)) as [hLeftSI | hLeftSI].
  { subst left. unfold compareAndSwap.
    remember (compare _ _ (nth (i + 1) l default) _) as expr eqn:hExpr.
    symmetry in hExpr. destruct expr; rewrite <- ?Is_true_true, <- ?Is_true_false in *.
    - rewrite !nthSwapVariant, !nthSwapExcept; try lia.
      rewrite compareAndSwapPreservesLength in *.
      exact (hPartitioned i right ltac:(lia) ltac:(lia) ltac:(lia)).
    - rewrite compareAndSwapPreservesLength in *.
      now pose proof hPartitioned (i + 1) right ltac:(lia) ltac:(lia) ltac:(lia) as step. }
Admitted.

Lemma bubbleSortPassPartialPreservesPartition {A : Type} (default : A) (comparator : Comparator A) (l : list A) (partitionPoint i : nat) (hPartitioned : partitioned default (compare A comparator) l partitionPoint) (hPartitionPoint : partitionPoint < length l) (hI : S i < length l) : partitioned default (compare A comparator) (bubbleSortPassPartial default (compare A comparator) l i) partitionPoint.
Proof.
  induction i as [| i IH].
  - easy.
  - pose proof IH ltac:(lia) as past.
    unfold bubbleSortPassPartial. rewrite seq_S, foldl_app, Nat.add_0_l, foldlSingleton, (ltac:(easy) : foldl _ _ _ = bubbleSortPassPartial _ _ _ _).
    apply compareAndSwapPreservesPartitioned; rewrite ?bubbleSortPassPartialPreservesLength; (done || lia).
Qed.

Lemma bubbleSortAuxInvariant {A : Type} (default : A) (comparator : Comparator A) (l : list A) (iterationCount : nat) (hIterationCount : iterationCount <= length l) : suffixSorted default (compare _ comparator) (bubbleSortAux default (compare _ comparator) iterationCount l) iterationCount /\ partitioned default (compare _ comparator) (bubbleSortAux default (compare _ comparator) iterationCount l) (length l - iterationCount).
Proof.
  induction iterationCount as [| iterationCount IHiterationCount] in l, hIterationCount |- *.
  - split.
    + intros i j hIJ hI hJ. rewrite <- bubbleSortAuxPreservesLength in *. lia.
    + intros i j hI hJ hLength. rewrite <- bubbleSortAuxPreservesLength in *. lia.
  - pose proof IHiterationCount (bubbleSortPass default (compare A comparator) l) ltac:(rewrite bubbleSortPassPreservesLength; lia) as [hS hP].
    split.
    + simpl in *.
      intros i j hIJ hI hJ. pose proof hS i j ltac:(lia) as partial.
      rewrite <- !bubbleSortAuxPreservesLength, !bubbleSortPassPreservesLength in *.
      destruct (decide (length l - iterationCount = i + 1)) as [hSplit | hSplit].
      * pose proof hP (length l - iterationCount - 1) j ltac:(lia) ltac:(lia) as partial2.
        rewrite <- !bubbleSortAuxPreservesLength, !bubbleSortPassPreservesLength in *.
        pose proof partial2 ltac:(lia) as close. rewrite (ltac:(lia) : length l - iterationCount - 1 = i) in close. easy.
      * exact (partial ltac:(lia) ltac:(lia)).
    + intros i j hI hJ hL. rewrite <- bubbleSortAuxPreservesLength in *.
      destruct (decide (i = j)) as [hDiff | hDiff].
      { subst i. apply irreflexive. }
      destruct (decide (j <> length l - S iterationCount)).
      { simpl. rewrite bubbleSortPassPreservesLength in *.
        apply hP; rewrite <- ?bubbleSortAuxPreservesLength, ?bubbleSortPassPreservesLength; lia. }
      assert (hJEq : j = length l - S iterationCount). { lia. }
      subst j.
      simpl. rewrite moveBubbleSortPassOut.
      destruct (decide (iterationCount = 0)) as [hZ | hZ].
      { subst iterationCount. simpl.
        now pose proof bubblingUp default comparator l (length l - 1) i ltac:(lia) ltac:(lia). }
      pose proof bubblingUp default comparator (bubbleSortAux default (compare A comparator) iterationCount l) (length l - S iterationCount) i ltac:(lia) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia) as half.
      pose proof (nthBubbleSortPassPartial default (compare _ comparator) (bubbleSortAux default (compare A comparator) iterationCount l) i (length (bubbleSortAux default (compare A comparator) iterationCount l) - 1) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia)) as s1.
      rewrite !(ltac:(easy) : bubbleSortPassPartial _ _ _ _ = bubbleSortPass _ _ _) in s1.
      rewrite <- s1. clear s1.
      rewrite <- (nthBubbleSortPassPartial default (compare _ comparator) (bubbleSortAux default (compare A comparator) iterationCount l) i (length l - S iterationCount) ltac:(lia) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia)) in half.
      pose proof nthBubbleSortPassPartial default (compare _ comparator) (bubbleSortAux default (compare A comparator) iterationCount l) (length l - S iterationCount) (length (bubbleSortAux default (compare A comparator) iterationCount l) - 1) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia) ltac:(rewrite <- bubbleSortAuxPreservesLength; lia) as s1.
      rewrite (ltac:(easy) : bubbleSortPassPartial _ _ _ _ = bubbleSortPass _ _ _) in s1.
      rewrite <- s1. clear s1.
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
