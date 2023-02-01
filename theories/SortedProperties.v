From stdpp Require Import numbers list.
From CoqCP Require Import Sorted Comparator SelectionSort SelectionSortProperties.
Require Import Permutation.
Require Import Coq.Program.Equality.

Lemma sortedCons [A : Type] [default : A] [a : A] [l : list A] [compare : A -> A -> bool] (hCons : sorted default compare (a :: l)) : sorted default compare l.
Proof.
  intros i j hIJ hJ.
  pose proof hCons (S i) (S j) ltac:(lia) ltac:(simpl; lia) as H.
  simpl in H. assumption.
Qed.

Lemma elemOfIff [A : Type] [a : A] (l : list A) : elem_of a l <-> In a l.
Proof.
  split.
  - intro h.
    induction h.
    + constructor. reflexivity.
    + constructor 2. assumption.
  - intro h.
    induction l.
    + simpl in h. easy.
    + simpl in h. destruct h as [H | H].
      * rewrite H. constructor.
      * constructor 2. tauto.
Qed.

Lemma sortedArraysEqual [A : Type] [default : A] [l1 l2 : list A] [comparator : Comparator A] (hPermutation : Permutation l1 l2) (hL1Sorted : sorted default (compare _ comparator) l1) (hL2Sorted : sorted default (compare _ comparator) l2) (comparatorStrict : forall a b, compare _ comparator a b \/ compare _ comparator b a \/ a = b) : l1 = l2.
Proof.
  revert l2 hPermutation hL2Sorted.
  induction l1; intros l2 hPermutation hL2Sorted.
  - rewrite (Permutation_nil hPermutation). reflexivity.
  - destruct l2.
    + symmetry in hPermutation. rewrite (Permutation_nil hPermutation). reflexivity.
    + assert (hEq : a = a0).
      { pose proof proj2 (elem_of_Permutation (a :: l1) a0) ltac:(now exists l2) as H1.
        pose proof proj2 (elem_of_Permutation (a0 :: l2) a) ltac:(now exists l1) as H2.
        rewrite elemOfIff in *.
        destruct (In_nth (a :: l1) a0 default ltac:(assumption)) as [i1 [hi1 hnthi1]].
        destruct (In_nth (a0 :: l2) a default ltac:(assumption)) as [i2 [hi2 hnthi2]].
        destruct i1; [simpl in hnthi1; rewrite ?hnthi1; reflexivity | idtac].
        destruct i2; [simpl in hnthi2; rewrite ?hnthi2; reflexivity | idtac].
        pose proof hL1Sorted 0 (S i1) ltac:(lia) ltac:(lia) as ineq1.
        pose proof hL2Sorted 0 (S i2) ltac:(lia) ltac:(lia) as ineq2.
        rewrite hnthi1 in ineq1. rewrite hnthi2 in ineq2.
        simpl in ineq1, ineq2. destruct (comparatorStrict a a0) as [hSplit | [hSplit | hSplit]]; tauto. }
      rewrite hEq in *.
      erewrite (IHl1 (sortedCons hL1Sorted) l2 (Permutation_cons_inv hPermutation) (sortedCons hL2Sorted)). reflexivity.
Qed.
