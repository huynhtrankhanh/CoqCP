From CoqCP Require Import Options KoxiaPolynomial KoxiaModular KoxiaRoots KoxiaFourier KoxiaBinomial KoxiaConvolutionMath.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia ZArith.ZArith.
Local Open Scope Z_scope.

Lemma zsum_head n f : zsum (S n) f=f 0+zsum n (fun i => f (1+i)).
Proof.
  pose proof (zsum_split 1 n f) as split.
  replace (1+n)%nat with (S n) in split by lia.
  cbn [zsum] in split. change (zsum n f+f (Z.of_nat n)=f 0+zsum n (fun i => f (1+i))) in split.
  cbn [zsum]. exact split.
Qed.
Lemma convolution_zsum kernel p index :
  convolution kernel p index=zsum (length kernel) (fun i => nth (Z.to_nat i) kernel 0*p (index-i)).
Proof.
  induction kernel as [|head kernel IH] in index |- *; [reflexivity|].
  cbn [convolution length]. rewrite IH,zsum_head.
  change (head*p index+zsum (length kernel) (fun i => nth (Z.to_nat i) kernel 0*p (index-1-i))=
    head*p (index-0)+zsum (length kernel) (fun i => nth (Z.to_nat (1+i)) (head::kernel) 0*p (index-(1+i)))).
  replace (index-0) with index by lia. f_equal. apply zsum_ext. intros i range.
  replace (Z.to_nat (1+i)) with (S (Z.to_nat i)) by lia.
  cbn [nth]. f_equal. f_equal. lia.
Qed.

Lemma zsum_delta n target f :
  zsum n (fun i => if Z.eqb i target then f i else 0)=
    if bool_decide (0<=target<Z.of_nat n) then f target else 0.
Proof.
  destruct (bool_decide (0<=target<Z.of_nat n)) eqn:inside.
  - apply bool_decide_eq_true in inside. apply zsum_select. exact inside.
  - apply bool_decide_eq_false in inside.
    transitivity (zsum n (fun _ => 0)); [|rewrite zsum_constant; ring].
    apply zsum_ext. intros i range. rewrite (proj2 (Z.eqb_neq i target)) by lia. reflexivity.
Qed.

Lemma linearConvolution_single n m p q index :
  linearConvolution n m p q index=
  zsum m (fun j => q j*(if bool_decide (0<=index-j<Z.of_nat n) then p (index-j) else 0)).
Proof.
  unfold linearConvolution. rewrite zsum_swap. apply zsum_ext. intros j range.
  transitivity (zsum n (fun i => if Z.eqb i (index-j) then q j*p i else 0)).
  - apply zsum_ext. intros i irange.
    assert (equality : Z.eqb (i+j) index=Z.eqb i (index-j)) by
      (apply eq_true_iff_eq; rewrite !Z.eqb_eq; lia).
    rewrite equality. destruct (Z.eqb i (index-j)); ring.
  - rewrite zsum_delta. destruct (bool_decide (0<=index-j<Z.of_nat n)); ring.
Qed.

Lemma linearConvolution_congruent n m p q p' q' index :
  (forall i, 0<=i<Z.of_nat n -> congruent (p i) (p' i)) ->
  (forall j, 0<=j<Z.of_nat m -> congruent (q j) (q' j)) ->
  congruent (linearConvolution n m p q index) (linearConvolution n m p' q' index).
Proof.
  intros pCorrect qCorrect. unfold linearConvolution. apply zsum_congruent. intros i range.
  apply zsum_congruent. intros j jrange. destruct (Z.eqb (i+j) index); [apply congruent_mul; auto|reflexivity].
Qed.

Theorem finite_linear_convolution n kernel p index : (length kernel<=n)%nat ->
  (forall i, i<0 \/ Z.of_nat n<=i -> p i=0) ->
  linearConvolution n n p (fun j => nth (Z.to_nat j) kernel 0) index=convolution kernel p index.
Proof.
  intros width support. rewrite linearConvolution_single,convolution_zsum.
  transitivity (zsum n (fun j => nth (Z.to_nat j) kernel 0*p (index-j))).
  - apply zsum_ext. intros j range.
    destruct (bool_decide (0<=index-j<Z.of_nat n)) eqn:inside; [reflexivity|].
    apply bool_decide_eq_false in inside. rewrite support by lia. ring.
  - replace n with (length kernel+(n-length kernel))%nat at 1 by lia.
    rewrite zsum_split.
    assert (zero : zsum (n-length kernel) (fun j => nth (Z.to_nat (Z.of_nat (length kernel)+j)) kernel 0*
      p (index-(Z.of_nat (length kernel)+j)))=0).
    { transitivity (zsum (n-length kernel) (fun _ => 0)); [|rewrite zsum_constant; ring].
      apply zsum_ext. intros j range. rewrite nth_overflow by lia. ring. }
    rewrite zero. ring.
Qed.
