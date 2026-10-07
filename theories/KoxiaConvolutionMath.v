From CoqCP Require Import Options KoxiaModular KoxiaRoots KoxiaFourier KoxiaBinomial.
From Stdlib Require Import Lia ZArith.ZArith.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Local Existing Instance congruent_mul.

Lemma zsum_reverse n f : zsum n (fun i => f (Z.of_nat n-1-i))=zsum n f.
Proof.
  induction n as [|n IH] in f |- *; [reflexivity|].
  cbn [zsum]. rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat n)-1-Z.of_nat n) with 0 by lia.
  transitivity (zsum n (fun i => f (1+i))+f 0).
  - f_equal. rewrite <-IH. apply zsum_ext. intros i range. f_equal. lia.
  - pose proof (zsum_split 1 n f) as first.
    replace (1+n)%nat with (S n) in first by lia. cbn [zsum] in first.
    change (zsum n f+f (Z.of_nat n)=f 0+zsum n (fun i => f (1+i))) in first. lia.
Qed.
Lemma zsum_reflect n f : (0<n)%nat ->
  zsum n (fun i => f ((-i) mod Z.of_nat n))=zsum n f.
Proof.
  intro positive. destruct n as [|n]; [lia|]. replace (S n) with (1+n)%nat by lia.
  rewrite !zsum_split. cbn [zsum]. change (0+f (0 mod Z.of_nat (1+n))+zsum n (fun i => f ((-(Z.of_nat 1+i)) mod Z.of_nat (1+n)))=
    0+f 0+zsum n (fun i => f (Z.of_nat 1+i))).
  rewrite Z.mod_0_l by lia.
  f_equal. rewrite Nat2Z.inj_add. change (zsum n (fun i => f ((-(1+i)) mod (1+Z.of_nat n)))=zsum n (fun i => f (1+i))).
  rewrite <-(zsum_reverse n (fun i => f (1+i))). apply zsum_ext. intros i range.
  replace ((-(1+i)) mod (1+Z.of_nat n)) with (Z.of_nat n-i).
  - f_equal. lia.
  - replace (-(1+i)) with ((Z.of_nat n-i)+(-1)*(1+Z.of_nat n)) by ring.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma rootPower_mod_equal stage a b : a mod stageSize stage=b mod stageSize stage ->
  rootPower stage a=rootPower stage b.
Proof. unfold rootPower. intro equal. rewrite equal. reflexivity. Qed.
Lemma fourier_reflect stage f frequency :
  fourier stage (fun i => f ((-i) mod stageSize stage)) frequency=fourier stage f (-frequency).
Proof.
  unfold fourier. rewrite stageSize_nat.
  transitivity (zsum (sizeNat stage)
    (fun i => (fun j => f j*rootPower stage (j*(-frequency))) ((-i) mod Z.of_nat (sizeNat stage)))).
  - apply zsum_ext. intros i range. f_equal. apply rootPower_mod_equal.
    rewrite stageSize_nat. rewrite Z.mul_mod_idemp_l by (pose proof (Nat.pow_nonzero 2 stage ltac:(lia)); lia).
    replace (-i * -frequency) with (i*frequency) by ring. reflexivity.
  - apply (zsum_reflect (sizeNat stage) (fun j => f j*rootPower stage (j*(-frequency)))).
    pose proof (stageSize_positive stage) as positive. rewrite stageSize_nat in positive. lia.
Qed.
Lemma fourier_scale stage f scale frequency :
  fourier stage (fun i => scale*f i) frequency=scale*fourier stage f frequency.
Proof. unfold fourier. rewrite <-zsum_scale. apply zsum_ext. intros. ring. Qed.
Lemma fourier_congruent stage f g frequency :
  (forall i, 0<=i<stageSize stage -> congruent (f i) (g i)) ->
  congruent (fourier stage f frequency) (fourier stage g frequency).
Proof. intro equal. unfold fourier. apply zsum_congruent. intros i range.
  apply congruent_mul; [apply equal; rewrite stageSize_nat; exact range|reflexivity]. Qed.

Theorem negated_scaled_transform stage frequencies index :
  congruent (fourier stage
    (fun i => (stageInverse stage * frequencies ((-i) mod stageSize stage)) mod koxiaModulus) index)
    (inverseFourier stage frequencies index).
Proof.
  transitivity (fourier stage (fun i => stageInverse stage*frequencies ((-i) mod stageSize stage)) index).
  - apply fourier_congruent. intros. apply congruent_modulo.
  - unfold inverseFourier. rewrite fourier_scale,fourier_reflect. reflexivity.
Qed.
