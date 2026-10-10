From CoqCP Require Import Options.
From Submission Require Import KoxiaModular KoxiaPrime.
From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory Lists.List Bool.Bool Lia Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Lemma nonzero_residue_coprime a : 0 < a < koxiaModulus -> rel_prime koxiaModulus a.
Proof.
  intro range. apply prime_rel_prime.
  - apply prime_alt. exact koxiaModulus_prime.
  - intro divided. pose proof (Z.divide_pos_le koxiaModulus a ltac:(lia) divided). lia.
Qed.

Lemma modulo_cancel a x y : 0 < a < koxiaModulus ->
  (a*x) mod koxiaModulus = (a*y) mod koxiaModulus -> x mod koxiaModulus = y mod koxiaModulus.
Proof.
  intros range equal. assert (divided : Z.divide koxiaModulus (a*(x-y))).
  { apply Z.mod_divide; [pose proof modulus_positive; lia |].
    replace (a*(x-y)) with (a*x-a*y) by ring.
    rewrite Zminus_mod, equal. rewrite Z.sub_diag, Z.mod_0_l; [reflexivity | pose proof modulus_positive; lia]. }
  apply (Gauss koxiaModulus a (x-y)) in divided; [| apply nonzero_residue_coprime; exact range].
  destruct divided as [q equality]. replace x with (y + q*koxiaModulus) by lia.
  rewrite Z.mod_add by (pose proof modulus_positive; lia). reflexivity.
Qed.

Fixpoint residueProduct (xs : list Z) : Z :=
  match xs with [] => 1 | x :: xs => (x*residueProduct xs) mod koxiaModulus end.
Lemma residueProduct_bounds xs : 0 <= residueProduct xs < koxiaModulus.
Proof. destruct xs; cbn [residueProduct]; [unfold koxiaModulus; lia | apply residue_bounds]. Qed.
Lemma residueProduct_positive xs : Forall (fun x => 0 < x < koxiaModulus) xs ->
  0 < residueProduct xs < koxiaModulus.
Proof.
  intro positive. induction positive as [| x xs hx positive IH]; cbn [residueProduct].
  - unfold koxiaModulus; lia.
  - pose proof (residue_bounds (x*residueProduct xs)) as bounds. split; [| lia].
    destruct (Z.eq_dec ((x*residueProduct xs) mod koxiaModulus) 0) as [zero | nonzero]; [| lia].
    assert (cancel : residueProduct xs mod koxiaModulus = 0).
    { apply (modulo_cancel x (residueProduct xs) 0 hx). rewrite Z.mul_0_r, Z.mod_0_l by (pose proof modulus_positive; lia). exact zero. }
    rewrite Z.mod_small in cancel by lia. lia.
Qed.

Lemma residueProduct_permutation xs ys : Permutation xs ys -> residueProduct xs = residueProduct ys.
Proof.
  intro perm. induction perm as [| x xs ys perm IH | x y xs | xs ys zs pxy IHxy pyz IHyz].
  - reflexivity.
  - cbn [residueProduct]. rewrite IH. reflexivity.
  - cbn [residueProduct]. rewrite !mod_mul_right by (pose proof modulus_positive; lia).
    f_equal. ring.
  - congruence.
Qed.
Lemma residueProduct_scale a xs :
  residueProduct (map (fun x => (a*x) mod koxiaModulus) xs) =
  (a^Z.of_nat (length xs) * residueProduct xs) mod koxiaModulus.
Proof.
  induction xs as [| x xs IH]; cbn [map length residueProduct].
  - cbn. unfold koxiaModulus. reflexivity.
  - rewrite IH, mod_mul_left, mod_mul_right by (pose proof modulus_positive; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite mod_mul_right by (pose proof modulus_positive; lia). f_equal. ring.
Qed.

Definition nonzeroResidues := map Z.of_nat (seq 1 (Z.to_nat (koxiaModulus-1))).
(* Keep the modulus symbolic when rewriting membership. Unifying [in_seq]
   with the concrete bound would expand nearly a billion unary successors. *)
Lemma positive_residues_member modulus x : 0 < modulus ->
  In x (map Z.of_nat (seq 1 (Z.to_nat (modulus-1)))) <-> 0 < x < modulus.
Proof.
  intro positive. rewrite in_map_iff. split.
  - intros [n [equal member]]. apply in_seq in member. subst x.
    rewrite Z2Nat.inj_sub in member by lia. lia.
  - intro bound. exists (Z.to_nat x). split; [apply Z2Nat.id; lia |].
    apply in_seq.
    rewrite Z2Nat.inj_sub by lia. lia.
Qed.
Lemma nonzeroResidues_member x : In x nonzeroResidues <-> 0 < x < koxiaModulus.
Proof. apply positive_residues_member, modulus_positive. Qed.
Lemma nonzeroResidues_length : Z.of_nat (length nonzeroResidues) = koxiaModulus-1.
Proof. unfold nonzeroResidues. rewrite length_map, length_seq. apply Z2Nat.id. pose proof modulus_positive; lia. Qed.
Lemma injective_map_unique {A B} (f : A -> B) xs :
  (forall x y, In x xs -> In y xs -> f x = f y -> x=y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros injective unique. induction unique as [| x xs fresh unique IH]; cbn; [constructor |].
  constructor.
  - intro member. apply in_map_iff in member. destruct member as [y [equal member]].
    apply fresh. assert (eq : y=x) by (apply injective; [right; exact member | left; reflexivity | exact equal]). subst y. exact member.
  - apply IH. intros a b ha hb eq. apply injective; [right; exact ha | right; exact hb | exact eq].
Qed.
Lemma nonzeroResidues_unique : NoDup nonzeroResidues.
Proof.
  unfold nonzeroResidues. apply injective_map_unique; [intros; lia | apply seq_NoDup].
Qed.
Local Opaque nonzeroResidues.

Lemma multiplication_residues_permutation a : 0 < a < koxiaModulus ->
  Permutation (map (fun x => (a*x) mod koxiaModulus) nonzeroResidues) nonzeroResidues.
Proof.
  intro ha. apply NoDup_Permutation_bis.
  - apply injective_map_unique; [| apply nonzeroResidues_unique].
    intros x y hx hy equal.
    pose proof (proj1 (nonzeroResidues_member x) hx) as hxBound.
    pose proof (proj1 (nonzeroResidues_member y) hy) as hyBound.
    clear hx hy.
    apply (modulo_cancel a x y ha) in equal. rewrite !Z.mod_small in equal by lia. exact equal.
  - rewrite length_map. lia.
  - intros y member.
    destruct (proj1 (@in_map_iff Z Z (fun x => (a*x) mod koxiaModulus)
      nonzeroResidues y) member) as [x [equal xMember]].
    pose proof (proj1 (nonzeroResidues_member x) xMember) as xBound.
    clear member xMember. subst y.
    apply (proj2 (nonzeroResidues_member ((a*x) mod koxiaModulus))).
    pose proof (residue_bounds (a*x)) as range. split; [| lia].
    assert (nonzero : (a*x) mod koxiaModulus <> 0).
    { intro zero. assert (cancel : x mod koxiaModulus = 0).
      { apply (modulo_cancel a x 0 ha). rewrite Z.mul_0_r, Z.mod_0_l by (pose proof modulus_positive; lia). exact zero. }
      rewrite Z.mod_small in cancel by lia. lia. }
    lia.
Qed.

Theorem koxia_fermat a : 0 < a < koxiaModulus -> a^(koxiaModulus-1) mod koxiaModulus = 1.
Proof.
  intro ha. pose proof (multiplication_residues_permutation a ha) as permutation.
  apply residueProduct_permutation in permutation.
  rewrite residueProduct_scale, nonzeroResidues_length in permutation.
  assert (hp : 0 < residueProduct nonzeroResidues < koxiaModulus).
  { apply residueProduct_positive. apply Forall_forall. intros x member.
    exact (proj1 (nonzeroResidues_member x) member). }
  apply (modulo_cancel (residueProduct nonzeroResidues) (a^(koxiaModulus-1)) 1 hp).
  rewrite Z.mul_comm, permutation, Z.mul_1_r, Z.mod_small by lia.
  reflexivity.
Qed.

Theorem fermat_inverse a : 0 < a < koxiaModulus ->
  (a * modularPower a (koxiaModulus-2)) mod koxiaModulus = 1.
Proof.
  intro ha. rewrite modularPower_correct.
  - rewrite mod_mul_right by (pose proof modulus_positive; lia).
    rewrite <- Z.pow_succ_r by (unfold koxiaModulus; lia).
    replace (Z.succ (koxiaModulus-2)) with (koxiaModulus-1) by lia.
    apply koxia_fermat. exact ha.
  - unfold koxiaModulus. change (0 <= 998244351 < 18446744073709551616). lia.
Qed.
