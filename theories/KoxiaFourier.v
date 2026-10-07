From CoqCP Require Import Options KoxiaModular KoxiaRoots KoxiaNumberTheory.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat Lists.List Lia
  Classes.RelationClasses Classes.Morphisms Setoid.
Local Open Scope Z_scope.
Local Opaque fastPower modularPower stageRoot stageInverse.

Definition congruent (x y : Z) := x mod koxiaModulus = y mod koxiaModulus.
#[local] Instance congruent_equivalence : Equivalence congruent.
Proof. split; unfold congruent; congruence. Qed.
#[local] Instance congruent_add : Proper (congruent ==> congruent ==> congruent) Z.add.
Proof. intros x y eqx a b eqa. unfold congruent in *.
  rewrite (Z.add_mod x a koxiaModulus), (Z.add_mod y b koxiaModulus) by (pose proof modulus_positive; lia). rewrite eqx,eqa. reflexivity. Qed.
#[local] Instance congruent_mul : Proper (congruent ==> congruent ==> congruent) Z.mul.
Proof. intros x y eqx a b eqa. unfold congruent in *.
  rewrite (Z.mul_mod x a koxiaModulus), (Z.mul_mod y b koxiaModulus) by (pose proof modulus_positive; lia). rewrite eqx,eqa. reflexivity. Qed.
#[local] Instance congruent_opp : Proper (congruent ==> congruent) Z.opp.
Proof.
  intros x y equal. replace (-x) with ((-1)*x) by ring. replace (-y) with ((-1)*y) by ring.
  apply congruent_mul; [reflexivity | exact equal].
Qed.
Lemma congruent_equal x y : x=y -> congruent x y. Proof. intros ->. reflexivity. Qed.
Lemma congruent_power x y e : 0 <= e -> congruent x y -> congruent (x^e) (y^e).
Proof.
  intros he equal. unfold congruent in *. rewrite <- (mod_power koxiaModulus x e), <- (mod_power koxiaModulus y e)
    by (try exact he; pose proof modulus_positive; lia). rewrite equal. reflexivity.
Qed.
Lemma congruent_modulo x : congruent (x mod koxiaModulus) x.
Proof. unfold congruent. apply Z.mod_mod. pose proof modulus_positive; lia. Qed.

Fixpoint zsum n (f : Z -> Z) : Z :=
  match n with O => 0 | S n => zsum n f + f (Z.of_nat n) end.
Lemma zsum_ext n f g : (forall i, 0 <= i < Z.of_nat n -> f i = g i) -> zsum n f = zsum n g.
Proof.
  induction n as [| n IH]; [reflexivity |]. intro equal. cbn [zsum].
  rewrite (equal (Z.of_nat n) ltac:(lia)). rewrite IH; [reflexivity |]. intros i range. apply equal. lia.
Qed.
Lemma zsum_congruent n f g : (forall i, 0 <= i < Z.of_nat n -> congruent (f i) (g i)) ->
  congruent (zsum n f) (zsum n g).
Proof.
  induction n as [| n IH]; [intros; reflexivity |]. intro equal. cbn [zsum]. apply congruent_add.
  - apply IH. intros i range. apply equal. lia.
  - apply equal. lia.
Qed.
Lemma zsum_add n f g : zsum n (fun i => f i+g i) = zsum n f + zsum n g.
Proof. induction n as [| n IH]; cbn [zsum]; rewrite ?IH; ring. Qed.
Lemma zsum_scale n a f : zsum n (fun i => a*f i) = a*zsum n f.
Proof. induction n as [| n IH]; cbn [zsum]; rewrite ?IH; ring. Qed.
Lemma zsum_scale_right n a f : zsum n (fun i => f i*a) = zsum n f*a.
Proof.
  replace (zsum n f*a) with (a*zsum n f) by ring.
  rewrite <- zsum_scale. apply zsum_ext. intros i hi. ring.
Qed.
Lemma zsum_constant n a : zsum n (fun _ => a) = Z.of_nat n*a.
Proof. induction n as [| n IH]; cbn [zsum]; rewrite ?IH, ?Nat2Z.inj_succ; lia. Qed.
Lemma zsum_split n m f : zsum (n+m)%nat f = zsum n f + zsum m (fun i => f (Z.of_nat n+i)).
Proof.
  induction m as [| m IH].
  - rewrite Nat.add_0_r. cbn [zsum]. lia.
  - rewrite Nat.add_succ_r. cbn [zsum]. rewrite IH, Nat2Z.inj_add. lia.
Qed.

Definition sizeNat (stage : nat) := (2^stage)%nat.
Lemma stageSize_nat stage : stageSize stage = Z.of_nat (sizeNat stage).
Proof. unfold stageSize,sizeNat. rewrite Nat2Z.inj_pow. reflexivity. Qed.
Lemma stageSize_succ stage : stageSize (S stage) = 2*stageSize stage.
Proof. unfold stageSize. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.
Lemma sizeNat_succ stage : sizeNat (S stage) = (sizeNat stage+sizeNat stage)%nat.
Proof. unfold sizeNat. cbn [Nat.pow]. lia. Qed.

Definition rootPower stage e := stageRoot stage ^ (e mod stageSize stage).
Lemma rootPower_zero stage : rootPower stage 0 = 1.
Proof. unfold rootPower. rewrite Z.mod_0_l by (pose proof (stageSize_positive stage); lia). apply Z.pow_0_r. Qed.
Lemma rootPower_periodic stage e : rootPower stage (e mod stageSize stage) = rootPower stage e.
Proof. unfold rootPower. rewrite Z.mod_mod by (pose proof (stageSize_positive stage); lia). reflexivity. Qed.
Lemma rootPower_unrestricted stage e : (stage <= 20)%nat -> 0 <= e ->
  congruent (rootPower stage e) (stageRoot stage ^ e).
Proof.
  intros bound he. pose proof (stageSize_positive stage) as hn.
  pose proof (Z.div_pos e (stageSize stage) he hn) as quotient.
  pose proof (Z.mod_pos_bound e (stageSize stage) hn) as remainder.
  pose proof (Z.div_mod e (stageSize stage) ltac:(lia)) as decomposition.
  rewrite decomposition at 2. rewrite Z.pow_add_r by lia.
  rewrite (Z.pow_mul_r (stageRoot stage) (stageSize stage) (e/stageSize stage)) by lia.
  assert (order : congruent (stageRoot stage ^ stageSize stage) 1).
  { unfold congruent. rewrite stageRoot_full_order by exact bound. reflexivity. }
  pose proof (congruent_power _ _ _ quotient order) as power.
  setoid_rewrite power. rewrite Z.pow_1_l by exact quotient. rewrite Z.mul_1_l. reflexivity.
Qed.
Lemma rootPower_add stage a b : (stage <= 20)%nat ->
  congruent (rootPower stage a * rootPower stage b) (rootPower stage (a+b)).
Proof.
  intro bound. pose proof (stageSize_positive stage) as hn.
  pose proof (Z.mod_pos_bound a (stageSize stage) hn) as ha.
  pose proof (Z.mod_pos_bound b (stageSize stage) hn) as hb.
  unfold rootPower at 1 2. rewrite <- Z.pow_add_r by lia.
  symmetry. unfold rootPower at 1. rewrite Z.add_mod by lia. fold (rootPower stage (a mod stageSize stage+b mod stageSize stage)).
  apply rootPower_unrestricted; [exact bound | lia].
Qed.

Definition characterSum stage frequency := zsum (sizeNat stage) (fun i => rootPower stage (i*frequency)).
Lemma characterSum_periodic stage frequency : characterSum stage (frequency mod stageSize stage) = characterSum stage frequency.
Proof.
  unfold characterSum. apply zsum_ext. intros i range. unfold rootPower.
  rewrite Z.mul_mod at 1 by (pose proof (stageSize_positive stage); lia).
  rewrite Z.mod_mod by (pose proof (stageSize_positive stage); lia).
  rewrite <- Z.mul_mod by (pose proof (stageSize_positive stage); lia). reflexivity.
Qed.
Lemma characterSum_zero stage : characterSum stage 0 = stageSize stage.
Proof.
  unfold characterSum. transitivity (zsum (sizeNat stage) (fun _ => 1)).
  - apply zsum_ext. intros i range. rewrite Z.mul_0_r. apply rootPower_zero.
  - rewrite zsum_constant, Z.mul_1_r, stageSize_nat. reflexivity.
Qed.

Lemma root_half_minus_one stage : (stage < 20)%nat ->
  congruent ((stageRoot (S stage))^stageSize stage) (-1).
Proof.
  intro bound. unfold congruent.
  pose proof (stageRoot_half_order (S stage) ltac:(lia)) as half.
  replace (S stage-1)%nat with stage in half by lia.
  rewrite half. unfold koxiaModulus; reflexivity.
Qed.
Lemma root_square_congruent stage : (stage < 20)%nat ->
  congruent ((stageRoot (S stage))^2) (stageRoot stage).
Proof.
  intro bound. unfold congruent. rewrite Z.pow_2_r, stageRoot_square by exact bound.
  symmetry. apply Z.mod_small, stageRoot_bounds.
Qed.
Lemma minus_one_odd e : 0 <= e -> e mod 2 = 1 -> (-1)^e = -1.
Proof.
  intros he odd. rewrite power_binary_decomposition by exact he.
  rewrite odd, Z.pow_1_r. change (1^(e/2)* -1 = -1).
  rewrite Z.pow_1_l by (apply Z.div_pos; lia). ring.
Qed.

Theorem root_exact_order stage e : (stage <= 20)%nat -> 0 < e < stageSize stage ->
  ~ congruent (stageRoot stage ^ e) 1.
Proof.
  induction stage as [| stage IH] in e |- *.
  - intros bound range. change (0 < e < 1) in range. lia.
  - intros bound range equal.
    pose proof (stageSize_positive stage) as halfPositive.
    pose proof (Z.mod_pos_bound e 2 ltac:(lia)) as remainder.
    destruct (Z.eq_dec (e mod 2) 1) as [odd | even].
    + pose proof (congruent_power _ _ (stageSize stage) ltac:(lia) equal) as raised.
      rewrite Z.pow_1_l in raised by lia.
      rewrite <- Z.pow_mul_r in raised by lia.
      rewrite (Z.mul_comm e (stageSize stage)), Z.pow_mul_r in raised by lia.
      pose proof (congruent_power _ _ e ltac:(lia) (root_half_minus_one stage ltac:(lia))) as minus.
      setoid_rewrite minus in raised. rewrite minus_one_odd in raised by assumption || lia.
      unfold congruent, koxiaModulus in raised. vm_compute in raised. discriminate raised.
    + assert (even0 : e mod 2 = 0) by lia.
      pose proof (Z.div_mod e 2 ltac:(lia)) as decomposition.
      assert (quotientRange : 0 < e/2 < stageSize stage).
      { rewrite stageSize_succ in range. lia. }
      apply (IH (e/2) ltac:(lia) quotientRange).
      pose proof (congruent_power _ _ (e/2) ltac:(lia) (root_square_congruent stage ltac:(lia))) as square.
      assert (power : stageRoot (S stage)^e = (stageRoot (S stage)^2)^(e/2)).
      { replace e with (2*(e/2)) at 1 by lia. apply Z.pow_mul_r; lia. }
      rewrite <- power in square. transitivity (stageRoot (S stage)^e); [symmetry; exact square | exact equal].
Qed.

Lemma congruent_minus_one x : congruent (x-1) 0 <-> congruent x 1.
Proof.
  split; intro equal.
  - replace x with ((x-1)+1) by ring. setoid_rewrite equal. reflexivity.
  - unfold Z.sub. setoid_rewrite equal. reflexivity.
Qed.
Lemma geometric_sum n root frequency : 0 <= frequency ->
  (root^frequency-1)*zsum n (fun i => root^(i*frequency)) = root^(Z.of_nat n*frequency)-1.
Proof.
  intro positive. induction n as [| n IH].
  - cbn [zsum]. rewrite Z.mul_0_l, Z.pow_0_r. ring.
  - cbn [zsum]. rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat n)*frequency) with (frequency+Z.of_nat n*frequency) by ring.
    rewrite Z.pow_add_r by nia. nia.
Qed.

Lemma characterSum_geometric stage frequency : (stage <= 20)%nat -> 0 <= frequency ->
  congruent ((stageRoot stage^frequency-1)*characterSum stage frequency) 0.
Proof.
  intros bound nonnegative.
  assert (sum : congruent (characterSum stage frequency)
    (zsum (sizeNat stage) (fun i => stageRoot stage^(i*frequency)))).
  { unfold characterSum. apply zsum_congruent. intros i range. apply rootPower_unrestricted; [exact bound | nia]. }
  setoid_rewrite sum. rewrite geometric_sum by exact nonnegative.
  rewrite <- stageSize_nat, Z.pow_mul_r by (pose proof (stageSize_positive stage); lia).
  assert (order : congruent (stageRoot stage^stageSize stage) 1).
  { unfold congruent. rewrite stageRoot_full_order by exact bound. reflexivity. }
  pose proof (congruent_power _ _ frequency nonnegative order) as powered.
  unfold Z.sub. setoid_rewrite powered. rewrite Z.pow_1_l by exact nonnegative. reflexivity.
Qed.

Lemma congruent_cancel a x y : a mod koxiaModulus <> 0 ->
  congruent (a*x) (a*y) -> congruent x y.
Proof.
  intros nonzero equal. pose proof (residue_bounds a) as range.
  unfold congruent in *. apply (modulo_cancel (a mod koxiaModulus) x y ltac:(lia)).
  rewrite !mod_mul_left by (pose proof modulus_positive; lia). exact equal.
Qed.
Theorem root_orthogonality stage frequency : (stage <= 20)%nat ->
  congruent (characterSum stage frequency)
    (if Z.eqb (frequency mod stageSize stage) 0 then stageSize stage else 0).
Proof.
  intro bound. rewrite <- characterSum_periodic.
  pose proof (stageSize_positive stage) as hn.
  pose proof (Z.mod_pos_bound frequency (stageSize stage) hn) as remainder.
  destruct (Z.eqb (frequency mod stageSize stage) 0) eqn:zero.
  - apply Z.eqb_eq in zero. rewrite zero, characterSum_zero. reflexivity.
  - apply Z.eqb_neq in zero.
    assert (nonzero : (stageRoot stage^(frequency mod stageSize stage)-1) mod koxiaModulus <> 0).
    { intro impossible. apply (root_exact_order stage (frequency mod stageSize stage) bound ltac:(lia)).
      apply congruent_minus_one. unfold congruent. rewrite impossible. reflexivity. }
    apply (congruent_cancel (stageRoot stage^(frequency mod stageSize stage)-1) _ 0 nonzero).
    rewrite Z.mul_0_r. apply characterSum_geometric; [exact bound | lia].
Qed.

Lemma zsum_swap n m f :
  zsum n (fun i => zsum m (fun j => f i j)) =
  zsum m (fun j => zsum n (fun i => f i j)).
Proof.
  induction n as [|n IH].
  - cbn [zsum]. rewrite zsum_constant. ring.
  - cbn [zsum]. rewrite IH, <- zsum_add. reflexivity.
Qed.
Lemma zsum_select n j f : 0 <= j < Z.of_nat n ->
  zsum n (fun i => if Z.eqb i j then f i else 0) = f j.
Proof.
  induction n as [|n IH]; intro range; [lia|]. cbn [zsum].
  destruct (Z.eq_dec j (Z.of_nat n)) as [->|different].
  - rewrite Z.eqb_refl.
    assert (zero : zsum n (fun i => if Z.eqb i (Z.of_nat n) then f i else 0) = 0).
    { transitivity (zsum n (fun _ => 0)).
      - apply zsum_ext. intros i hi.
        assert (different : Z.eqb i (Z.of_nat n) = false) by (apply Z.eqb_neq; lia).
        rewrite different. reflexivity.
      - rewrite zsum_constant. ring. }
    rewrite zero. ring.
  - assert (neq : Z.eqb (Z.of_nat n) j = false) by (apply Z.eqb_neq; lia).
    rewrite neq. rewrite IH by lia. ring.
Qed.
Lemma modular_difference_zero n i j : 0 < n -> 0 <= i < n -> 0 <= j < n ->
  Z.eqb ((i-j) mod n) 0 = Z.eqb i j.
Proof.
  intros hn hi hj. apply Bool.eq_true_iff_eq. rewrite !Z.eqb_eq.
  split.
  - intro equal. pose proof (Z.div_mod (i-j) n ltac:(lia)) as decomposition.
    assert (quotient : -1 <= (i-j)/n <= 0).
    { split.
      - apply Z.div_le_lower_bound; lia.
      - assert ((i-j)/n < 1) by (apply Z.div_lt_upper_bound; lia). lia. }
    destruct (Z.eq_dec ((i-j)/n) 0) as [zero|negative].
    + rewrite zero, equal in decomposition. lia.
    + assert (minus : (i-j)/n = -1) by lia.
      rewrite minus, equal in decomposition. lia.
  - intros ->. rewrite Z.sub_diag. apply Z.mod_0_l; lia.
Qed.

Definition fourier stage (coefficients : Z -> Z) frequency :=
  zsum (sizeNat stage) (fun i => coefficients i * rootPower stage (i*frequency)).
Definition inverseFourier stage (frequencies : Z -> Z) index :=
  stageInverse stage * fourier stage frequencies (-index).

Theorem fourier_double stage coefficients index : (stage <= 20)%nat ->
  0 <= index < stageSize stage ->
  congruent (fourier stage (fourier stage coefficients) (-index))
    (stageSize stage * coefficients index).
Proof.
  intros bound range. unfold fourier.
  set (n := sizeNat stage).
  transitivity (zsum n (fun k => zsum n
    (fun i => coefficients i * (rootPower stage (i*k)*rootPower stage (k * -index))))).
  - apply zsum_congruent. intros k hk.
    rewrite <- zsum_scale_right.
    apply zsum_congruent. intros i hi. apply congruent_equal. ring.
  - rewrite zsum_swap.
    transitivity (zsum n (fun i => coefficients i * characterSum stage (i-index))).
    + apply zsum_congruent. intros i hi. unfold characterSum. fold n.
      rewrite <- zsum_scale. apply zsum_congruent. intros k hk.
      apply congruent_mul; [reflexivity|].
      transitivity (rootPower stage (i*k+k * -index)).
      * apply rootPower_add. exact bound.
      * replace (i*k+k * -index) with (k*(i-index)) by ring. reflexivity.
    + transitivity (zsum n (fun i => if Z.eqb i index
        then stageSize stage * coefficients i else 0)).
      * apply zsum_congruent. intros i hi.
        pose proof (root_orthogonality stage (i-index) bound) as orthogonal.
        rewrite modular_difference_zero in orthogonal by
          (try exact range; try apply stageSize_positive; unfold n in hi; rewrite stageSize_nat; exact hi).
        setoid_rewrite orthogonal.
        destruct (Z.eqb i index); apply congruent_equal; ring.
      * rewrite zsum_select; [reflexivity|]. unfold n. rewrite <- stageSize_nat. exact range.
Qed.

Theorem fourier_inverse stage coefficients index : (stage <= 20)%nat ->
  0 <= index < stageSize stage ->
  congruent (inverseFourier stage (fourier stage coefficients) index) (coefficients index).
Proof.
  intros bound range. unfold inverseFourier.
  pose proof (fourier_double stage coefficients index bound range) as double.
  setoid_rewrite double.
  replace (stageInverse stage * (stageSize stage * coefficients index)) with
    ((stageSize stage * stageInverse stage)*coefficients index) by ring.
  assert (inverse : congruent (stageSize stage * stageInverse stage) 1).
  { unfold congruent. rewrite stageSize_inverse by exact bound. reflexivity. }
  setoid_rewrite inverse. rewrite Z.mul_1_l. reflexivity.
Qed.

Definition cyclicConvolution stage p q index :=
  zsum (sizeNat stage) (fun i => zsum (sizeNat stage)
    (fun j => if Z.eqb ((i+j-index) mod stageSize stage) 0 then p i*q j else 0)).
Definition linearConvolution n m p q index :=
  zsum n (fun i => zsum m (fun j => if Z.eqb (i+j) index then p i*q j else 0)).

Lemma zsum_product n m f g :
  zsum n f * zsum m g = zsum n (fun i => zsum m (fun j => f i*g j)).
Proof.
  transitivity (zsum n (fun i => f i*zsum m g)).
  - symmetry. apply zsum_scale_right.
  - apply zsum_ext. intros i hi. symmetry. apply zsum_scale.
Qed.

Theorem fourier_convolution stage p q index : (stage <= 20)%nat ->
  0 <= index < stageSize stage ->
  congruent (inverseFourier stage (fun k => fourier stage p k * fourier stage q k) index)
    (cyclicConvolution stage p q index).
Proof.
  intros bound range. unfold inverseFourier, fourier.
  set (n := sizeNat stage).
  assert (expand : zsum n (fun k =>
    zsum n (fun i => p i*rootPower stage (i*k)) *
    zsum n (fun j => q j*rootPower stage (j*k)) *rootPower stage (k * -index)) =
    zsum n (fun i => zsum n (fun j => zsum n (fun k =>
      p i*q j*(rootPower stage (i*k)*rootPower stage (j*k)*rootPower stage (k * -index)))))).
  { transitivity (zsum n (fun k => zsum n (fun i => zsum n (fun j =>
      p i*q j*(rootPower stage (i*k)*rootPower stage (j*k)*rootPower stage (k * -index)))))).
    - apply zsum_ext. intros k hk. rewrite zsum_product, <- zsum_scale_right.
      apply zsum_ext. intros i hi. rewrite <- zsum_scale_right.
      apply zsum_ext. intros j hj. ring.
    - rewrite zsum_swap. apply zsum_ext. intros i hi. apply zsum_swap. }
  rewrite expand.
  transitivity (stageInverse stage * zsum n (fun i => zsum n (fun j =>
    p i*q j*characterSum stage (i+j-index)))).
  - apply congruent_mul; [reflexivity|]. apply zsum_congruent. intros i hi.
    apply zsum_congruent. intros j hj. unfold characterSum. fold n.
    rewrite <- zsum_scale. apply zsum_congruent. intros k hk.
    apply congruent_mul; [reflexivity|].
    pose proof (rootPower_add stage (i*k) (j*k) bound) as pair.
    setoid_rewrite pair.
    transitivity (rootPower stage (i*k+j*k+k * -index)).
    + apply rootPower_add. exact bound.
    + replace (i*k+j*k+k * -index) with (k*(i+j-index)) by ring. reflexivity.
  - unfold cyclicConvolution. fold n.
    rewrite <- zsum_scale. apply zsum_congruent. intros i hi.
    rewrite <- zsum_scale. apply zsum_congruent. intros j hj.
    pose proof (root_orthogonality stage (i+j-index) bound) as orthogonal.
    setoid_rewrite orthogonal.
    destruct (Z.eqb ((i+j-index) mod stageSize stage) 0).
    + replace (stageInverse stage*(p i*q j*stageSize stage)) with
        ((stageSize stage*stageInverse stage)*(p i*q j)) by ring.
      assert (inverse : congruent (stageSize stage*stageInverse stage) 1).
      { unfold congruent. rewrite stageSize_inverse by exact bound. reflexivity. }
      setoid_rewrite inverse. rewrite Z.mul_1_l. reflexivity.
    + rewrite !Z.mul_0_r. reflexivity.
Qed.

Theorem zero_padded_convolution stage p q a b index :
  (a+b <= S (sizeNat stage))%nat ->
  (a <= sizeNat stage)%nat -> (b <= sizeNat stage)%nat ->
  (forall i, Z.of_nat a <= i < stageSize stage -> p i=0) ->
  (forall j, Z.of_nat b <= j < stageSize stage -> q j=0) ->
  0 <= index < stageSize stage ->
  cyclicConvolution stage p q index = linearConvolution (sizeNat stage) (sizeNat stage) p q index.
Proof.
  intros width ha hb pzero qzero range. unfold cyclicConvolution, linearConvolution.
  apply zsum_ext. intros i hi. apply zsum_ext. intros j hj.
  rewrite <- stageSize_nat in hi,hj.
  destruct (Z_lt_ge_dec i (Z.of_nat a)) as [ia|ia];
    destruct (Z_lt_ge_dec j (Z.of_nat b)) as [jb|jb].
  - assert (sumrange : 0 <= i+j < stageSize stage).
    { rewrite stageSize_nat. apply Nat2Z.inj_le in width. rewrite Nat2Z.inj_add, Nat2Z.inj_succ in width. lia. }
    replace (i+j-index) with ((i+j)-index) by ring.
    rewrite modular_difference_zero by (try apply stageSize_positive; assumption). reflexivity.
  - rewrite qzero by lia. destruct (Z.eqb ((i+j-index) mod stageSize stage) 0), (Z.eqb (i+j) index); ring.
  - rewrite pzero by lia. destruct (Z.eqb ((i+j-index) mod stageSize stage) 0), (Z.eqb (i+j) index); ring.
  - rewrite pzero by lia. destruct (Z.eqb ((i+j-index) mod stageSize stage) 0), (Z.eqb (i+j) index); ring.
Qed.

Theorem ntt_linear_convolution stage p q a b index : (stage <= 20)%nat ->
  (a+b <= S (sizeNat stage))%nat ->
  (a <= sizeNat stage)%nat -> (b <= sizeNat stage)%nat ->
  (forall i, Z.of_nat a <= i < stageSize stage -> p i=0) ->
  (forall j, Z.of_nat b <= j < stageSize stage -> q j=0) ->
  0 <= index < stageSize stage ->
  congruent (inverseFourier stage (fun k => fourier stage p k*fourier stage q k) index)
    (linearConvolution (sizeNat stage) (sizeNat stage) p q index).
Proof.
  intros bound width ha hb pzero qzero range.
  rewrite <- (zero_padded_convolution stage p q a b index width ha hb pzero qzero range).
  apply fourier_convolution; assumption.
Qed.

Lemma zsum_even_odd n f :
  zsum (n+n)%nat f = zsum n (fun i => f (2*i)) + zsum n (fun i => f (2*i+1)).
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (S n+S n)%nat with (S (S (n+n))) by lia.
  cbn [zsum]. rewrite IH, !Nat2Z.inj_succ, !Nat2Z.inj_add.
  replace (Z.of_nat n+Z.of_nat n) with (2*Z.of_nat n) by ring.
  replace (Z.succ (2*Z.of_nat n)) with (2*Z.of_nat n+1) by lia.
  ring.
Qed.
Lemma rootPower_even stage e : (stage < 20)%nat -> 0 <= e ->
  congruent (rootPower (S stage) (2*e)) (rootPower stage e).
Proof.
  intros bound nonnegative.
  transitivity (stageRoot (S stage)^(2*e)).
  - apply rootPower_unrestricted; lia.
  - rewrite Z.pow_mul_r by lia.
    pose proof (congruent_power _ _ e nonnegative (root_square_congruent stage bound)) as squares.
    transitivity (stageRoot stage^e); [exact squares|]. symmetry. apply rootPower_unrestricted; lia.
Qed.

Theorem fourier_even_odd stage p frequency : (stage < 20)%nat -> 0 <= frequency ->
  congruent (fourier (S stage) p frequency)
    (fourier stage (fun i => p (2*i)) frequency +
      rootPower (S stage) frequency * fourier stage (fun i => p (2*i+1)) frequency).
Proof.
  intros bound nonnegative. unfold fourier. rewrite sizeNat_succ, zsum_even_odd.
  apply congruent_add.
  - apply zsum_congruent. intros i hi. apply congruent_mul; [reflexivity|].
    replace (2*i*frequency) with (2*(i*frequency)) by ring. apply rootPower_even; [exact bound|nia].
  - rewrite <- zsum_scale. apply zsum_congruent. intros i hi.
    transitivity (p (2*i+1)*(rootPower stage (i*frequency)*rootPower (S stage) frequency)).
    + apply congruent_mul; [reflexivity|].
      pose proof (rootPower_even stage (i*frequency) bound ltac:(nia)) as even.
      transitivity (rootPower (S stage) (2*(i*frequency))*rootPower (S stage) frequency).
      * replace ((2*i+1)*frequency) with (2*(i*frequency)+frequency) by ring.
        symmetry. apply rootPower_add; lia.
      * apply congruent_mul; [exact even|reflexivity].
    + apply congruent_equal. ring.
Qed.
Lemma fourier_periodic stage p frequency :
  fourier stage p (frequency mod stageSize stage) = fourier stage p frequency.
Proof.
  unfold fourier. apply zsum_ext. intros i hi. f_equal.
  unfold rootPower. rewrite Z.mul_mod at 1 by (pose proof (stageSize_positive stage); lia).
  rewrite Z.mod_mod by (pose proof (stageSize_positive stage); lia).
  rewrite <- Z.mul_mod by (pose proof (stageSize_positive stage); lia). reflexivity.
Qed.
Lemma fourier_shift stage p frequency : fourier stage p (frequency+stageSize stage) = fourier stage p frequency.
Proof.
  rewrite <- (fourier_periodic stage p (frequency+stageSize stage)).
  replace (frequency+stageSize stage) with (frequency+1*stageSize stage) by ring.
  rewrite Z.mod_add by (pose proof (stageSize_positive stage); lia).
  apply fourier_periodic.
Qed.
Lemma rootPower_half stage : (stage < 20)%nat ->
  congruent (rootPower (S stage) (stageSize stage)) (-1).
Proof.
  intro bound. transitivity (stageRoot (S stage)^stageSize stage).
  - apply rootPower_unrestricted; [lia|pose proof (stageSize_positive stage); lia].
  - apply root_half_minus_one. exact bound.
Qed.
Theorem fourier_second_half stage p frequency : (stage < 20)%nat -> 0 <= frequency ->
  congruent (fourier (S stage) p (frequency+stageSize stage))
    (fourier stage (fun i => p (2*i)) frequency -
      rootPower (S stage) frequency * fourier stage (fun i => p (2*i+1)) frequency).
Proof.
  intros bound nonnegative.
  pose proof (fourier_even_odd stage p (frequency+stageSize stage) bound
    ltac:(pose proof (stageSize_positive stage); lia)) as split.
  rewrite !fourier_shift in split. transitivity
    (fourier stage (fun i => p (2*i)) frequency + rootPower (S stage) (frequency+stageSize stage)*
      fourier stage (fun i => p (2*i+1)) frequency); [exact split|].
  pose proof (rootPower_add (S stage) frequency (stageSize stage) ltac:(lia)) as addition.
  setoid_rewrite <- addition.
  pose proof (rootPower_half stage bound) as half. setoid_rewrite half.
  apply congruent_equal. ring.
Qed.

Fixpoint radixTwo stage (p : Z -> Z) index : Z :=
  match stage with
  | O => p 0 mod koxiaModulus
  | S stage =>
    let offset := index mod stageSize stage in
    let even := radixTwo stage (fun i => p (2*i)) offset in
    let odd := radixTwo stage (fun i => p (2*i+1)) offset in
    let twiddle := rootPower (S stage) offset * odd in
    (if index <? stageSize stage then even+twiddle else even-twiddle) mod koxiaModulus
  end.

Theorem radixTwo_correct stage p index : (stage <= 20)%nat ->
  0 <= index < stageSize stage -> congruent (radixTwo stage p index) (fourier stage p index).
Proof.
  induction stage as [|stage IH] in p,index |- *.
  - intros bound range. change (0 <= index < 1) in range. assert (index=0) by lia. subst index.
    cbn [radixTwo fourier sizeNat Nat.pow zsum]. rewrite Z.mul_0_l, rootPower_zero.
    rewrite Z.mul_1_r, Z.add_0_l. apply congruent_modulo.
  - intros bound range. cbn [radixTwo].
    pose proof (stageSize_positive stage) as hn.
    pose proof (Z.mod_pos_bound index (stageSize stage) hn) as offsetRange.
    pose proof (IH (fun i => p (2*i)) (index mod stageSize stage) ltac:(lia) offsetRange) as even.
    pose proof (IH (fun i => p (2*i+1)) (index mod stageSize stage) ltac:(lia) offsetRange) as odd.
    transitivity (if index <? stageSize stage then
      fourier stage (fun i => p (2*i)) (index mod stageSize stage) +
        rootPower (S stage) (index mod stageSize stage)*fourier stage (fun i => p (2*i+1)) (index mod stageSize stage)
      else fourier stage (fun i => p (2*i)) (index mod stageSize stage) -
        rootPower (S stage) (index mod stageSize stage)*fourier stage (fun i => p (2*i+1)) (index mod stageSize stage)).
    + destruct (index <? stageSize stage).
      * transitivity (radixTwo stage (fun i => p (2*i)) (index mod stageSize stage) +
          rootPower (S stage) (index mod stageSize stage)*radixTwo stage (fun i => p (2*i+1)) (index mod stageSize stage)).
        -- apply congruent_modulo.
        -- setoid_rewrite even. setoid_rewrite odd. reflexivity.
      * transitivity (radixTwo stage (fun i => p (2*i)) (index mod stageSize stage) -
          rootPower (S stage) (index mod stageSize stage)*radixTwo stage (fun i => p (2*i+1)) (index mod stageSize stage)).
        -- apply congruent_modulo.
        -- unfold Z.sub. setoid_rewrite even. setoid_rewrite odd. reflexivity.
    + destruct (index <? stageSize stage) eqn:lower.
      * apply Z.ltb_lt in lower. rewrite Z.mod_small by lia.
        symmetry. apply fourier_even_odd; lia.
      * apply Z.ltb_ge in lower.
        assert (offset : index mod stageSize stage = index-stageSize stage).
        { rewrite stageSize_succ in range.
          replace index with ((index-stageSize stage)+1*stageSize stage) at 1 by ring.
          rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
        rewrite offset.
        pose proof (fourier_second_half stage p (index-stageSize stage) ltac:(lia) ltac:(lia)) as second.
        replace (index-stageSize stage+stageSize stage) with index in second by ring.
        symmetry. exact second.
Qed.
