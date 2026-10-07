From CoqCP Require Import Options Imperative.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat Lia Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition koxiaModulus : Z := 998244353.
Lemma modulus_positive : 0 < koxiaModulus. Proof. unfold koxiaModulus; lia. Qed.
Lemma residue_bounds x : 0 <= x mod koxiaModulus < koxiaModulus.
Proof. apply Z.mod_pos_bound, modulus_positive. Qed.
Lemma product_fits64 x y : 0 <= x < koxiaModulus -> 0 <= y < koxiaModulus ->
  0 <= x*y < 2^64.
Proof. unfold koxiaModulus. change (0 <= x < 998244353 -> 0 <= y < 998244353 -> 0 <= x*y < 18446744073709551616). nia. Qed.
Lemma residue_product_coerce x y : 0 <= x < koxiaModulus -> 0 <= y < koxiaModulus ->
  coerceInt (x*y) 64 = x*y.
Proof. intros hx hy. apply Z.mod_small, product_fits64; assumption. Qed.
Lemma residue_sum_coerce x y : 0 <= x < koxiaModulus -> 0 <= y < koxiaModulus ->
  coerceInt (x+y) 64 = x+y.
Proof. intros hx hy. unfold coerceInt, koxiaModulus in *. apply Z.mod_small.
  change (0 <= x+y < 18446744073709551616). lia. Qed.
Lemma butterfly_difference_coerce x y : 0 <= x < koxiaModulus -> 0 <= y < koxiaModulus ->
  coerceInt (coerceInt (x+koxiaModulus) 64-y) 64 = x+koxiaModulus-y.
Proof.
  intros hx hy. unfold coerceInt. rewrite (Z.mod_small (x+koxiaModulus) (2^64)).
  - apply Z.mod_small. unfold koxiaModulus in *. change (0 <= x+998244353-y < 18446744073709551616). lia.
  - unfold koxiaModulus in *. change (0 <= x+998244353 < 18446744073709551616). lia.
Qed.

Lemma mod_mul_left m x y : m <> 0 -> ((x mod m)*y) mod m = (x*y) mod m.
Proof. intro hm. rewrite (Z.mul_mod (x mod m) y m), Z.mod_mod by exact hm.
  symmetry. apply Z.mul_mod. exact hm. Qed.
Lemma mod_mul_right m x y : m <> 0 -> (x*(y mod m)) mod m = (x*y) mod m.
Proof. intro hm. rewrite (Z.mul_mod x (y mod m) m), Z.mod_mod by exact hm.
  symmetry. apply Z.mul_mod. exact hm. Qed.
Lemma mod_power m x exponent : m <> 0 -> 0 <= exponent ->
  ((x mod m)^exponent) mod m = (x^exponent) mod m.
Proof.
  intros hm he. rewrite <- (Z2Nat.id exponent he).
  induction (Z.to_nat exponent) as [| e IH].
  - reflexivity.
  - rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia.
    rewrite (Z.mul_mod (x mod m) ((x mod m)^Z.of_nat e) m), Z.mod_mod by exact hm.
    rewrite IH. symmetry. apply Z.mul_mod. exact hm.
Qed.

Fixpoint fastPower (fuel : nat) (base exponent answer : Z) : Z :=
  match fuel with
  | O => answer
  | S fuel => if Z.eqb exponent 0 then answer else
      fastPower fuel ((base*base) mod koxiaModulus) (exponent/2)
        (if Z.eqb (exponent mod 2) 1 then (answer*base) mod koxiaModulus else answer)
  end.

Lemma fastPower_bounds fuel base exponent answer : 0 <= answer < koxiaModulus ->
  0 <= fastPower fuel base exponent answer < koxiaModulus.
Proof.
  induction fuel as [| fuel IH] in base, exponent, answer |- *; cbn [fastPower]; [auto |].
  intro ha. destruct (Z.eqb exponent 0); [exact ha |]. apply IH.
  destruct (Z.eqb (exponent mod 2) 1); [apply residue_bounds | exact ha].
Qed.

Lemma power_binary_decomposition base exponent : 0 <= exponent ->
  base^exponent = (base*base)^(exponent/2) * base^(exponent mod 2).
Proof.
  intro he. pose proof (Z.div_pos exponent 2 ltac:(lia) ltac:(lia)) as hquot.
  pose proof (Z.mod_pos_bound exponent 2 ltac:(lia)) as hrem.
  pose proof (Z.div_mod exponent 2 ltac:(lia)) as decomp.
  rewrite decomp at 1. rewrite Z.pow_add_r by lia.
  rewrite (Z.pow_mul_r base 2 (exponent/2)) by lia. rewrite Z.pow_2_r. reflexivity.
Qed.

Theorem fastPower_correct fuel base exponent answer :
  0 <= exponent < 2^Z.of_nat fuel -> 0 <= answer < koxiaModulus ->
  fastPower fuel base exponent answer = (answer*base^exponent) mod koxiaModulus.
Proof.
  induction fuel as [| fuel IH] in base, exponent, answer |- *.
  - cbn [fastPower]. intros he ha. change (0 <= exponent < 1) in he.
    assert (zero : exponent = 0) by lia. subst exponent. rewrite Z.pow_0_r, Z.mul_1_r.
    symmetry. apply Z.mod_small. exact ha.
  - intros he ha. cbn [fastPower]. destruct (Z.eqb exponent 0) eqn:zero.
    + apply Z.eqb_eq in zero. subst exponent. rewrite Z.pow_0_r, Z.mul_1_r.
      symmetry. apply Z.mod_small. exact ha.
    + apply Z.eqb_neq in zero.
      assert (next : 0 <= exponent/2 < 2^Z.of_nat fuel).
      { split; [apply Z.div_pos; lia |]. apply Z.div_lt_upper_bound; [lia |].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in he by lia. lia. }
      pose proof (Z.mod_pos_bound exponent 2 ltac:(lia)) as rem.
      pose proof modulus_positive as hp.
      assert (nextAnswer : 0 <= (if Z.eqb (exponent mod 2) 1
        then (answer*base) mod koxiaModulus else answer) < koxiaModulus).
      { destruct (Z.eqb (exponent mod 2) 1); [apply residue_bounds | exact ha]. }
      rewrite IH by assumption.
      destruct (Z.eqb (exponent mod 2) 1) eqn:odd.
      * apply Z.eqb_eq in odd. rewrite mod_mul_left by lia.
        rewrite Z.mul_mod at 1 by lia. rewrite mod_power by lia.
        rewrite <- Z.mul_mod by lia. rewrite (power_binary_decomposition base exponent ltac:(lia)).
        rewrite odd, Z.pow_1_r. f_equal. ring.
      * apply Z.eqb_neq in odd. assert (even : exponent mod 2 = 0) by lia.
        rewrite Z.mul_mod at 1 by lia. rewrite mod_power by lia.
        rewrite <- Z.mul_mod by lia.
        rewrite (power_binary_decomposition base exponent ltac:(lia)). rewrite even, Z.pow_0_r, Z.mul_1_r. reflexivity.
Qed.

Definition modularPower base exponent := fastPower 64 base exponent 1.
Theorem modularPower_correct base exponent : 0 <= exponent < 2^64 ->
  modularPower base exponent = base^exponent mod koxiaModulus.
Proof.
  intro he. unfold modularPower. rewrite fastPower_correct by (unfold koxiaModulus; lia).
  rewrite Z.mul_1_l. reflexivity.
Qed.
