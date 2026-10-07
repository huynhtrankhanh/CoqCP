From CoqCP Require Import Options KoxiaModular KoxiaNumberTheory KoxiaPolynomial.
From Stdlib Require Import ZArith.ZArith Lists.List Arith.PeanoNat Arith.Factorial Lia.
Import ListNotations.
Local Open Scope Z_scope.

Lemma addPolynomial_length a b : length (addPolynomial a b) = Nat.max (length a) (length b).
Proof.
  induction a as [| x a IH] in b |- *; destruct b as [| y b]; cbn [addPolynomial length Nat.max]; auto.
Qed.
Lemma addPolynomial_nth a b k : nth k (addPolynomial a b) 0 = nth k a 0 + nth k b 0.
Proof.
  induction a as [| x a IH] in b,k |- *; destruct b as [| y b]; destruct k as [| k];
    cbn [addPolynomial nth]; try rewrite IH; ring.
Qed.
Lemma binomialRow_length n : length (binomialRow n) = S n.
Proof.
  induction n as [| n IH]; [reflexivity |]. cbn [binomialRow].
  rewrite addPolynomial_length. cbn [length]. rewrite IH. lia.
Qed.
Definition choose n k := nth k (binomialRow n) 0.
Lemma choose_outside n k : (n < k)%nat -> choose n k = 0.
Proof. intro bound. unfold choose. apply nth_overflow. rewrite binomialRow_length. lia. Qed.
Lemma choose_first n : choose n 0 = 1.
Proof.
  induction n as [| n IH]; [reflexivity |]. unfold choose in *.
  cbn [binomialRow]. rewrite addPolynomial_nth. cbn [nth]. lia.
Qed.
Lemma choose_pascal n k : choose (S n) (S k) = choose n (S k) + choose n k.
Proof. unfold choose. cbn [binomialRow]. rewrite addPolynomial_nth. reflexivity. Qed.
Lemma choose_last n : choose n n = 1.
Proof.
  induction n as [| n IH]; [reflexivity |]. rewrite choose_pascal, choose_outside by lia. lia.
Qed.

Definition zFactorial n := Z.of_nat (fact n).
Lemma zFactorial_zero : zFactorial 0 = 1. Proof. reflexivity. Qed.
Lemma zFactorial_succ n : zFactorial (S n) = Z.of_nat (S n) * zFactorial n.
Proof. unfold zFactorial. cbn [fact]. rewrite Nat2Z.inj_mul. reflexivity. Qed.

Theorem binomial_factorial_identity n k : (k <= n)%nat ->
  choose n k * zFactorial k * zFactorial (n-k) = zFactorial n.
Proof.
  induction n as [| n IH] in k |- *.
  - intro bound. assert (zero : k=0%nat) by lia. subst k. reflexivity.
  - intro bound. destruct k as [| k].
    + rewrite choose_first, Nat.sub_0_r, zFactorial_zero. ring.
    + destruct (Nat.eq_dec k n) as [equal | before].
      * subst k. rewrite choose_last, Nat.sub_diag, zFactorial_zero. ring.
      * assert (kbound : (k < n)%nat) by lia.
        rewrite choose_pascal, zFactorial_succ.
        replace (S n - S k)%nat with (n-k)%nat by lia.
        assert (fac : zFactorial (n-k) = Z.of_nat (n-k) * zFactorial (n-S k)).
        { replace (n-k)%nat with (S (n-S k))%nat by lia. apply zFactorial_succ. }
        pose proof (IH k ltac:(lia)) as small.
        pose proof (IH (S k) ltac:(lia)) as large.
        rewrite zFactorial_succ in large.
        replace ((choose n (S k) + choose n k) * (Z.of_nat (S k)*zFactorial k) * zFactorial (n-k))
          with (Z.of_nat (n-k) * (choose n (S k) * (Z.of_nat (S k)*zFactorial k) * zFactorial (n-S k)) +
            Z.of_nat (S k)*(choose n k*zFactorial k*zFactorial (n-k)))
          by (rewrite fac; ring).
        rewrite large, small, zFactorial_succ.
        assert (sum : Z.of_nat (n-k) + Z.of_nat (S k) = Z.of_nat (S n)) by lia.
        rewrite <- sum. ring.
Qed.

Fixpoint factorialMod n : Z :=
  match n with O => 1 | S n => (factorialMod n * Z.of_nat (S n)) mod koxiaModulus end.
Lemma factorialMod_agrees n : factorialMod n = zFactorial n mod koxiaModulus.
Proof.
  induction n as [| n IH]; [reflexivity |]. cbn [factorialMod].
  rewrite IH, mod_mul_left by (pose proof modulus_positive; lia).
  rewrite zFactorial_succ. f_equal. ring.
Qed.
Lemma factorialMod_positive n : Z.of_nat n < koxiaModulus -> 0 < factorialMod n < koxiaModulus.
Proof.
  induction n as [| n IH].
  - cbn [factorialMod]. unfold koxiaModulus; lia.
  - intro bound. pose proof (IH ltac:(lia)) as previous.
    pose proof (residueProduct_positive [factorialMod n; Z.of_nat (S n)]) as nonzero.
    specialize (nonzero ltac:(repeat constructor; lia)).
    cbn [residueProduct] in nonzero.
    rewrite Z.mul_1_r, (Z.mod_small (Z.of_nat (S n)) koxiaModulus) in nonzero by lia. exact nonzero.
Qed.
Lemma modularPower_bounds base exponent : 0 <= modularPower base exponent < koxiaModulus.
Proof. unfold modularPower. apply fastPower_bounds. unfold koxiaModulus; lia. Qed.
Local Opaque fastPower modularPower.

Definition inverseFactorialMod n := modularPower (factorialMod n) (koxiaModulus-2).
Theorem factorialMod_inverse n : Z.of_nat n < koxiaModulus ->
  (factorialMod n * inverseFactorialMod n) mod koxiaModulus = 1.
Proof. intro bound. unfold inverseFactorialMod. apply fermat_inverse, factorialMod_positive. exact bound. Qed.

Theorem inverseFactorialMod_step n : Z.of_nat (S n) < koxiaModulus ->
  (inverseFactorialMod (S n) * Z.of_nat (S n)) mod koxiaModulus = inverseFactorialMod n.
Proof.
  intro bound. pose proof (factorialMod_inverse (S n) bound) as next.
  pose proof (factorialMod_inverse n ltac:(lia)) as current.
  pose proof (factorialMod_positive n ltac:(lia)) as nonzero.
  assert (equal : ((inverseFactorialMod (S n) * Z.of_nat (S n)) mod koxiaModulus) mod koxiaModulus =
    inverseFactorialMod n mod koxiaModulus).
  { apply (modulo_cancel (factorialMod n) _ _ nonzero).
    rewrite mod_mul_right by (pose proof modulus_positive; lia).
    cbn [factorialMod] in next. rewrite mod_mul_left in next by (pose proof modulus_positive; lia).
    rewrite current. replace (factorialMod n * (inverseFactorialMod (S n) * Z.of_nat (S n)))
      with (factorialMod n * Z.of_nat (S n) * inverseFactorialMod (S n)) by ring. exact next. }
  rewrite Z.mod_mod in equal by (pose proof modulus_positive; lia).
  assert (range : 0 <= inverseFactorialMod n < koxiaModulus).
  { unfold inverseFactorialMod. apply modularPower_bounds. }
  rewrite (Z.mod_small (inverseFactorialMod n) koxiaModulus) in equal by exact range. exact equal.
Qed.

Theorem factorial_binomial n k : (k <= n)%nat -> Z.of_nat n < koxiaModulus ->
  (((factorialMod n * inverseFactorialMod k) mod koxiaModulus) * inverseFactorialMod (n-k)) mod koxiaModulus =
  choose n k mod koxiaModulus.
Proof.
  intros kn bound. pose proof (binomial_factorial_identity n k kn) as identity.
  pose proof (factorialMod_inverse k ltac:(lia)) as ik.
  pose proof (factorialMod_inverse (n-k) ltac:(lia)) as ink.
  rewrite mod_mul_left by (pose proof modulus_positive; lia).
  rewrite factorialMod_agrees.
  replace (zFactorial n mod koxiaModulus * inverseFactorialMod k * inverseFactorialMod (n-k))
    with ((zFactorial n mod koxiaModulus) * (inverseFactorialMod k * inverseFactorialMod (n-k))) by ring.
  rewrite mod_mul_left by (pose proof modulus_positive; lia).
  rewrite <- identity.
  replace (choose n k * zFactorial k * zFactorial (n-k) * (inverseFactorialMod k * inverseFactorialMod (n-k)))
    with (choose n k * (zFactorial k * inverseFactorialMod k) *
      (zFactorial (n-k)*inverseFactorialMod (n-k))) by ring.
  rewrite factorialMod_agrees, mod_mul_left in ik, ink by (pose proof modulus_positive; lia).
  rewrite Z.mul_mod at 1 by (pose proof modulus_positive; lia). rewrite ink.
  rewrite Z.mul_1_r, Z.mod_mod by (pose proof modulus_positive; lia).
  rewrite Z.mul_mod at 1 by (pose proof modulus_positive; lia). rewrite ik.
  rewrite !Z.mul_1_r, !Z.mod_mod by (pose proof modulus_positive; lia). reflexivity.
Qed.
