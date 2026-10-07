From CoqCP Require Import Options Imperative.
From Stdlib Require Import Numbers.DecimalNat ZArith.ZArith Lia.
Local Open Scope Z_scope.
Lemma capacityLiteral: Z.of_nat 500000%nat=500000.
Proof.
  cbv beta iota zeta delta [Nat.of_num_uint].
  rewrite DecimalNat.Unsigned.of_uint_alt.
  cbv beta iota zeta delta [DecimalNat.Unsigned.of_lu Decimal.rev Decimal.revapp].
  repeat first [rewrite Nat2Z.inj_mul | rewrite Nat2Z.inj_add].
  reflexivity.
Qed.
Lemma fuelLiteral: Z.to_nat 500001=500001%nat.
Proof.
  apply Nat2Z.inj. rewrite Z2Nat.id by lia.
  cbv beta iota zeta delta [Nat.of_num_uint].
  rewrite DecimalNat.Unsigned.of_uint_alt.
  cbv beta iota zeta delta [DecimalNat.Unsigned.of_lu Decimal.rev Decimal.revapp].
  repeat first [rewrite Nat2Z.inj_mul | rewrite Nat2Z.inj_add].
  reflexivity.
Qed.
