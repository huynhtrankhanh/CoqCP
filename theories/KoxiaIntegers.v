From CoqCP Require Import Options Imperative.
From stdpp Require Import numbers.
From Stdlib Require Import ZArith.ZArith Lia.
Local Open Scope Z_scope.

Lemma coerce64_small value : 0 <= value < 2^64 -> coerceInt value 64 = value.
Proof. unfold coerceInt. apply Z.mod_small. Qed.
Lemma signed64_coerce value : -(2^63) <= value < 2^63 -> toSigned (coerceInt value 64) 64 = value.
Proof.
  intro bound. unfold coerceInt, toSigned.
  change ((if decide (value mod 18446744073709551616 < 9223372036854775808)
    then value mod 18446744073709551616
    else value mod 18446744073709551616 - 18446744073709551616) = value).
  change (-9223372036854775808 <= value < 9223372036854775808) in bound.
  destruct (Z_lt_dec value 0) as [negative | nonnegative].
  - assert (modulo : value mod 18446744073709551616 = value+18446744073709551616).
    { replace value with ((value+18446744073709551616) + (-1)*18446744073709551616) at 1 by ring.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite modulo, decide_False by lia. lia.
  - rewrite Z.mod_small, decide_True by lia. reflexivity.
Qed.
Lemma coerce64_add value step : coerceInt (coerceInt value 64+step) 64 = coerceInt (value+step) 64.
Proof.
  unfold coerceInt. rewrite Z.add_mod at 1 by lia.
  rewrite Z.mod_mod by lia. symmetry. apply Z.add_mod. lia.
Qed.
Lemma coerce64_sub value step : coerceInt (coerceInt value 64-step) 64 = coerceInt (value-step) 64.
Proof.
  unfold coerceInt. rewrite Zminus_mod at 1. rewrite Z.mod_mod by lia.
  symmetry. apply Zminus_mod.
Qed.
Lemma bracket_byte_coerce (opening : bool) : coerceInt (if opening then 40 else 41) 8 = if opening then 40 else 41.
Proof. destruct opening; reflexivity. Qed.
Lemma bracket_byte_flip (opening : bool) : Z.lxor (if opening then 40 else 41) 1 = if negb opening then 40 else 41.
Proof. destruct opening; reflexivity. Qed.
