From CoqCP Require Import Options Imperative Execution KnapsackCode DecimalDigits KoxiaPrinter.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec Submission.SpecProperties.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat Lia.
From stdpp Require Import numbers list.
Import ListNotations Trusted.Spec.
Local Open Scope nat_scope.

Lemma littleDigits_zero fuel : littleDigits fuel 0%Z = [].
Proof. destruct fuel; [reflexivity |]. cbn [littleDigits]. rewrite decide_True by reflexivity. reflexivity. Qed.
Lemma littleDigits_extend fuel extra value : (0 <= value < 10^Z.of_nat fuel)%Z ->
  littleDigits (fuel+extra) value = littleDigits fuel value.
Proof.
  induction fuel as [| fuel IH] in value |- *.
  - intro bound. change (0 <= value < 1)%Z in bound. assert (zero : value=0%Z) by lia.
    subst value. rewrite !littleDigits_zero. reflexivity.
  - intro bound. cbn [Nat.add littleDigits]. destruct (decide (value=0%Z)) as [zero | nonzero]; [reflexivity |].
    f_equal. apply IH. split; [apply Z.div_pos; lia |].
    apply Z.div_lt_upper_bound; [lia |]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in bound by lia. lia.
Qed.

Lemma decimal_littleDigits fuel value : 0 < value -> (Z.of_nat value < 10^Z.of_nat fuel)%Z ->
  decimal fuel value = rev (littleDigits fuel (Z.of_nat value)).
Proof.
  induction fuel as [| fuel IH] in value |- *.
  - intro positive. intro bound. change (Z.of_nat value < 1)%Z in bound. lia.
  - intros positive bound. cbn [decimal littleDigits].
    rewrite decide_False by lia.
    assert (divide : (Z.of_nat value / 10)%Z = Z.of_nat (value/10)) by (symmetry; apply (Nat2Z.inj_div value 10)).
    assert (remainder : (Z.of_nat value mod 10)%Z = Z.of_nat (value mod 10)) by (symmetry; apply (Nat2Z.inj_mod value 10)).
    destruct (value <? 10) eqn:small.
    + apply Nat.ltb_lt in small.
      assert (quotient : value/10 = 0) by (apply Nat.div_small; lia).
      rewrite divide, quotient, littleDigits_zero.
      rewrite remainder, Nat.mod_small by exact small. reflexivity.
    + apply Nat.ltb_ge in small. cbn [rev].
      rewrite divide, remainder.
      rewrite IH; [reflexivity | |].
      * apply Nat.div_str_pos; lia.
      * rewrite <- divide. apply Z.div_lt_upper_bound; [lia |].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in bound by lia. lia.
Qed.

Theorem specified_decimal_bytes value : (Z.of_nat value < 998244353)%Z ->
  decimalBytes value = decimal 10 value.
Proof.
  intro range. unfold decimalBytes. destruct (decide (value=0)) as [zero | positive].
  - subst value. reflexivity.
  - rewrite decimal_littleDigits.
    2: lia.
    2: change (Z.of_nat value < 10000000000)%Z; lia.
    change (reverse (littleDigits (10+10) (Z.of_nat value)) = rev (littleDigits 10 (Z.of_nat value))).
    rewrite littleDigits_extend.
    + unfold reverse. rewrite rev_append_rev, app_nil_r. reflexivity.
    +
    change (0 <= Z.of_nat value < 10000000000)%Z. lia.
Qed.

Theorem generated_spec_printer value state : (Z.of_nat value < 998244353)%Z ->
  length (memory state Generated.KoxiaAndBracket.arraydef_0__printBuffer) = 20 ->
  exists final,
    exec (KoxiaPrinter.mappedPrinter (Z.of_nat value)) state = Some (tt, final) /\
    stdout final = stdout state ++ decimal 10 value /\ stdin final = stdin state.
Proof.
  intros range buffer.
  assert (limit : value < 2^64).
  { apply Nat2Z.inj_lt. rewrite Nat2Z.inj_pow.
    change (Z.of_nat value < 18446744073709551616)%Z. lia. }
  destruct (printerExecutionAny value state limit buffer) as [scratch [execution size]].
  eexists. split; [exact execution |]. cbn [withOutput stdout setBuffer withMemory stdin].
  rewrite specified_decimal_bytes by exact range. auto.
Qed.
