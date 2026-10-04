From CoqCP Require Import Options Imperative KnapsackCode.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Definition decodeDigits (digits : list Z) (initial : Z) :=
  fold_left (fun value digit => 10 * value + digit - 48) digits initial.
Definition decimalDigit digit := 48 <= digit < 58.

Lemma littleDigits_length fuel value : (length (littleDigits fuel value) <= fuel)%nat.
Proof.
  induction fuel as [| fuel IH] in value |- *; [reflexivity |].
  cbn [littleDigits]. destruct (decide (value = 0)); [cbn; lia |].
  cbn [length]. specialize (IH (value / 10)). lia.
Qed.
Lemma littleDigits_valid fuel value : Forall decimalDigit (littleDigits fuel value).
Proof.
  induction fuel as [| fuel IH] in value |- *; [constructor |].
  cbn [littleDigits]. destruct (decide (value = 0)); [constructor |].
  constructor; [unfold decimalDigit; pose proof Z.mod_pos_bound value 10 ltac:(lia); lia | apply IH].
Qed.
Lemma decode_littleDigits fuel value (h : 0 <= value < 10 ^ Z.of_nat fuel) :
  decodeDigits (reverse (littleDigits fuel value)) 0 = value.
Proof.
  induction fuel as [| fuel IH] in value, h |- *.
  - change (0 = value). change (0 <= value < 1) in h. lia.
  - cbn [littleDigits]. destruct (decide (value = 0)) as [zero | nonzero].
    + subst value. reflexivity.
    + rewrite reverse_cons. unfold decodeDigits at 1. rewrite fold_left_app.
      change (10 * decodeDigits (reverse (littleDigits fuel (value / 10))) 0 + (value mod 10 + 48) - 48 = value).
      rewrite IH.
      * pose proof Z.div_mod value 10 ltac:(lia). lia.
      * split; [apply Z.div_pos; lia |].
        apply Z.div_lt_upper_bound; [lia |].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in h; [nia | lia].
Qed.

Lemma decimalBytes_valid value : Forall decimalDigit (decimalBytes value).
Proof.
  unfold decimalBytes. destruct (decide (value = 0)%nat).
  - constructor; [unfold decimalDigit; lia | constructor].
  - apply Forall_reverse. apply littleDigits_valid.
Qed.
Lemma decimalBytes_length value : (length (decimalBytes value) <= 20)%nat.
Proof.
  unfold decimalBytes. destruct (decide (value = 0)%nat); [cbn; lia |].
  rewrite length_reverse. apply littleDigits_length.
Qed.
Lemma decimalBytes_decode value (h : (value < 2^64)%nat) : decodeDigits (decimalBytes value) 0 = Z.of_nat value.
Proof.
  unfold decimalBytes. destruct (decide (value = 0)%nat); [subst value; reflexivity |].
  apply decode_littleDigits. split; [lia |].
  assert (power : Z.of_nat (2^64)%nat = (2^64)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (comparison : (2^64 < 10^20)%Z) by (vm_compute; reflexivity).
  lia.
Qed.
Lemma decimalBytes_nonempty value (h : (value < 2^64)%nat) : decimalBytes value <> [].
Proof.
  intro empty. pose proof decimalBytes_decode value h as decoded.
  rewrite empty in decoded. cbn [decodeDigits fold_left] in decoded.
  assert (value = 0%nat) by lia. subst value. discriminate empty.
Qed.

Lemma decodeDigits_nonnegative digits initial
  (hDigits : Forall decimalDigit digits) (hInitial : 0 <= initial) : 0 <= decodeDigits digits initial.
Proof.
  induction hDigits as [| digit digits hd hs IH] in initial, hInitial |- *; [exact hInitial |].
  unfold decodeDigits. cbn [fold_left]. apply IH. unfold decimalDigit in hd. lia.
Qed.
Lemma decodeDigits_ge digits initial
  (hDigits : Forall decimalDigit digits) (hInitial : 0 <= initial) : initial <= decodeDigits digits initial.
Proof.
  induction hDigits as [| digit digits hd hs IH] in initial, hInitial |- *; [apply Z.le_refl |].
  unfold decodeDigits. cbn [fold_left].
  specialize (IH (10 * initial + digit - 48) ltac:(unfold decimalDigit in hd; lia)).
  unfold decodeDigits in IH. unfold decimalDigit in hd. lia.
Qed.
