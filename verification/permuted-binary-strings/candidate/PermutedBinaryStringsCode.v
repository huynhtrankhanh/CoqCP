From CoqCP Require Import Options Imperative Execution.
From Submission Require Import PermutedBinaryStrings.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Lemma small_coerce value width
  (hw : width = 8 \/ width = 64) (hv : 0 <= value <= 2048)
  (h8 : width = 8 -> value < 256) : coerceInt value width = value.
Proof.
  unfold coerceInt. apply Z.mod_small. split; [lia |].
  destruct hw as [-> | ->].
  - change (value < 256). apply h8. reflexivity.
  - assert (2048 < 2^64) by (vm_compute; reflexivity). lia.
Qed.

Definition queryNums (index weight : Z) : varsfuncdef_0__queryBit -> Z :=
  fun name => match name with
  | vardef_0__queryBit_index => index
  | vardef_0__queryBit_weight => weight
  end.

(* Verify the whole generated queryBit procedure, including its output byte. *)
Theorem generated_query_bit k x s b :
  execLocal funcdef_0__queryBit_body
    {| machine := s; bools := b; nums := queryNums (Z.of_nat x) (Z.of_nat (2^k)%nat) |} =
  Some (tt, {| machine := withOutput s (stdout s ++ [48 + Z.of_nat (bit k x)]);
               bools := b; nums := queryNums (Z.of_nat x) (Z.of_nat (2^k)%nat) |}).
Proof.
  unfold funcdef_0__queryBit_body.
  cbn [queryNums numberLocalGet bind execLocal localStep optionBind fst snd
    machine nums bools divIntUnsigned modIntUnsigned addInt writeChar].
  rewrite decide_False by (pose proof (power_positive k); lia).
  cbn [bind].
  rewrite decide_False by lia.
  rewrite <- Nat2Z.inj_div.
  replace (Z.of_nat (x / 2^k)%nat mod 2) with (Z.of_nat (bit k x))
    by (unfold bit; apply Nat2Z.inj_mod).
  cbn [bind].
  pose proof (bit_binary k x) as hb.
  rewrite (small_coerce _ 64) by (try (right; reflexivity); lia).
  rewrite (small_coerce _ 8) by (try (left; reflexivity); lia).
  reflexivity.
Qed.

Definition recordNums (index weight digit : Z) : varsfuncdef_0__recordBit -> Z :=
  fun name => match name with
  | vardef_0__recordBit_index => index
  | vardef_0__recordBit_weight => weight
  | vardef_0__recordBit_digit => digit
  end.

(* Bounds describe every intermediate value of a valid ten-round execution. *)
Theorem generated_record_bit (s : @Machine arrayIndex2 (arrayType _ environment2))
  b index weight digit old
  (hi : (index < length (memory s arraydef_0__answer))%nat)
  (hOld : nth index (memory s arraydef_0__answer) 0 = old)
  (hBounds : 0 <= old <= 1023 /\ 1 <= weight <= 512 /\ (digit = 0 \/ digit = 1)) :
  execLocal funcdef_0__recordBit_body
    {| machine := s; bools := b; nums := recordNums (Z.of_nat index) weight (48+digit) |} =
  Some (tt, {| machine := withMemory s
                (modifyArray (memory s) arraydef_0__answer index (old + digit*weight));
               bools := b; nums := recordNums (Z.of_nat index) weight (48+digit) |}).
Proof.
  unfold funcdef_0__recordBit_body.
  cbn [recordNums numberLocalGet bind execLocal localStep optionBind fst snd
    machine nums bools retrieve step addInt subInt multInt].
  rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length (memory s arraydef_0__answer)))) as [hIn | hOut];
    [| contradiction].
  rewrite nth_lt_default with (default := 0).
  change (@nth Z index (memory s arraydef_0__answer) 0 = old) in hOld.
  rewrite hOld.
  cbn [addInt subInt multInt numberLocalGet bind execLocal localStep
    optionBind fst snd machine nums bools setMachine recordNums].
  replace (48+digit-48) with digit by lia.
  rewrite (small_coerce digit 64) by (try (right; reflexivity); lia).
  rewrite (small_coerce (digit*weight) 64) by (try (right; reflexivity); lia).
  rewrite (small_coerce (old+digit*weight) 64) by (try (right; reflexivity); lia).
  cbn [bind store execLocal localStep optionBind fst snd step machine].
  rewrite Nat2Z.id, decide_True by exact hi.
  reflexivity.
Qed.

(* The generated update implements the induction step of decode_mod. *)
Theorem generated_decode_step k x index s b
  (hk : (k < 10)%nat) (hx : (x < 1000)%nat)
  (hi : (index < length (memory s arraydef_0__answer))%nat)
  (hOld : nth index (memory s arraydef_0__answer) 0 = Z.of_nat (decode k x)) :
  execLocal funcdef_0__recordBit_body
    {| machine := s; bools := b;
       nums := recordNums (Z.of_nat index) (Z.of_nat (2^k)%nat) (48+Z.of_nat (bit k x)) |} =
  Some (tt, {| machine := withMemory s (modifyArray (memory s)
                 arraydef_0__answer index (Z.of_nat (decode (S k) x)));
               bools := b;
               nums := recordNums (Z.of_nat index) (Z.of_nat (2^k)%nat) (48+Z.of_nat (bit k x)) |}).
Proof.
  assert (hp : (1 <= 2^k <= 512)%nat).
  { split; [pose proof (power_positive k); lia |].
    replace 512%nat with (2^9)%nat by reflexivity.
    apply Nat.pow_le_mono_r; lia. }
  assert (ho : (decode k x <= 1023)%nat).
  { rewrite decode_mod. pose proof (Nat.Div0.mod_le x (2^k)). lia. }
  pose proof (bit_binary k x) as hb.
  rewrite generated_record_bit with (old := Z.of_nat (decode k x)) by
    (try assumption; lia).
  cbn [decode]. rewrite Nat2Z.inj_add, Nat2Z.inj_mul. reflexivity.
Qed.

Print Assumptions generated_query_bit.
Print Assumptions generated_decode_step.
