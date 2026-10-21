From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash InternTail.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module TokenByteExecution.
Import IndexExecution SipHashExecution InternTailExecution.
Definition separator ch := ch = 32 \/ ch = 9 \/ ch = 10 \/ ch = 13.
Definition put_byte (s : Machine) size ch :=
  store_meta (withMemory s (modifyArray (memory s) arraydef_0__token size ch)) 6 (Z.of_nat (S size)).
Definition tick (s : Machine) size ch :=
  if bool_decide (separator ch) then
    if bool_decide (size = 0%nat) then s else store_meta s 17 1
  else if bool_decide (size = 1024%nat) then store_meta s 8 1 else put_byte s size ch.
Lemma byte_coerce ch : 0 <= ch < 256 -> coerceInt ch 8 = ch.
Proof. intro H. unfold coerceInt. apply Z.mod_small. exact H. Qed.

Theorem generated_tokenByte s bs ns size :
  (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value s 6 = Z.of_nat size -> (size <= 1024)%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  0 <= ns vardef_0__tokenByte_ch < 256 ->
  exec (funcdef_0__tokenByte bs ns) s = Some (tt,tick s size (ns vardef_0__tokenByte_ch)).
Proof.
  intros Hmeta Hsize Hlimit Htoken Hbyte.
  remember (ns vardef_0__tokenByte_ch) as ch eqn:Hch.
  change (@List.nth Z 6 (memory s arraydef_0__meta) 0 = Z.of_nat size) in Hsize.
  cbv beta iota zeta delta [memory] in Hmeta, Hsize, Htoken.
  destruct (Z.eq_dec ch 32), (Z.eq_dec ch 9), (Z.eq_dec ch 10), (Z.eq_dec ch 13);
    try congruence;
    destruct (Nat.eq_dec size 0), (Nat.eq_dec size 1024); try congruence.
  all: unfold funcdef_0__tokenByte; rewrite exec_eliminate; unfold funcdef_0__tokenByte_body, tick.
  all: repeat first [rewrite <- Hch |rewrite Hsize
    |rewrite nth_lt_default with (default := 0%Z)
    |rewrite byte_coerce by exact Hbyte
    |rewrite Nat2Z.id
    |rewrite modify_other by discriminate
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 17) with 17%nat by reflexivity
    |progress replace (Z.of_nat size + 1) with (Z.of_nat (S size)) by lia
    |match goal with |- context [coerceInt ?value 64] =>
      rewrite (coerce_word value) by (unfold word, maximum; lia) end
    |match goal with |- context [bool_decide ?P] =>
      first [rewrite (bool_decide_true P) by (unfold separator; lia)
        |rewrite (bool_decide_false P) by (unfold separator; lia)] end
    |progress cbv beta iota zeta delta [shortCircuitOr numberLocalGet numberLocalSet retrieve store addInt bind
      execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory]
    |match goal with |- context [decide (Nat.lt ?slot ?len)] =>
      let Hready := fresh "Hready" in
      assert (Hready : (slot < len)%nat) by lia;
      case_decide; [clear Hready|contradiction] end
  ].
  all: reflexivity.
Qed.
Lemma tick_io s size ch : stdin (tick s size ch) = stdin s /\ stdout (tick s size ch) = stdout s.
Proof. unfold tick. repeat case_bool_decide; split; reflexivity. Qed.
Lemma tick_other s size ch name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (tick s size ch) name = memory s name.
Proof.
  intros Hm Ht. unfold tick. repeat case_bool_decide; try reflexivity; try (now apply store_meta_other).
  unfold put_byte. rewrite store_meta_other by exact Hm. now apply modify_other.
Qed.
Lemma tick_meta_length s size ch : length (memory (tick s size ch) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof.
  unfold tick. repeat case_bool_decide; try reflexivity; try apply store_meta_length.
  unfold put_byte. rewrite store_meta_length. cbn [withMemory memory]. now rewrite modify_other by discriminate.
Qed.
Lemma tick_token_length s size ch : length (memory (tick s size ch) arraydef_0__token) = length (memory s arraydef_0__token).
Proof.
  unfold tick. repeat case_bool_decide; try reflexivity; try (now rewrite store_meta_other by discriminate).
  unfold put_byte. rewrite store_meta_other by discriminate. cbn [withMemory memory]. rewrite modify_same. apply length_insert.
Qed.
Lemma tick_meta_other s size ch i : i <> 6%nat -> i <> 8%nat -> i <> 17%nat ->
  meta_value (tick s size ch) i = meta_value s i.
Proof.
  intros H6 H8 H17. unfold tick. repeat case_bool_decide; try reflexivity;
    try (now apply meta_store_other).
  unfold put_byte. rewrite meta_store_other by exact H6. unfold meta_value. cbn [withMemory memory]. now rewrite modify_other by discriminate.
Qed.

Lemma tick_data s size ch : ~ separator ch -> (size < 1024)%nat -> tick s size ch = put_byte s size ch.
Proof. intros Hsep Hsize. unfold tick. rewrite bool_decide_false by exact Hsep. rewrite bool_decide_false by lia. reflexivity. Qed.
Lemma tick_separator s size ch : separator ch -> (0 < size)%nat -> tick s size ch = store_meta s 17 1.
Proof. intros Hsep Hsize. unfold tick. rewrite bool_decide_true by exact Hsep. rewrite bool_decide_false by lia. reflexivity. Qed.
Lemma put_byte_meta_other s size ch i : i <> 6%nat -> meta_value (put_byte s size ch) i = meta_value s i.
Proof. intro H. unfold put_byte. rewrite meta_store_other by exact H. unfold meta_value.
  cbn [withMemory memory]. now rewrite modify_other by discriminate. Qed.
Lemma put_byte_count s size ch : (6 < length (memory s arraydef_0__meta))%nat ->
  meta_value (put_byte s size ch) 6 = Z.of_nat (S size).
Proof. intro H. unfold put_byte. apply meta_store_same. cbn [withMemory memory]. now rewrite modify_other by discriminate. Qed.
Lemma put_byte_token s size ch : memory (put_byte s size ch) arraydef_0__token = <[size := ch]> (memory s arraydef_0__token).
Proof. unfold put_byte. rewrite store_meta_other by discriminate. apply modify_same. Qed.
Lemma put_byte_input s size ch input : put_byte (withInput s input) size ch = withInput (put_byte s size ch) input.
Proof. reflexivity. Qed.
Lemma tick_input s size ch input : tick (withInput s input) size ch = withInput (tick s size ch) input.
Proof. unfold tick. repeat case_bool_decide; reflexivity. Qed.
End TokenByteExecution.
