From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module DecimalInput.
Import ReadNatExecution.
Fixpoint radix (fuel : nat) : Z := match fuel with O => 1 | S fuel => 10 * radix fuel end.
Lemma radix_positive fuel : 0 < radix fuel.
Proof. induction fuel as [|fuel IH]; cbn [radix]; lia. Qed.
Lemma number_append chars tail value : number_from value (chars ++ tail) = number_from (number_from value chars) tail.
Proof. induction chars as [|ch chars IH] in value |- *; [reflexivity|]. cbn [List.app number_from]. apply IH. Qed.
Lemma little_roundtrip fuel value : 0 <= value < radix fuel ->
  number_from 0 (reverse (littleDigits fuel value)) = value.
Proof.
  induction fuel as [|fuel IH] in value |- *.
  - change (0 <= value < 1 -> 0 = value). lia.
  - intro Hvalue. cbn [littleDigits]. case_decide as Hz.
    + subst value. reflexivity.
    + rewrite reverse_cons, number_append. cbn [number_from].
      assert (Hdiv : 0 <= value/10 < radix fuel).
      { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; cbn [radix] in Hvalue; lia]. }
      rewrite (IH (value/10) Hdiv).
      pose proof (Z.div_mod value 10 ltac:(lia)). lia.
Qed.
Lemma little_digit_bounds fuel value : 0 <= value ->
  Forall (fun ch => 48 <= ch <= 57) (littleDigits fuel value).
Proof.
  induction fuel as [|fuel IH] in value |- *; [constructor|].
  intro Hvalue. cbn [littleDigits]. case_decide; [constructor|]. constructor.
  - pose proof (Z.mod_pos_bound value 10 ltac:(lia)). lia.
  - apply IH. apply Z.div_pos; lia.
Qed.
Lemma little_length fuel value : (length (littleDigits fuel value) <= fuel)%nat.
Proof. induction fuel as [|fuel IH] in value |- *; [reflexivity|]. cbn [littleDigits]. case_decide; cbn [length]; [lia|]. specialize (IH (value/10)). lia. Qed.
Lemma decimal_word value : Z.of_nat value <= IndexExecution.maximum ->
  number_from 0 (decimalBytes value) = Z.of_nat value /\
  Forall (fun ch => 48 <= ch <= 57) (decimalBytes value) /\
  (0 < length (decimalBytes value) <= 20)%nat.
Proof.
  intro Hlimit. unfold decimalBytes. case_decide as Hz.
  - subst value. repeat split; try reflexivity; cbn [length]; try lia. constructor; [lia|constructor].
  - assert (Hpositive : 0 < Z.of_nat value) by lia.
    assert (Hvalue : 0 <= Z.of_nat value < radix 20).
    { change (0 <= Z.of_nat value < 100000000000000000000). unfold IndexExecution.maximum in Hlimit. lia. }
    split; [now apply little_roundtrip|]. split.
    + apply Forall_reverse. apply little_digit_bounds. lia.
    + rewrite length_reverse. split.
      * cbn [littleDigits]. case_decide; [lia|]. cbn [length]. lia.
      * apply little_length.
Qed.

Definition encoded_result s value tail := token_number (ReadTokenExecution.read_result s (decimalBytes value) tail) (decimalBytes value).
Theorem generated_readNat_encoded s bs ns value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  SipHashExecution.meta_value s 15 = 0 -> SipHashExecution.meta_value s 8 = 0 ->
  Z.of_nat value <= IndexExecution.maximum -> TokenByteExecution.separator sep ->
  stdin s = decimalBytes value ++ sep :: tail ->
  exec (funcdef_0__readNat bs ns) s = Some (tt,encoded_result s value tail).
Proof.
  intros Hmeta Htoken Hpending Herror Hlimit Hsep Hin.
  destruct (decimal_word value Hlimit) as [Hnumber [Hdigits Hlength]].
  apply (generated_readNat_none s bs ns (decimalBytes value) sep tail); try assumption.
  - lia.
  - now rewrite Hnumber.
Qed.
Theorem encoded_result_correct s value tail :
  (17 < length (memory s arraydef_0__meta))%nat -> Z.of_nat value <= IndexExecution.maximum ->
  SipHashExecution.meta_value (encoded_result s value tail) 11 = Z.of_nat value /\
  stdin (encoded_result s value tail) = tail /\ stdout (encoded_result s value tail) = stdout s.
Proof.
  intros Hmeta Hvalue. split.
  - unfold encoded_result. rewrite number_result_value.
    + exact (proj1 (decimal_word value Hvalue)).
    + rewrite ReadTokenExecution.result_meta_length. lia.
  - split; [reflexivity|]. unfold encoded_result, token_number. change
      (stdout (ReadTokenExecution.read_result s (decimalBytes value) tail) = stdout s).
    apply ReadTokenExecution.result_output.
Qed.
Theorem generated_readNat_encoded_observed s bs ns value sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  SipHashExecution.meta_value s 15 = 0 -> SipHashExecution.meta_value s 8 = 0 ->
  Z.of_nat value <= IndexExecution.maximum -> TokenByteExecution.separator sep ->
  stdin s = decimalBytes value ++ sep :: tail ->
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(encoded_result s value tail,observations)).
Proof. intros Hmeta Htoken Hpending Herror Hvalue Hsep Hin. apply generated_readNat_observed.
  now apply (generated_readNat_encoded s bs ns value sep tail). Qed.

Lemma encoded_meta_length s value tail :
  length (memory (encoded_result s value tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold encoded_result, token_number. now rewrite IndexExecution.store_meta_length, ReadTokenExecution.result_meta_length. Qed.
Lemma encoded_token_length s value tail :
  length (memory (encoded_result s value tail) arraydef_0__token) = length (memory s arraydef_0__token).
Proof.
  unfold encoded_result, token_number. rewrite IndexExecution.store_meta_other by discriminate.
  unfold ReadTokenExecution.read_result. rewrite IndexExecution.store_meta_other by discriminate. change
    (length (memory (IndexExecution.store_meta (ReadTokenExecution.put_many (ReadTokenExecution.reset s) 0 (decimalBytes value)) 17 1) arraydef_0__token) = length (memory s arraydef_0__token)).
  rewrite IndexExecution.store_meta_other by discriminate. now rewrite ReadTokenExecution.put_many_token_length, ReadTokenExecution.reset_token.
Qed.
Lemma encoded_meta_other s value tail i :
  (17 < length (memory s arraydef_0__meta))%nat ->
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 17%nat ->
  SipHashExecution.meta_value (encoded_result s value tail) i = SipHashExecution.meta_value s i.
Proof. intros Hm H6 H11 H14 H17. unfold encoded_result, token_number.
  rewrite SipHashExecution.meta_store_other by exact H11. now apply ReadTokenExecution.result_meta_other. Qed.
Lemma encoded_other s value tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (encoded_result s value tail) name = memory s name.
Proof. intros Hm Ht. unfold encoded_result, token_number. rewrite IndexExecution.store_meta_other by exact Hm.
  now apply ReadTokenExecution.result_other. Qed.
Theorem generated_readNat_encoded_pending s bs ns value ch chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  SipHashExecution.meta_value s 15 = ch+1 -> SipHashExecution.meta_value s 8 = 0 ->
  Z.of_nat value <= IndexExecution.maximum -> decimalBytes value = ch :: chars ->
  TokenByteExecution.separator sep -> stdin s = chars ++ sep :: tail ->
  exec (funcdef_0__readNat bs ns) s =
    Some (tt,token_number (ReadTokenExecution.pending_result s ch chars tail) (decimalBytes value)).
Proof.
  intros Hmeta Htoken Hpending Herror Hvalue Hencoding Hsep Hin.
  destruct (decimal_word value Hvalue) as [Hnumber [Hdigits Hlength]]. rewrite Hencoding in *.
  apply (generated_readNat_pending s bs ns ch chars sep tail); try assumption.
  - cbn [length] in Hlength. lia.
  - now rewrite Hnumber.
Qed.
End DecimalInput.


