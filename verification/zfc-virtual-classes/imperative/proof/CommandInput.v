From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput TokenFrame ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandInput.
Import IndexExecution SipHashExecution.
Definition parsed s ch chars tail :=
  ReadNatExecution.token_number (ReadTokenExecution.pending_result s ch chars tail) (ch :: chars).
Lemma parsed_meta_length s ch chars tail :
  length (memory (parsed s ch chars tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold parsed, ReadNatExecution.token_number.
  now rewrite store_meta_length, ReadTokenExecution.pending_meta_length. Qed.
Lemma parsed_other s ch chars tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (parsed s ch chars tail) name = memory s name.
Proof. intros Hm Ht. unfold parsed, ReadNatExecution.token_number.
  rewrite store_meta_other by exact Hm. now apply TokenFrame.pending_other. Qed.
Lemma parsed_meta_other s ch chars tail i :
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (parsed s ch chars tail) i = meta_value s i.
Proof. intros H6 H11 H14 H15 H17. unfold parsed, ReadNatExecution.token_number.
  rewrite meta_store_other by exact H11. now apply TokenFrame.pending_meta_other. Qed.
Lemma parsed_input s ch chars tail : stdin (parsed s ch chars tail) = tail.
Proof. reflexivity. Qed.
Lemma parsed_output s ch chars tail : stdout (parsed s ch chars tail) = stdout s.
Proof. unfold parsed, ReadNatExecution.token_number. change
  (stdout (ReadTokenExecution.pending_result s ch chars tail) = stdout s).
  apply TokenFrame.pending_output. Qed.
Lemma parsed_valid s ch chars tail :
  (17 < length (memory s arraydef_0__meta))%nat -> meta_value (parsed s ch chars tail) 14 = 1.
Proof. intro Hmeta. unfold parsed, ReadNatExecution.token_number.
  rewrite meta_store_other by lia. now apply ReadTokenExecution.pending_valid. Qed.
Lemma parsed_number s value ch chars tail :
  (17 < length (memory s arraydef_0__meta))%nat -> Z.of_nat value <= maximum ->
  decimalBytes value = ch :: chars -> meta_value (parsed s ch chars tail) 11 = Z.of_nat value.
Proof.
  intros Hmeta Hvalue Hencoding. unfold parsed. rewrite ReadNatExecution.number_result_value.
  - pose proof (proj1 (DecimalInput.decimal_word value Hvalue)) as Hnumber.
    rewrite Hencoding in Hnumber. exact Hnumber.
  - rewrite ReadTokenExecution.pending_meta_length. lia.
Qed.
Lemma parsed_storage s ch chars tail : ArenaFrame.storage s (parsed s ch chars tail).
Proof. split; [apply parsed_meta_length|]. split; [intros; now apply parsed_other|].
  repeat split; apply parsed_meta_other; lia. Qed.
Theorem generated_pending s bs ns value ch chars sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 -> Z.of_nat value <= maximum ->
  decimalBytes value = ch :: chars -> TokenByteExecution.separator sep -> stdin s = chars ++ sep :: tail ->
  execObserved (funcdef_0__readNat bs ns) (s,observations) =
    Some (tt,(parsed s ch chars tail,observations)).
Proof.
  intros Hmeta Htoken Hpending Herror Hvalue Hencoding Hsep Hin.
  apply ReadNatExecution.generated_readNat_observed.
  pose proof (DecimalInput.generated_readNat_encoded_pending s bs ns value ch chars sep tail
    Hmeta Htoken Hpending Herror Hvalue Hencoding Hsep Hin) as Hrun.
  rewrite Hencoding in Hrun. exact Hrun.
Qed.
End CommandInput.
