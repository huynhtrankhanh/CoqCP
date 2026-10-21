From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput CommandInput ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandArgs.
Import IndexExecution SipHashExecution.
Lemma pending_cleared s ch chars tail :
  (17 < length (memory s arraydef_0__meta))%nat -> meta_value (CommandInput.parsed s ch chars tail) 15 = 0.
Proof.
  intro Hmeta. unfold CommandInput.parsed, ReadNatExecution.token_number, ReadTokenExecution.pending_result.
  rewrite !meta_store_other by lia. change
    (meta_value (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.started s ch) 1 chars) 17 1) 15 = 0).
  rewrite meta_store_other by lia. rewrite ReadTokenExecution.put_many_meta_other by lia.
  unfold ReadTokenExecution.started. apply meta_store_same.
  rewrite ReadTokenExecution.put_meta_length, ReadTokenExecution.reset_length. lia.
Qed.
Lemma pending_token_length s ch chars tail :
  length (memory (CommandInput.parsed s ch chars tail) arraydef_0__token) = length (memory s arraydef_0__token).
Proof. unfold CommandInput.parsed, ReadNatExecution.token_number. rewrite store_meta_other by discriminate.
  apply ReadTokenExecution.pending_token_length. Qed.
Lemma encoded_valid s value tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (DecimalInput.encoded_result s value tail) 14 = 1.
Proof. intro Hmeta. unfold DecimalInput.encoded_result, ReadNatExecution.token_number.
  rewrite meta_store_other by lia. now apply ReadTokenExecution.result_valid. Qed.
Lemma encoded_storage s value tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (DecimalInput.encoded_result s value tail).
Proof.
  intro Hmeta. split; [apply DecimalInput.encoded_meta_length|]. split; [intros; now apply DecimalInput.encoded_other|].
  repeat split; apply DecimalInput.encoded_meta_other; try exact Hmeta; lia.
Qed.
End CommandArgs.
