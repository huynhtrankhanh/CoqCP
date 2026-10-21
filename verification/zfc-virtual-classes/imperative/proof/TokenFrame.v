From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash InternTail TokenByte ReadToken.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module TokenFrame.
Import IndexExecution SipHashExecution ReadTokenExecution TokenByteExecution.
Lemma pending_other s ch chars tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (pending_result s ch chars tail) name = memory s name.
Proof.
  intros Hmeta Htoken. unfold pending_result. rewrite store_meta_other by exact Hmeta.
  change (memory (store_meta (put_many (started s ch) 1 chars) 17 1) name = memory s name).
  rewrite store_meta_other by exact Hmeta. rewrite put_many_other by assumption.
  unfold started, put_byte. rewrite !store_meta_other by exact Hmeta.
  change (modifyArray (memory (reset s)) arraydef_0__token 0 ch name = memory s name).
  rewrite InternTailExecution.modify_other by exact Htoken.
  unfold reset. now rewrite !store_meta_other by exact Hmeta.
Qed.
Lemma pending_meta_other s ch chars tail i : i <> 6%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (pending_result s ch chars tail) i = meta_value s i.
Proof.
  intros H6 H14 H15 H17. unfold pending_result. rewrite meta_store_other by exact H14.
  change (meta_value (store_meta (put_many (started s ch) 1 chars) 17 1) i = meta_value s i).
  rewrite meta_store_other by exact H17. rewrite put_many_meta_other by exact H6.
  unfold started. rewrite meta_store_other by exact H15. rewrite put_byte_meta_other by exact H6.
  unfold reset. now rewrite !meta_store_other by assumption.
Qed.
Lemma pending_input s ch chars tail : stdin (pending_result s ch chars tail) = tail.
Proof. reflexivity. Qed.
Lemma pending_output s ch chars tail : stdout (pending_result s ch chars tail) = stdout s.
Proof. unfold pending_result. change (stdout (put_many (started s ch) 1 chars) = stdout s).
  rewrite put_many_output. reflexivity. Qed.
End TokenFrame.
