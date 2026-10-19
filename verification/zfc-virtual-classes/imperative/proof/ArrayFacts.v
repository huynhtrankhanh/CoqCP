From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ArrayFacts.
Import IndexExecution.
Lemma nth_insert_other {A} (xs : list A) i j value default :
  i <> j -> List.nth i (<[j := value]> xs) default = List.nth i xs default.
Proof.
  induction xs as [|x xs IH] in i, j |- *; [destruct i, j; reflexivity |].
  destruct i as [|i], j as [|j]; cbn; try reflexivity; [congruence |].
  intro H. apply IH. congruence.
Qed.
Lemma full_flag s : (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 8 (memory (store_meta s 8 1) arraydef_0__meta) 0 = 1.
Proof.
  intro H. unfold store_meta. cbn [withMemory memory]. rewrite modify_meta.
  now apply OverflowExecution.nth_insert_same.
Qed.
End ArrayFacts.
