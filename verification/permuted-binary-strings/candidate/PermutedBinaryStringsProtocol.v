From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.

From Submission Require Import PermutedBinaryStrings.
Require Export Trusted.Spec.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia Sorting.Permutation.
Open Scope Z_scope.

(* The specified input bytes are the grader's permutation of the query digits,
   encoded as ASCII, rather than an unconstrained oracle transcript. *)
Lemma replyBytes_truthful n a k (h : valid n a) :
  replyBytes a k =
  map (fun x => 48 + Z.of_nat (nth (x-1) (query n k) 0%nat)) a ++ [10].
Proof.
  pose proof (response_is_permuted_query n a k h) as truthful.
  apply (f_equal (map (fun b => 48 + Z.of_nat b))) in truthful.
  unfold response in truthful. rewrite !map_map in truthful.
  unfold replyBytes, bitBytes. rewrite truthful. reflexivity.
Qed.
