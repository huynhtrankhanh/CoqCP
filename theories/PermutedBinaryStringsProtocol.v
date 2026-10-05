(* Protocol data and the generated entry point, independent of the execution proof. *)
From CoqCP Require Import Options Imperative Execution InteractiveExecution KnapsackCode PermutedBinaryStrings.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia Sorting.Permutation.
Open Scope Z_scope.

Definition bitBytes k a := map (fun x => 48 + Z.of_nat (bit k (x-1))) a.
Definition queryBytes n k := [63;32] ++ map (fun i => 48+Z.of_nat (bit k i)) (seq 0 n) ++ [10].
Definition replyBytes a k := bitBytes k a ++ [10].
Definition answerBytes a := [33] ++ concat (map (fun x => 32 :: decimalBytes x) a) ++ [10].


Fixpoint roundInputs a k fuel := match fuel with
  | O => [] | S fuel => replyBytes a k ++ roundInputs a (S k) fuel end.
Fixpoint roundOutputs n k fuel := match fuel with
  | O => [] | S fuel => queryBytes n k ++ roundOutputs n (S k) fuel end.
Fixpoint roundSnapshots a k fuel output tail := match fuel with
  | O => []
  | S fuel => {| flushedOutput := output ++ queryBytes (length a) k;
                unreadInput := replyBytes a k ++ roundInputs a (S k) fuel ++ tail |} ::
      roundSnapshots a (S k) fuel (output ++ queryBytes (length a) k) tail
  end.

Definition inputBytes a := decimalBytes (length a) ++ 10 :: roundInputs a 0 10.
Definition outputBytes a := roundOutputs (length a) 0 10 ++ answerBytes a.
Definition flushes a := roundSnapshots a 0 10 [] [] ++
  [{| flushedOutput := outputBytes a; unreadInput := [] |}].
Definition initial a : @Machine arrayIndex2 (arrayType _ environment2) :=
  {| memory := arrays _ environment2; stdin := inputBytes a; stdout := [] |}.
Definition program := funcdef_0__main (fun _ => false) (fun _ => 0).


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
