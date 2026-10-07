From stdpp Require Import numbers list.
From CoqCP Require Import DecimalEncoding Optimality ArrayExecution.
From CoqCP Require Import Options Imperative Execution DecimalDigits.
From Submission Require Import Knapsack KnapsackCode KnapsackTable KnapsackEndToEnd.
From Generated Require Import Knapsack.

(* The theorem covers the generated competitive program, from decimal input
   through dynamic allocation to the decimal answer and its final newline. *)
Lemma extractAnswerEq (items : list (nat * nat)) (limit : nat)
  (hSize : ((length items + 1) * (limit + 1) < 2^64)%nat)
  (hWeights : forall item, In item items -> (fst item < 2^32)%nat)
  (hValues : forall item, In item items -> (snd item < 2^32)%nat)
  (hSum : (list_sum (map snd items) < 2^64)%nat) :
  extractAnswer (start items limit) = Z.of_nat (knapsack items limit).
Proof.
  destruct (mainExecution items limit hSize hWeights hValues hSum) as [state [executed output]].
  unfold start, runProgram. rewrite exec_runProgram, executed.
  cbn [optionBind fst snd extractAnswer]. rewrite output.
  rewrite take_app_length'; [| rewrite length_app; cbn [length]; lia].
  change (decodeDigits (decimalBytes (knapsack items limit)) 0%Z = Z.of_nat (knapsack items limit)).
  apply decimalBytes_decode. pose proof (knapsack_sum items limit). lia.
Qed.

Example competitiveKnapsackExample : extractAnswer (start [(2, 3); (3, 4); (4, 5)]%nat 5%nat) = 7%Z.
Proof. vm_compute. reflexivity. Qed.

Example competitiveKnapsackEmpty : extractAnswer (start [] 0%nat) = 0%Z.
Proof. vm_compute. reflexivity. Qed.
