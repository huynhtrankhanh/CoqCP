From stdpp Require Import numbers list.
From CoqCP Require Import Options Imperative Knapsack KnapsackCode.
From Generated Require Import Knapsack.
From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma extractAnswerEq (items : list (nat * nat)) (limit : nat) (hp : ((limit + 1%nat) * (length items + 1%nat) <= 1000000%nat)%nat) (a32 : forall x, (fst (nth x items (0%nat,0%nat)) < 2^32)%nat) (b32 : forall x, (snd (nth x items (0%nat,0%nat)) < 2^32)%nat) : extractAnswer (start items limit) = Z.of_nat (knapsack items limit).
Proof.
  unfold start, invokeContract, state at 1. case_decide as uu; [| easy].
  fold state.
  unfold funcdef_0__main at 2. unfold getCommunicationSize.
  rewrite pushDispatch2 unfoldInvoke_S_GetCommunicationSize dataLength pushNumberSet.
  rewrite pushNumberGet2.
Admitted.