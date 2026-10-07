From CoqCP Require Import Options.
From CoqCP Require Import DecimalEncoding Optimality ArrayExecution.
From Submission Require Import Knapsack KnapsackEndToEnd.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
Require Trusted.Spec.

Module Implementation.
  Definition program : Trusted.Spec.Program :=
    funcdef_0__main (fun _ => false) (fun _ => 0%Z).
  Lemma correct : Trusted.Spec.required program.
  Proof.
    split; [reflexivity |]. intros items limit hSize hWeights hValues hSum.
    destruct (mainExecution items limit hSize hWeights hValues hSum)
      as [final [executed output]].
    exists final, (knapsack items limit). split; [exact executed |].
    split; [apply knapsackMax | exact output].
  Qed.
End Implementation.
