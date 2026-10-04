From CoqCP Require Import Options KnapsackEndToEnd.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
Require Trusted.Spec.

Module Implementation.
  Definition program : Trusted.Spec.Program :=
    funcdef_0__main (fun _ => false) (fun _ => 0%Z).
  Lemma correct : Trusted.Spec.required program.
  Proof. exact CoqCP.KnapsackEndToEnd.mainExecution. Qed.
End Implementation.
