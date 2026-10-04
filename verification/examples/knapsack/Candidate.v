From CoqCP Require Import Options Knapsack.
Require Trusted.Spec.

Module Implementation.
  Definition program := CoqCP.Knapsack.knapsack.
  Lemma correct : Trusted.Spec.required program.
  Proof. exact CoqCP.Knapsack.knapsackMax. Qed.
End Implementation.
