From CoqCP Require Import Options.
From Submission Require Import Solver.
Require Trusted.Spec.

Module Implementation.
  Definition program := is_division_possible.
  Lemma correct : Trusted.Spec.required program.
  Proof. exact solution_is_correct. Qed.
End Implementation.
