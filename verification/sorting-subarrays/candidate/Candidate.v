From CoqCP Require Import Options.
From Submission Require Import Algorithm MainIO.
Require Trusted.Spec.

Module Implementation.
  Definition program : Trusted.Spec.Program := main Algorithm.program.
  Theorem correct : Trusted.Spec.required program.
  Proof. apply main_correct. exact Algorithm.correct. Qed.
End Implementation.
