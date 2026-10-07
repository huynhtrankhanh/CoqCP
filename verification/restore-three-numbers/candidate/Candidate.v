From CoqCP Require Import Options.
From Submission Require Import Solver.
Require Trusted.Spec.

Module Implementation.
  Definition program := restore_a_b_c_aux.
  Lemma correct : Trusted.Spec.required program.
  Proof.
    intros input a b c bounds.
    exact (solution_is_correct {| value := input; inner_a := a; inner_b := b;
      inner_c := c; constraints := bounds |}).
  Qed.
End Implementation.
