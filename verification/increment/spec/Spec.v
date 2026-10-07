From CoqCP Require Import Options.

Definition required (program : nat -> nat) : Prop :=
  forall input, program input = S input.

Module Type SOLUTION.
  Parameter program : nat -> nat.
  Parameter correct : required program.
End SOLUTION.
