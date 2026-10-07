From CoqCP Require Import Options.
From Stdlib Require Import Lists.List ZArith.ZArith Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

Definition valid_input_list(l : list Z) (a b c : Z) : Prop :=
  (forall x, In x l -> 2 <= x <= 1000000000)
  /\ (a >= 1)
  /\ (b >= 1)
  /\ (c >= 1)
  /\ Permutation [a + b; a + c; b + c; a + b + c] l.

Definition required (program : list Z -> list Z) : Prop :=
  forall input a b c, valid_input_list input a b c ->
    Permutation (program input) [a; b; c].

Module Type SOLUTION.
  Parameter program : list Z -> list Z.
  Parameter correct : required program.
End SOLUTION.
