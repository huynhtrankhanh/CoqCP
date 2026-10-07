From CoqCP Require Import Options.

Definition isMaximum (x : nat) (predicate : nat -> Prop) :=
  predicate x /\ forall y, predicate y -> y <= x.
