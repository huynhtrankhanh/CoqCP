From CoqCP Require Import Options.
From stdpp Require Import numbers.

Definition is_positive (x : nat) : Prop :=
  x >= 1.

Record input_w : Type := {
  value : nat;
  constraints : 1 <= value <= 100
}.

Definition valid_division (w1 w2 : nat) (total_weight : input_w) : Prop :=
  is_positive w1
  /\ is_positive w2
  /\ Nat.Even w1
  /\ Nat.Even w2
  /\ ((w1 + w2) = (value total_weight)).

Definition required (program : input_w -> bool) : Prop :=
  forall weight, program weight <-> exists a b, valid_division a b weight.

Module Type SOLUTION.
  Parameter program : input_w -> bool.
  Parameter correct : required program.
End SOLUTION.
