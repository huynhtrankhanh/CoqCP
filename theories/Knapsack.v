From stdpp Require Import numbers list.

Fixpoint knapsack (l : nat * nat) (limit : nat) :=
  match l with
  | [] => 0
  | (weight, value) :: tail =>
    if decide (weight > limit) then knapsack tail limit
    else knapsack tail limit `max` value + knapsack tail (limit - weight)
  end.
