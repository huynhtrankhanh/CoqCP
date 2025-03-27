From stdpp Require Import numbers list.

Fixpoint knapsack (l : list (nat * nat)) (limit : nat) :=
  match l with
  | [] => 0
  | (weight, value) :: tail =>
    if decide (limit < weight) then knapsack tail limit
    else knapsack tail limit `max` (value + knapsack tail (limit - weight))
  end.

Fixpoint knapsack_elements (l : list (nat * nat)) (limit : nat) : list (nat * nat) :=
  match l with
  | [] => []
  | (weight, value) :: tail =>
    if decide (limit < weight) then knapsack_elements tail limit
    else
      let without := knapsack_elements tail limit in
      let with_item := (weight, value) :: knapsack_elements tail (limit - weight) in
      if decide ((fold_right (fun x acc => snd x + acc) 0 without) < (fold_right (fun x acc => snd x + acc) 0 with_item))
      then with_item
      else without
  end.

Compute knapsack_elements [(1,3); (2,5)] 9.