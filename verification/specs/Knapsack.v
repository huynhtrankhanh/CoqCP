From CoqCP Require Import Options Knapsack.
From stdpp Require Import numbers list.

(* This contract concerns a Gallina solver. It does not claim verification
   of emitted C++ or of a byte-stream input/output frontend. *)
Definition required (program : list (nat * nat) -> nat -> nat) : Prop :=
  forall items limit,
    CoqCP.Knapsack.isMaximum (program items limit)
      (fun value => exists choice,
        sublist choice items /\
        fold_right (fun item acc => snd item + acc) 0 choice = value /\
        fold_right (fun item acc => fst item + acc) 0 choice <= limit).

Module Type SOLUTION.
  Parameter program : list (nat * nat) -> nat -> nat.
  Parameter correct : required program.
End SOLUTION.
