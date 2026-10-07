From CoqCP Require Import Options Imperative Execution DecimalEncoding Optimality.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.

Definition Program := Action
  (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.
Definition tableSize (items : list (nat * nat)) limit :=
  ((length items + 1) * (limit + 1))%nat.
Definition generateData (items : list (nat * nat)) (limit : nat) : list Z :=
  decimalBytes (length items) ++ [32%Z] ++ decimalBytes limit ++ [10%Z] ++
  concat (map (fun item => decimalBytes (fst item) ++ [32%Z] ++
    decimalBytes (snd item) ++ [10%Z]) items).
Definition optimal items limit value :=
  isMaximum value (fun value => exists choice,
    sublist choice items /\
    fold_right (fun item acc => snd item + acc) 0 choice = value /\
    fold_right (fun item acc => fst item + acc) 0 choice <= limit).

(* Successful generated-main execution and an optimal answer, with no solver
   recurrence or execution proof on the specification side. *)
Definition required (program : Program) : Prop :=
  program = funcdef_0__main (fun _ => false) (fun _ => 0%Z) /\
  forall items limit,
    (tableSize items limit < 2^64)%nat ->
    (forall item, In item items -> (fst item < 2^32)%nat) ->
    (forall item, In item items -> (snd item < 2^32)%nat) ->
    (list_sum (map snd items) < 2^64)%nat ->
    exists final value,
      exec program {| memory := arrays _ environment2;
        stdin := generateData items limit; stdout := [] |} = Some (tt, final) /\
      optimal items limit value /\ stdout final = decimalBytes value ++ [10%Z].

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
