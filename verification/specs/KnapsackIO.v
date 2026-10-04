From CoqCP Require Import Options Imperative Execution Knapsack KnapsackCode KnapsackTable DecimalDigits.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.

Definition Program := Action
  (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.

(* Successful execution and the complete output stream, including newline,
   under the same arithmetic bounds as the existing end-to-end proof. *)
Definition required (program : Program) : Prop :=
  forall items limit,
    (tableSize items limit < 2^64)%nat ->
    (forall item, In item items -> (fst item < 2^32)%nat) ->
    (forall item, In item items -> (snd item < 2^32)%nat) ->
    (list_sum (map snd items) < 2^64)%nat ->
    exists final,
      exec program
        {| memory := arrays _ environment2;
           stdin := generateData items limit; stdout := [] |} = Some (tt, final) /\
      stdout final = decimalBytes (CoqCP.Knapsack.knapsack items limit) ++ [10%Z].

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
