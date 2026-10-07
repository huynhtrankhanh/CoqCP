From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From Generated Require Import PermutedBinaryStrings.
From stdpp Require Import numbers list.
From Stdlib Require Import Sorting.Permutation.
Local Open Scope nat_scope.

Definition bit (k x : nat) := (x / 2^k) mod 2.

Definition query (n k : nat) := map (bit k) (seq 0 n).

Definition response (a : list nat) (k : nat) := map (fun x => bit k (x-1)) a.

Definition valid (n : nat) (a : list nat) :=
  1 <= n <= 1000 /\ Permutation a (seq 1 n).

Open Scope Z_scope.
Definition bitBytes k a := map (fun x => 48 + Z.of_nat (bit k (x-1))) a.
Definition queryBytes n k := [63;32] ++ map (fun i => 48+Z.of_nat (bit k i)) (seq 0 n) ++ [10].
Definition replyBytes a k := bitBytes k a ++ [10].
Definition answerBytes a := [33] ++ concat (map (fun x => 32 :: decimalBytes x) a) ++ [10].


Fixpoint roundInputs a k fuel := match fuel with
  | O => [] | S fuel => replyBytes a k ++ roundInputs a (S k) fuel end.
Fixpoint roundOutputs n k fuel := match fuel with
  | O => [] | S fuel => queryBytes n k ++ roundOutputs n (S k) fuel end.
Fixpoint roundSnapshots a k fuel output tail := match fuel with
  | O => []
  | S fuel => {| flushedOutput := output ++ queryBytes (length a) k;
                unreadInput := replyBytes a k ++ roundInputs a (S k) fuel ++ tail |} ::
      roundSnapshots a (S k) fuel (output ++ queryBytes (length a) k) tail
  end.

Definition inputBytes a := decimalBytes (length a) ++ 10 :: roundInputs a 0 10.
Definition outputBytes a := roundOutputs (length a) 0 10 ++ answerBytes a.
Definition flushes a := roundSnapshots a 0 10 [] [] ++
  [{| flushedOutput := outputBytes a; unreadInput := [] |}].
Definition initial a : @Machine arrayIndex2 (arrayType _ environment2) :=
  {| memory := arrays _ environment2; stdin := inputBytes a; stdout := [] |}.
Definition program := funcdef_0__main (fun _ => false) (fun _ => 0).



Definition Program := Action
  (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.

(* Complete truthful interactive transcript, including all flush boundaries. *)
Definition required (candidate : Program) : Prop :=
  candidate = program /\
  forall n a, valid n a ->
    endToEnd candidate (initial a) (outputBytes a) (flushes a).

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
