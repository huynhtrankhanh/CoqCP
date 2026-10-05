From CoqCP Require Import Options Imperative Execution InteractiveExecution
  PermutedBinaryStrings PermutedBinaryStringsProtocol.
From Generated Require Import PermutedBinaryStrings.

Definition Program := Action
  (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.

(* Bind the certificate to the actual generated entry point. Both success and
   every interactive boundary belong to the evaluator-owned requirement. *)
Definition required (candidate : Program) : Prop :=
  candidate = CoqCP.PermutedBinaryStringsProtocol.program /\
  forall n a, valid n a ->
    endToEnd candidate (initial a) (outputBytes a) (flushes a).

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
