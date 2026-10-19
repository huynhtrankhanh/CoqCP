From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From stdpp Require Import numbers list.
From Trusted Require Export Protocol.

(* Primary contract: actual byte-stream execution, termination, logical command
   semantics, seed handshake, exact replies, residual input and every flush.
   Capacity is a trusted domain bound, fixed outside the submitted program.
   No property here assumes that execution succeeds. *)
Definition required {I : Type} {T : I -> Type} `{EqDecision I}
  (program : Action (WithArrays I T) withArraysReturnValue unit)
  (initial_memory : forall name, list (T name))
  (within_capacity : list Protocol.request -> Prop) :=
  Protocol.required program initial_memory within_capacity.
