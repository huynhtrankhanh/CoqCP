From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Stdlib Require Import Lists.List Bool.Bool.
Import ListNotations SetTheory VirtualClasses.

Definition state := list statement.
Inductive certificate :=
| axiom_use (a : axiom)
| reference (index : nat)
| modus_ponens (implication_proof antecedent_proof : certificate)
| generalize (proof : certificate).

(* An independent declarative judgment; references are zero based, newest
   first. Inference checks the antecedent, not just the consequent. *)
Inductive judges (s : state) : certificate -> formula -> Prop :=
| j_axiom a : judges s (axiom_use a) (axiom_formula a)
| j_reference n p : nth_error s n = Some p -> judges s (reference n) (erase p)
| j_mp ci ca p q : judges s ci (implies p q) -> judges s ca p ->
    judges s (modus_ponens ci ca) q
| j_generalize c p : judges s c p -> judges s (generalize c) (all p).

Inductive command :=
| submit (claim : statement) (proof : certificate)
| undo
| reset.
Inductive transition : state -> command -> state -> Prop :=
| t_submit s p c : judges s c (erase p) -> transition s (submit p c) (p :: s)
| t_undo p s : transition (p :: s) undo s
| t_reset s : transition s reset [].

Definition safe s := Forall proves s.
Definition Step := state -> command -> bool * state.
Fixpoint run (step : Step) (s : state) (commands : list command) : state :=
  match commands with [] => s | c :: cs => run step (snd (step s c)) cs end.
Definition exact_step (step : Step) :=
  forall s c, let result := step s c in
    (fst result = true -> transition s c (snd result)) /\
    (fst result = false -> snd result = s /\ forall t, ~ transition s c t) /\
    (forall t, transition s c t -> result = (true, t)).

(* Keep the requested unconditional obligation in the frozen signature. No
   consistency or model premise is allowed on this field. *)
Definition required (program : Step) :=
  exact_step program /\
  (forall s cs, safe s -> safe (run program s cs)) /\
  (forall p, proves p <-> exists cs, In p (run program [] cs)) /\
  (VirtualClasses.consistent <-> SetTheory.consistent) /\
  (forall cs, ~ In (core falsity) (run program [] cs)).

Module Type SOLUTION.
  Parameter program : Step.
  Parameter correct : required program.
End SOLUTION.
