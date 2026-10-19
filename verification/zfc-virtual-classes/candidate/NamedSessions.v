From CoqCP Require Import Options SetTheory VirtualClasses.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith.
From Submission Require Import Checker ClassNames.
Require Import Trusted.Spec.
Import ListNotations.

(* Reference refinement target for sessions which interleave ordinary proofs,
   undo/reset, immutable class declarations, and checked set certificates. *)
Module NamedSessions.
Definition state := (Trusted.Spec.state * ClassNames.registry)%type.
Definition initial : state := ([], ClassNames.empty).
Inductive command :=
| proof_command (c : Trusted.Spec.command)
| class_command (c : ClassNames.command).
Definition step (s : state) (c : command) : bool * state :=
  match c with
  | proof_command c => let '(accepted, proofs) := Checker.step (fst s) c in
      (accepted, (proofs, snd s))
  | class_command c => let '(accepted, registry) := ClassNames.step (fst s) (snd s) c in
      (accepted, (fst s, registry))
  end.
Definition safe (s : state) := Trusted.Spec.safe (fst s) /\ ClassNames.safe (snd s).
Theorem initial_safe : safe initial.
Proof. split; [constructor | apply ClassNames.empty_safe]. Qed.

Theorem step_safe s c : safe s -> safe (snd (step s c)).
Proof.
  intros [Hp Hc]. destruct c as [c | c]; cbn [step].
  - pose proof (Checker.step_safe (fst s) c Hp) as H.
    destruct (Checker.step (fst s) c) as [accepted proofs].
    cbn [fst snd] in H. split; assumption.
  - pose proof (ClassNames.step_safe (fst s) (snd s) c Hp Hc) as H.
    destruct (ClassNames.step (fst s) (snd s) c) as [accepted registry].
    cbn [fst snd] in H. split; assumption.
Qed.

Fixpoint run (s : state) (cs : list command) : state :=
  match cs with [] => s | c :: tail => run (snd (step s c)) tail end.
Fixpoint bounded_run (fuel : nat) (s : state) (cs : list command) : state :=
  match fuel, cs with
  | S fuel, c :: tail => bounded_run fuel (snd (step s c)) tail
  | _, _ => s
  end.

Theorem run_safe s cs : safe s -> safe (run s cs).
Proof.
  induction cs as [| c cs IH] in s |- *; cbn [run]; [tauto |].
  intro H. apply IH. now apply step_safe.
Qed.
Theorem bounded_run_prefix fuel s cs : bounded_run fuel s cs = run s (firstn fuel cs).
Proof.
  induction fuel as [| fuel IH] in s, cs |- *; [reflexivity |].
  destruct cs as [| c cs]; cbn [bounded_run firstn run]; [reflexivity | apply IH].
Qed.
Theorem bounded_run_safe fuel s cs : safe s -> safe (bounded_run fuel s cs).
Proof. rewrite bounded_run_prefix. apply run_safe. Qed.

Definition maximum_iterations := Z.to_nat (2 ^ 256).
Definition bounded_session := bounded_run maximum_iterations initial.
Theorem bounded_session_safe cs : safe (bounded_session cs).
Proof. apply bounded_run_safe. exact initial_safe. Qed.

Theorem named_set_certificate_is_a_theorem cs n cls :
  In (n, cls) (ClassNames.certified_sets (snd (bounded_session cs))) ->
  ClassNames.lookup n (ClassNames.definitions (snd (bounded_session cs))) = Some cls /\
  SetTheory.derives (ClassNames.is_set cls).
Proof. exact (proj2 (bounded_session_safe cs) n cls). Qed.

Theorem noncontradiction_if_consistent cs : SetTheory.consistent ->
  ~ In (VirtualClasses.core SetTheory.falsity) (fst (bounded_session cs)).
Proof.
  intros Hcon Hin. pose proof (proj1 (bounded_session_safe cs)) as Hsafe.
  apply Forall_forall with (x := VirtualClasses.core SetTheory.falsity) in Hsafe; [|exact Hin].
  exact (Hcon (Elimination.eliminate _ Hsafe)).
Qed.

(* The compiler emits exactly eight range(2^32) bounds. This arithmetic fact
   checks their product without constructing or traversing a unary 2^256 nat. *)
Theorem nested_iteration_budget :
  ((2 ^ 32) * (2 ^ 32) * (2 ^ 32) * (2 ^ 32) *
   (2 ^ 32) * (2 ^ 32) * (2 ^ 32) * (2 ^ 32) = 2 ^ 256)%Z.
Proof. reflexivity. Qed.
End NamedSessions.
