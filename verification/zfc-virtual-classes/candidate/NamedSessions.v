From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith.
From Submission Require Import Checker ClassNames.
Require Import Trusted.Reference.
Import ListNotations.

(* Reference refinement target for sessions which interleave ordinary proofs,
   undo/reset, immutable class declarations, and checked set certificates. *)
Module NamedSessions.
Definition state := (Trusted.Reference.state * ClassNames.registry)%type.
Definition initial : state := ([], ClassNames.empty).
Inductive command :=
| proof_command (c : Trusted.Reference.command)
| class_command (c : ClassNames.command).
Definition step (s : state) (c : command) : bool * state :=
  match c with
  | proof_command c => let '(accepted, proofs) := Checker.step (fst s) c in
      (accepted, (proofs, snd s))
  | class_command c => let '(accepted, registry) := ClassNames.step (fst s) (snd s) c in
      (accepted, (fst s, registry))
  end.
Definition safe (s : state) := Trusted.Reference.safe (fst s) /\ ClassNames.safe (snd s).
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
Theorem run_safe s cs : safe s -> safe (run s cs).
Proof.
  induction cs as [| c cs IH] in s |- *; cbn [run]; [tauto |].
  intro H. apply IH. now apply step_safe.
Qed.
Theorem named_set_certificate_is_a_theorem cs n cls :
  In (n, cls) (ClassNames.certified_sets (snd (run initial cs))) ->
  ClassNames.lookup n (ClassNames.definitions (snd (run initial cs))) = Some cls /\
  SetTheory.derives (ClassNames.is_set cls).
Proof. exact (proj2 (run_safe initial cs initial_safe) n cls). Qed.
End NamedSessions.
