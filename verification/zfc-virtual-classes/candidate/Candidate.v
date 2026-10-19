From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Submission Require Import Checker Elimination Regression Model ConstructibleModel ClassNames Arena NamedSessions.
Require Import Trusted.Spec.

Module Implementation.
  Definition program : Trusted.Spec.Step := step.
  Theorem correct_steps : Trusted.Spec.exact_step program.
  Proof. exact step_exact. Qed.
  Theorem correct_sessions :
    forall s cs, safe s -> safe (run program s cs).
  Proof. exact session_safe. Qed.
  Theorem complete : forall p,
    VirtualClasses.proves p <-> exists cs, List.In p (run program nil cs).
  Proof. exact reachable_iff_provable. Qed.
  Theorem classes_conservative : forall p,
    VirtualClasses.proves p <-> SetTheory.derives (VirtualClasses.erase p).
  Proof. exact conservative. Qed.
  Theorem classes_equiconsistent :
    VirtualClasses.consistent <-> SetTheory.consistent.
  Proof. exact equiconsistent. Qed.
  Theorem noncontradiction_obligation :
    (forall cs, ~ List.In (VirtualClasses.core SetTheory.falsity) (run program nil cs))
      <-> SetTheory.consistent.
  Proof. exact checker_consistency_iff. Qed.
  Theorem full_contract_obligation :
    Trusted.Spec.required program <-> SetTheory.consistent.
  Proof. exact full_contract_iff. Qed.

  (* SOLUTION.correct remains unprovided. The frozen gate must reject this
     module until unconditional noncontradiction is actually proved. *)
End Implementation.
