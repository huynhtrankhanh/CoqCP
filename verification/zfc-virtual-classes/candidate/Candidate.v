From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Submission Require Import Checker Elimination Regression ClassNames Arena NamedSessions.
Require Import Trusted.Reference.

Module Implementation.
  Definition program : Trusted.Reference.Step := step.
  Theorem correct_steps : Trusted.Reference.exact_step program.
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
  Theorem correct : Trusted.Reference.required program.
  Proof. split; [exact correct_steps |]. split; [exact correct_sessions |exact complete]. Qed.
End Implementation.

Module Checked : Trusted.Reference.SOLUTION := Implementation.
