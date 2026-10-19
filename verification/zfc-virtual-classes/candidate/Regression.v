From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
From Stdlib Require Import Lists.List.
From Submission Require Import Checker.
Require Import Trusted.Spec.
Import ListNotations SetTheory VirtualClasses.

Example empty_reference_rejected :
  step [] (submit (core falsity) (reference 0)) = (false, []).
Proof. reflexivity. Qed.
Example wrong_claim_rejected :
  step [] (submit (core falsity) (axiom_use (Refl 0))) = (false, []).
Proof. reflexivity. Qed.
Example mismatched_mp_rejected :
  step [] (submit (core falsity)
    (modus_ponens (axiom_use (K falsity (equal 0 0))) (axiom_use (Refl 0)))) = (false, []).
Proof. reflexivity. Qed.
Example non_implication_mp_rejected :
  step [] (submit (core falsity)
    (modus_ponens (axiom_use (Refl 0)) (axiom_use (Refl 0)))) = (false, []).
Proof. reflexivity. Qed.
Example valid_mp_accepted :
  step [] (submit (core (implies falsity (equal 0 0)))
    (modus_ponens (axiom_use (K (equal 0 0) falsity)) (axiom_use (Refl 0)))) =
      (true, [core (implies falsity (equal 0 0))]).
Proof. reflexivity. Qed.
Example generalization_accepted :
  step [] (submit (universal (core (equal 0 0))) (generalize (axiom_use (Refl 0)))) =
    (true, [universal (core (equal 0 0))]).
Proof. reflexivity. Qed.
Example reference_restatement :
  step [core (all (equal 0 0))]
    (submit (universal (core (equal 0 0))) (reference 0)) =
    (true, [universal (core (equal 0 0)); core (all (equal 0 0))]).
Proof. reflexivity. Qed.
Example reference_is_newest_first :
  step [core (equal 0 0); core (equal 1 1)] (submit (core (equal 0 0)) (reference 1)) =
    (false, [core (equal 0 0); core (equal 1 1)]).
Proof. reflexivity. Qed.
Example rejection_preserves_history :
  step [core (equal 0 0)] (submit (core falsity) (reference 0)) =
    (false, [core (equal 0 0)]).
Proof. reflexivity. Qed.
Example empty_undo_rejected : step [] undo = (false, []).
Proof. reflexivity. Qed.
Example undo_preserves_previous_theorems :
  step [core (equal 0 0); core (equal 1 1)] undo = (true, [core (equal 1 1)]).
Proof. reflexivity. Qed.
Example reset_clears_history : step [core (equal 0 0)] reset = (true, []).
Proof. reflexivity. Qed.

Example class_universe_membership_accepted :
  let p := class_member (set 5) (abstract (core (equal 0 0))) in
  step [] (submit p (axiom_use (Refl 5))) = (true, [p]).
Proof. reflexivity. Qed.
Example abstraction_avoids_capture :
  erase (class_member (set 1) (abstract (universal (core (member 1 2))))) =
    all (member 2 1).
Proof. reflexivity. Qed.
Example russell_class_is_a_predicate :
  erase (class_member (set 3) (abstract (core (neg (member 0 0))))) =
    neg (member 3 3).
Proof. reflexivity. Qed.
Example nested_classes_eliminate :
  erase (class_member (set 2)
    (abstract (class_member (set 0) (abstract (core (equal 0 0)))))) = equal 2 2.
Proof. reflexivity. Qed.
Example proper_class_membership_requires_a_set_witness :
  erase (class_member (abstract (core (equal 0 0))) (abstract (core (equal 0 0)))) =
    ex (conj (all (iff (member 0 1) (equal 0 0))) (equal 0 0)).
Proof. reflexivity. Qed.
Example set_class_equality_is_set_equality :
  erase (class_equal (set 0) (set 1)) = equal 0 1.
Proof. reflexivity. Qed.

(* Replacement and Separation allow arbitrary parameterized formulas. *)
Example separation_parameters_shift :
  separation (member 0 3) = ex (all
    (iff (member 0 1) (conj (member 0 2) (member 0 4)))).
Proof. reflexivity. Qed.
Example replacement_parameters_shift :
  rename repl_left (implies (member 0 1) (member 1 4)) =
    implies (member 2 1) (member 1 5).
Proof. reflexivity. Qed.
