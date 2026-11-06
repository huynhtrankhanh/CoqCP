From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import Spec Capacity ProofChecker.
From Submission Require Import AdversarialCapacityBridge.
Module Implementation.
Definition program := funcdef_0__main (fun x => match x with end) (fun x => match x with end).
Theorem correct : Trusted.Spec.required program (arrays _ environment1) Trusted.Capacity.Capacity.within_capacity.
Proof. exact AdversarialCapacityBridge.native_required. Qed.
End Implementation.
