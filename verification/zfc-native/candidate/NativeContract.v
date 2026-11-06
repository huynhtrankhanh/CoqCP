From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import Spec ProofChecker.
Definition native_contract capacity := Trusted.Spec.required
  (funcdef_0__main (fun x => match x with end) (fun x => match x with end))
  (arrays _ environment1) capacity.
