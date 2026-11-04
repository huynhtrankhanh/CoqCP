(* Appended to Spec.v only in the adversarial evaluator's frozen bundle.
   The manifest cannot replace either the generated program or its domain. *)
From Trusted Require Import Capacity ProofChecker.

Module Type SOLUTION.
  Definition program := funcdef_0__main
    (fun x => match x with end) (fun x => match x with end).
  Parameter correct : required program (arrays _ environment1) Capacity.within_capacity.
End SOLUTION.
