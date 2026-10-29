From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker NativeContract.
From NativeProof Require Import NativeBudgetPlan NativeGeneralSession.

Module NativeContractVerified.
(** The exact public contract for the generated entry point and initial
    arrays, with the closed finite arithmetic domain used by the proof. *)
Theorem required : native_contract NativeBudgetPlan.domain.
Proof.
 exact(NativeGeneralSession.required (fun variable=>match variable with end)
  (fun variable=>match variable with end)).
Qed.
End NativeContractVerified.
