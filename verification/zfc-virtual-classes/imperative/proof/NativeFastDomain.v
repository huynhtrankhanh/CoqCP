From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker NativeContract.
From Trusted Require Import Protocol Spec.
From NativeProof Require Import NativeRequestBounds NativeBudgetPlan NativeSetBudgetPlan NativeVerifiedDomain BoundedIteration.
From Stdlib Require Import Bool.Bool.
Module NativeFastDomain.
Definition check requests :=
 if NativeSetBudgetPlan.check NativeSetBudgetPlan.initial requests then true else
 let N:=NativeRequestBounds.maximum requests in
 BoundedIteration.fast_check N (NativeBudgetPlan.initial N) requests.
Definition within_capacity requests := check requests=true.
Lemma check_exact requests : check requests=NativeVerifiedDomain.check requests.
Proof.
 unfold check,NativeVerifiedDomain.check. destruct (NativeSetBudgetPlan.check NativeSetBudgetPlan.initial requests);[reflexivity|].
 apply BoundedIteration.fast_check_exact.
Qed.
Theorem domain_exact requests : within_capacity requests <-> NativeVerifiedDomain.within_capacity requests.
Proof. unfold within_capacity,NativeVerifiedDomain.within_capacity. now rewrite check_exact. Qed.
Theorem required bs ns : Spec.required (funcdef_0__main bs ns) (arrays _ environment1) within_capacity.
Proof.
 intros key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity.
 apply domain_exact in Hcapacity.
 exact (NativeVerifiedDomain.required bs ns key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity).
Qed.
Theorem native_required : native_contract within_capacity.
Proof. exact (required (fun variable=>match variable with end) (fun variable=>match variable with end)). Qed.
End NativeFastDomain.
