From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker NativeContract.
From Trusted Require Import Protocol Spec.
From NativeProof Require Import NativeRequestBounds NativeBudgetPlan NativeSetBudgetPlan NativeGeneralSession NativeSetSchemaSession.
From Stdlib Require Import Bool.Bool.

Module NativeVerifiedDomain.
(** Both plans are finite Boolean computations over the supplied request list.
    The flat set-schema plan adds at most 42 times the square of the schema
    arena size per instantiation, including actual class-metavariable examples. *)
Definition check requests :=
 if NativeSetBudgetPlan.check NativeSetBudgetPlan.initial requests then true else
 NativeBudgetPlan.check (NativeRequestBounds.maximum requests)
   (NativeBudgetPlan.initial (NativeRequestBounds.maximum requests)) requests.
Definition within_capacity requests := check requests=true.
Lemma domain_iff requests : within_capacity requests <->
 NativeBudgetPlan.domain requests \/ NativeSetBudgetPlan.domain requests.
Proof. unfold within_capacity,check,NativeBudgetPlan.domain,NativeSetBudgetPlan.domain. destruct (NativeSetBudgetPlan.check NativeSetBudgetPlan.initial requests) eqn:Hset; cbn; intuition congruence. Qed.
Theorem required bs ns :
 Spec.required (funcdef_0__main bs ns) (arrays _ environment1) within_capacity.
Proof.
 intros key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity.
 apply domain_iff in Hcapacity. destruct Hcapacity as [Hgeneral|Hsets].
 - exact (NativeGeneralSession.required bs ns key0 key1 requests Hkey0 Hkey1 Hshape Hgeneral).
 - exact (NativeSetSchemaSession.required bs ns key0 key1 requests Hkey0 Hkey1 Hshape Hsets).
Qed.
Theorem native_required : native_contract within_capacity.
Proof.
 exact (required (fun variable=>match variable with end) (fun variable=>match variable with end)).
Qed.
End NativeVerifiedDomain.
