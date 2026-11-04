From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker NativeContract.
From Trusted Require Import Protocol Spec Capacity CapacityGeneral CapacitySet.
From NativeProof Require Import AdversarialGeneralCapacityBridge AdversarialSetCapacityBridge NativeVerifiedDomain.
Module AdversarialCapacityBridge.
Theorem domain requests : Capacity.within_capacity requests <-> NativeVerifiedDomain.within_capacity requests.
Proof.
 unfold Capacity.within_capacity. rewrite AdversarialGeneralCapacityBridge.domain,AdversarialSetCapacityBridge.domain.
 symmetry. apply NativeVerifiedDomain.domain_iff.
Qed.
Theorem native_required : native_contract Capacity.within_capacity.
Proof.
 unfold native_contract. intros key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity.
 apply domain in Hcapacity.
 exact (NativeVerifiedDomain.required (fun variable=>match variable with end) (fun variable=>match variable with end)
  key0 key1 requests Hkey0 Hkey1 Hshape Hcapacity).
Qed.
End AdversarialCapacityBridge.
