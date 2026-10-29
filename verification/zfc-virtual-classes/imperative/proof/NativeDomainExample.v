From CoqCP Require Import Options.
From NativeProof Require Import NativeVerifiedDomain NativeClassSchemaExample.

Module NativeDomainExample.
Theorem class_schema_capacity :
 NativeVerifiedDomain.within_capacity NativeClassSchemaExample.requests.
Proof. vm_compute. reflexivity. Qed.
End NativeDomainExample.
