From CoqCP Require Import Options.
From Trusted Require Import Protocol.
From NativeProof Require Import NativeFastDomain NativeClassSchemaExample.
From Stdlib Require Import Lists.List.
Import ListNotations.
Module NativeFastExample.
Definition requests := Protocol.Req 6 [0] [] :: NativeClassSchemaExample.requests.
Theorem bounded_rejection : NativeFastDomain.check requests = false.
Proof. vm_compute. reflexivity. Qed.
End NativeFastExample.
