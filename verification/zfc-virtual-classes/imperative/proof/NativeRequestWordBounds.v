From CoqCP Require Import Options.
From Trusted Require Import Protocol.
From NativeProof Require Import NativeRequestBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeRequestWordBounds.
Lemma numbers_word values limit : 0<=limit -> Forall(fun value=>Z.of_nat value<=limit)values ->
 Z.of_nat(NativeRequestBounds.numbers_max values)<=limit.
Proof.
 intros Hzero Hvalues. induction Hvalues as [|value values Hvalue Hvalues IH];cbn [NativeRequestBounds.numbers_max];[exact Hzero|].
 rewrite Nat2Z.inj_max. apply Z.max_lub;assumption.
Qed.
Lemma requests_word requests limit : 0<=limit ->
 Forall(fun request=>Forall(fun value=>Z.of_nat value<=limit)(Protocol.arguments request))requests ->
 Z.of_nat(NativeRequestBounds.maximum requests)<=limit.
Proof.
 intros Hzero Hrequests. induction Hrequests as [|request requests Hrequest Hrequests IH];cbn [NativeRequestBounds.maximum];[exact Hzero|].
 rewrite Nat2Z.inj_max. apply Z.max_lub;[now apply numbers_word|exact IH].
Qed.
Theorem shaped_requests requests : Forall Protocol.shape requests ->
 Z.of_nat(NativeRequestBounds.maximum requests)<=Protocol.maximum.
Proof.
 intro Hshape. apply requests_word;[unfold Protocol.maximum;lia|].
 eapply Forall_impl;[exact Hshape|]. intros request Hrequest. exact(proj1 Hrequest).
Qed.
End NativeRequestWordBounds.
