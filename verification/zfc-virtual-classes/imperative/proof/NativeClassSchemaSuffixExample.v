From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeClassSchemaExample NativeSetBudgetPlan NativeVerifiedDomain NativeVerifiedSuffixSession SeedBootstrap CommandQuit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeClassSchemaSuffixExample.
Import IndexExecution SipHashExecution.
Definition prefix := firstn 9 NativeClassSchemaExample.requests.
Lemma full_requests : prefix++[NativeSession.quit]=NativeClassSchemaExample.requests.
Proof. reflexivity. Qed.
Lemma prefix_shape : Forall Protocol.shape prefix.
Proof. pose proof NativeClassSchemaExample.requests_shape as H. rewrite <-full_requests in H. apply Forall_app in H. tauto. Qed.
Lemma prefix_positive : Forall(fun request=>Protocol.opcode request<>0%nat)prefix.
Proof. unfold prefix,NativeClassSchemaExample.requests,NativeClassSchemaExample.schema_name. repeat constructor;cbn [Protocol.opcode];discriminate. Qed.
Lemma prefix_capacity : NativeVerifiedDomain.within_capacity(prefix++[NativeSession.quit]).
Proof. rewrite full_requests. apply NativeVerifiedDomain.domain_iff. right. exact NativeClassSchemaExample.requests_capacity. Qed.
Theorem checked_session suffix bs ns :
 exists replies final logical,
 length replies=9%nat /\ nth_error replies 8=Some(Protocol.OK 0) /\
 Protocol.dialogue Protocol.initial NativeClassSchemaExample.requests (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\
 execObserved(funcdef_0__main bs ns)(SeedBootstrapExecution.initial 1 2(NativeSession.input prefix suffix)[],[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=Protocol.seed_bytes 1 2++NativeSession.input prefix suffix|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeSession.input prefix suffix|}]++
 NativeSession.schedule Protocol.handshake_output prefix replies suffix)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\
 stdin final=suffix /\ meta_value final 9=1 /\ meta_value final 8=0.
Proof.
 destruct(NativeVerifiedSuffixSession.generated_main 1 2 prefix suffix bs ns
   ltac:(unfold IndexExecution.maximum;lia) ltac:(unfold IndexExecution.maximum;lia) prefix_shape prefix_positive prefix_capacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Hrun & Hout & Hin & Hstop & Herror).
 rewrite full_requests in Hdialogue. assert(Hlen:length replies=9%nat) by exact Hlength.
 pose proof(NativeClassSchemaExample.dialogue_instantiates (replies++[Protocol.BYE]) logical [] Hdialogue) as Hreply.
 rewrite nth_error_app1 in Hreply by lia.
 exists replies,final,logical. repeat first[assumption|split].
Qed.
End NativeClassSchemaSuffixExample.
