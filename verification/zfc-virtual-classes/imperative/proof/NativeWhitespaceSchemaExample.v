From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeClassSchemaExample NativeFastDomain NativeWhitespaceDialogue
 NativeGeneralWhitespaceDialogue NativeGeneralWhitespaceQuitDialogue NativeAllWhitespaceDialogue CommandQuit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceSchemaExample.
Import IndexExecution SipHashExecution NativeGeneralWhitespaceDialogue.
Definition frames := map (fun request=>([9],request)) (firstn 9 NativeClassSchemaExample.requests).
Lemma requests_match : map snd frames++[NativeSession.quit]=NativeClassSchemaExample.requests.
Proof. reflexivity. Qed.
Lemma frame_count : length frames=9%nat.
Proof. reflexivity. Qed.
Lemma frames_valid : Forall valid frames.
Proof.
 apply Forall_forall. intros item Hin. unfold frames in Hin. apply list_elem_of_In in Hin.
 apply in_map_iff in Hin as [request [Hitem Hin]]. subst item.
 unfold valid. cbn [fst snd]. split.
 - apply (proj1 (@List.Forall_forall Protocol.request Protocol.shape NativeClassSchemaExample.requests) NativeClassSchemaExample.requests_shape request).
   rewrite <-(firstn_skipn 9 NativeClassSchemaExample.requests). apply in_or_app. now left.
 - split.
   + unfold NativeClassSchemaExample.requests in Hin. cbn [firstn List.In] in Hin.
     repeat match type of Hin with _ \/ _=>destruct Hin as [Hin|Hin];[subst request;discriminate|] end. contradiction.
   + constructor;[unfold TokenByteExecution.separator;tauto|constructor].
Qed.
Lemma capacity : NativeFastDomain.within_capacity (map snd frames++[NativeSession.quit]).
Proof. rewrite requests_match. vm_compute. reflexivity. Qed.
Theorem checked_session bs ns :
 exists replies final logical,
 length replies=9%nat /\ nth_error replies 8=Some(Protocol.OK 0) /\
 Protocol.dialogue Protocol.initial NativeClassSchemaExample.requests (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate 1 2 [9] [13] 32 10
   (NativeGeneralWhitespaceQuitDialogue.wire frames [9] [120]),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=[9]++decimalBytes 1++32::([13]++decimalBytes 2++10::NativeGeneralWhitespaceQuitDialogue.wire frames [9] [120])|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeGeneralWhitespaceQuitDialogue.wire frames [9] [120]|}]++
 NativeGeneralWhitespaceQuitDialogue.schedule frames replies [9] [120] Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=[120].
Proof.
 destruct(NativeAllWhitespaceDialogue.quit 1%nat 2%nat [9] [13] 32 10 frames [9] [120] bs ns
  ltac:(unfold maximum;lia) ltac:(unfold maximum;lia)
  ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
  ltac:(repeat constructor;unfold TokenByteExecution.separator;tauto)
  ltac:(repeat constructor;unfold TokenByteExecution.separator;tauto)
  frames_valid ltac:(repeat constructor;unfold TokenByteExecution.separator;tauto) capacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hstop & Hrun & Hout & Hin).
 rewrite requests_match in Hdialogue. pose proof(NativeClassSchemaExample.dialogue_instantiates (replies++[Protocol.BYE]) logical [] Hdialogue) as Hreply.
 assert(Hnine:length replies=9%nat) by (rewrite Hlength;exact frame_count).
 rewrite nth_error_app1 in Hreply by lia.
 exists replies,final,logical. repeat first [assumption|split].
Qed.
End NativeWhitespaceSchemaExample.
