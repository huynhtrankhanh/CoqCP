From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte NativeState NativeSession NativeClassSchemaExample NativeFastDomain NativeWhitespaceDialogue
 NativeWhitespaceSchemaArguments NativeWhitespaceSchemaMixedGeneral NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaQuitGeneral NativeWhitespaceSchemaQuitDialogue CommandQuit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSpacedClassSchemaExample.
Import IndexExecution SipHashExecution NativeWhitespaceSchemaSpacedGeneral NativeWhitespaceSchemaMixedGeneral.
Definition items : list item :=
 map (fun request=>([9],canonical request)) (firstn 8 NativeClassSchemaExample.requests) ++
 [([13],schema [([9],0%nat);([13;9],1%nat)] NativeClassSchemaExample.schema_name [9;13] 9 [13] 32 10)].
Lemma requests_match : map req items++[NativeSession.quit]=NativeClassSchemaExample.requests.
Proof. reflexivity. Qed.
Lemma item_count : length items=9%nat.
Proof. reflexivity. Qed.
Lemma items_valid : Forall valid_item items.
Proof.
 unfold items. apply Forall_app. split.
 - apply Forall_forall. intros entry Hin. apply list_elem_of_In in Hin.
   apply in_map_iff in Hin as [request [Hentry Hin]]. subst entry.
   cbn [valid_item fst snd valid]. split.
   + repeat constructor;unfold TokenByteExecution.separator;tauto.
   + split.
     * apply (proj1 (@List.Forall_forall Protocol.request Protocol.shape NativeClassSchemaExample.requests) NativeClassSchemaExample.requests_shape request).
       rewrite <-(firstn_skipn 8 NativeClassSchemaExample.requests). apply in_or_app. now left.
     * unfold NativeClassSchemaExample.requests in Hin. cbn [firstn List.In] in Hin.
       repeat match type of Hin with _ \/ _=>destruct Hin as [Hin|Hin];[subst request;discriminate|] end. contradiction.
 - repeat first [solve [reflexivity] | solve [unfold TokenByteExecution.separator;tauto]
     | solve [unfold maximum,Protocol.maximum;cbn;lia]
     | progress cbn [valid_item valid fst snd Protocol.shape Protocol.opcode Protocol.arguments Protocol.object_name Protocol.valid_name NativeClassSchemaExample.schema_name length map]
     | split | constructor].
Qed.
Lemma capacity : NativeFastDomain.within_capacity (map req items++[NativeSession.quit]).
Proof. rewrite requests_match. vm_compute. reflexivity. Qed.
Theorem checked_session bs ns :
 exists replies final logical,
 length replies=9%nat /\ nth_error replies 8=Some(Protocol.OK 0) /\
 Protocol.dialogue Protocol.initial NativeClassSchemaExample.requests (replies++[Protocol.BYE]) logical [] /\
 Guarantees.safe logical /\ NativeState.represents final logical /\ meta_value final 8=0 /\ meta_value final 9=1 /\
 execObserved(funcdef_0__main bs ns)(NativeWhitespaceDialogue.alternate 1 2 [9] [13] 32 10
   (NativeWhitespaceSchemaQuitGeneral.wire items [9] [120]),[])=
 Some(tt,(final,
 [{|flushedOutput:=Protocol.seed_prompt;unreadInput:=[9]++decimalBytes 1++32::([13]++decimalBytes 2++10::NativeWhitespaceSchemaQuitGeneral.wire items [9] [120])|};
  {|flushedOutput:=Protocol.handshake_output;unreadInput:=NativeWhitespaceSchemaQuitGeneral.wire items [9] [120]|}]++
 NativeWhitespaceSchemaQuitGeneral.schedule items replies [9] [120] Protocol.handshake_output)) /\
 stdout final=NativeSession.output Protocol.handshake_output replies++CommandQuitExecution.bye_bytes /\ stdin final=[120].
Proof.
 destruct(NativeWhitespaceSchemaQuitDialogue.quit 1%nat 2%nat [9] [13] 32 10 items [9] [120] bs ns
  ltac:(unfold maximum;lia) ltac:(unfold maximum;lia)
  ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
  ltac:(repeat constructor;unfold TokenByteExecution.separator;tauto)
  ltac:(repeat constructor;unfold TokenByteExecution.separator;tauto)
  items_valid ltac:(repeat constructor;unfold TokenByteExecution.separator;tauto) capacity)
 as(replies & final & logical & Hlength & Hdialogue & Hsafe & Hstate & Herror & Hstop & Hrun & Hout & Hin).
 rewrite requests_match in Hdialogue. pose proof(NativeClassSchemaExample.dialogue_instantiates (replies++[Protocol.BYE]) logical [] Hdialogue) as Hreply.
 assert(Hnine:length replies=9%nat) by (rewrite Hlength;exact item_count).
 rewrite nth_error_app1 in Hreply by lia.
 exists replies,final,logical. repeat first [assumption|split].
Qed.
End NativeSpacedClassSchemaExample.
