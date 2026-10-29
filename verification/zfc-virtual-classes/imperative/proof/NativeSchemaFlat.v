From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte SchemaNodeTotal SchemaRepresentation
 NativeState NativeCommandBoundary NativeCommandStop ReadFive SchemaNode SchemaNodeRejection
 SchemaBasicRejectionProtocol SchemaReferenceRejection ReplyNO DecimalInput ReadNat ReadToken ReadFour ReadTwo ReadOne CommandInput SchemaNodeProtocol SchemaLiteralProtocol SchemaReferenceProtocol
 SchemaMetadata SchemaNodeCommand SchemaNodeMeaning ArenaFrame SemanticFrames Representation ClassStorage HistoryRefinement NameRepresentation.
From NativeProof Require Import NativeSchemaBoundary NativeGeneralCommandInvariant NativeBasicDispatcher NativeFullDispatcher CommandSchemaFrame NativeFullTapeStep SchemaGraph SchemaEvaluationSetRun SchemaEvaluationSetCell AxiomTaggedInvariant.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaFlat.
Import IndexExecution SipHashExecution.
Definition allowed (kind tag:nat) := In kind [0;1;2;4;5;6;8;9;11]%nat /\
 (kind=8%nat -> AxiomTaggedInvariant.uses_rename tag=false).
Definition check (kind tag:nat) := existsb (Nat.eqb kind) [0;1;2;4;5;6;8;9;11]%nat &&
 (negb(Nat.eqb kind 8) || negb(AxiomTaggedInvariant.uses_rename tag)).
Lemma check_spec kind tag : check kind tag=true <-> allowed kind tag.
Proof.
 unfold check,allowed. rewrite Bool.andb_true_iff. split.
 - intros [Hkind Htag]. split.
   + apply existsb_exists in Hkind as [value [Hin Heq]]. apply Nat.eqb_eq in Heq. now subst value.
   + intro Hkind8. subst kind. cbn [Nat.eqb negb] in Htag. now apply Bool.negb_true_iff.
 - intros [Hkind Htag]. split.
   + apply existsb_exists. exists kind. split;[exact Hkind|apply Nat.eqb_refl].
   + destruct(Nat.eq_dec kind 8%nat) as [->|Hother].
     * rewrite Nat.eqb_refl. cbn. apply Bool.negb_true_iff. now apply Htag.
     * rewrite(proj2(Nat.eqb_neq _ _) Hother). reflexivity.
Qed.
Definition raw_flat (raw:Z*Z*Z*Z*Z*Z*Z) :=
 let '(kind,tag,_,_,_,_,_):=raw in allowed (Z.to_nat kind) (Z.to_nat tag).
Definition flat (native:Machine) := forall node raw,
 nth_error(memory native arraydef_0__schemaNodes)node=Some raw -> raw_flat raw.
Definition request_allowed request := match Protocol.opcode request,Protocol.arguments request with
 | 22%nat,kind::tag::_=>allowed kind tag |22%nat,_=>False|_,_=>True end.
Definition request_check request := match Protocol.opcode request,Protocol.arguments request with
 | 22%nat,kind::tag::_=>check kind tag |22%nat,_=>false|_,_=>true end.
Lemma request_check_spec request : request_check request=true <-> request_allowed request.
Proof.
 unfold request_check,request_allowed. destruct(Nat.eq_dec(Protocol.opcode request)22%nat) as [H22|Hother].
 - rewrite H22. destruct(Protocol.arguments request) as [|kind [|tag rest]];try (split;[discriminate|contradiction]).
   apply check_spec.
 - destruct(Protocol.opcode request) as [|opcode];[tauto|].
   let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>destruct tag as [|tag];[try tauto;try contradiction|cases rest tag] end in cases 23%nat opcode.
   tauto.
Qed.
Lemma allowed_literal kind tag : (kind=1%nat \/ kind=2%nat \/ kind=11%nat) -> allowed kind tag.
Proof. intros [-> | [-> | ->]];unfold allowed;split;[cbn;tauto|discriminate|cbn;tauto|discriminate|cbn;tauto|discriminate]. Qed.
Lemma encoded_flat k a b c d expression : allowed k a ->
 raw_flat(SchemaRepresentation.encode k a b c d expression).
Proof. unfold raw_flat,SchemaRepresentation.encode. now rewrite !Nat2Z.id. Qed.
Lemma frame before after : memory after arraydef_0__schemaNodes=memory before arraydef_0__schemaNodes ->
 flat before -> flat after.
Proof. intros Hsame Hflat node raw Hlookup. apply(Hflat node raw). now rewrite <-Hsame. Qed.
Lemma result_flat native count raw : length(memory native arraydef_0__schemaNodes)=count ->
 flat native -> raw_flat raw -> flat(SchemaNode.result native count raw).
Proof.
 intros Hcount Hflat Hraw node value Hlookup. rewrite SchemaNode.result_nodes in Hlookup by exact Hcount.
 rewrite nth_error_app in Hlookup. destruct(node <? length(memory native arraydef_0__schemaNodes))%nat.
 - exact(Hflat _ _ Hlookup).
 - destruct(node-length(memory native arraydef_0__schemaNodes))%nat as [|index];cbn in Hlookup.
   + injection Hlookup as <-. exact Hraw.
   + destruct index;discriminate.
Qed.
Lemma variable_flat native logical variable b c d : NativeState.represents native logical -> flat native ->
 flat(SchemaNodeProtocol.variable_result native variable b c d(length(Protocol.expressions logical))).
Proof.
 intros Hstate Hflat. unfold SchemaNodeProtocol.variable_result. apply result_flat.
 - unfold SchemaNode.variable_state,SchemaNode.initialized. rewrite !store_meta_other by discriminate.
   exact(SchemaMetadata.represents_length native _ (proj1(NativeState.schema_representation _ _ Hstate))).
 - eapply frame;[|exact Hflat]. unfold SchemaNode.variable_state,SchemaNode.initialized.
   now rewrite !store_meta_other by discriminate.
 - unfold raw_flat,SchemaNodeProtocol.variable_raw,allowed. split;[cbn;tauto|discriminate].
Qed.
Lemma literal_flat native logical k a b c d expression : NativeState.represents native logical -> flat native ->
 allowed k a -> flat(SchemaLiteralProtocol.result native logical k a b c d expression).
Proof.
 intros Hstate Hflat Hallowed. unfold SchemaLiteralProtocol.result. apply result_flat.
 - unfold SchemaNode.initialized. rewrite !store_meta_other by discriminate.
   exact(SchemaMetadata.represents_length native _ (proj1(NativeState.schema_representation _ _ Hstate))).
 - eapply frame;[|exact Hflat]. unfold SchemaNode.initialized. now rewrite !store_meta_other by discriminate.
 - now apply encoded_flat.
Qed.
Lemma reference_flat native logical k a b c d expression : NativeState.represents native logical -> flat native ->
 allowed k a -> flat(SchemaReferenceProtocol.result native logical k a b c d expression).
Proof.
 intros Hstate Hflat Hallowed. unfold SchemaReferenceProtocol.result. apply result_flat.
 - rewrite SchemaNode.reference_other by discriminate.
   exact(SchemaMetadata.represents_length native _ (proj1(NativeState.schema_representation _ _ Hstate))).
 - eapply frame;[apply SchemaNode.reference_other;discriminate|exact Hflat].
 - now apply encoded_flat.
Qed.
Lemma argument_flat native ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail : flat native ->
 flat(ReadFive.fifth_state native ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail).
Proof. intro Hflat. eapply frame;[apply ReadFive.fifth_other;discriminate|exact Hflat]. Qed.
Lemma accepted_helper s logical kind a b c d expression observations :
 Protocol.builds_node logical [kind;a;b;c;d] expression ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 Z.of_nat (length (Protocol.expressions logical))<maximum -> NativeState.represents s logical ->
 flat s -> allowed kind a ->
 exists final, flat final /\
 execObserved (funcdef_0__schemaNode (fun _=>false)
   (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)))
   (s,observations)=Some(tt,(final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)));unreadInput:=stdin s|}])) /\
 stdin final=stdin s /\ stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical))) /\
 length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\ meta_value final 8=meta_value s 8.
Proof.
 intros Hbuild Hmeta Hprint Ha Hb Hc Hd Hcapacity Hstate Hbound Hallowed.
 pose proof Hstate as Hsource.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 assert (Hcount:meta_value s 16=Z.of_nat (length (Protocol.expressions logical))) by exact (proj1 (proj1 Hschemas)).
 assert (Hcases:kind=0%nat \/ (kind=1%nat \/ kind=2%nat \/ kind=11%nat) \/ (3<=kind<=10)%nat).
 { inversion Hbuild;subst;lia. }
 destruct Hcases as [Hzero|[Hliteral|Hrefs]].
 - subst kind. assert (Hsmall:Z.of_nat (S a)<=maximum).
   { assert (Hlt:Z.of_nat a<maximum) by (inversion Hbuild;subst;assumption). lia. }
   exists (SchemaNodeProtocol.variable_result s a b c d (length (Protocol.expressions logical))). split;[exact(variable_flat s logical a b c d Hsource Hbound)|]. split.
   + exact (SchemaNode.generated_variable s (fun _=>false)
       (SchemaNodeCommand.arguments 0 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))
       a (length (Protocol.expressions logical)) observations Hmeta eq_refl eq_refl Hsmall Hcount Hcapacity Hprint).
   + split;[unfold SchemaNodeProtocol.variable_result;rewrite SchemaNode.result_input;reflexivity|]. split.
     * unfold SchemaNodeProtocol.variable_result. rewrite SchemaNode.result_output. reflexivity.
     * split;[apply SchemaNodeProtocol.variable_meta_length|]. apply SchemaNodeProtocol.variable_meta_other;lia.
 - destruct (SchemaLiteralProtocol.generated_literal_helper s logical kind a b c d expression observations
     Hliteral Hbuild Hmeta Ha Hb Hc Hd Hcapacity Harena Hclasses Hhistory Hschemas Hprint) as [stored [Hentry Hhelper]].
   exists (SchemaLiteralProtocol.result s logical kind stored b c d expression). split;[exact(literal_flat s logical kind stored b c d expression Hsource Hbound (allowed_literal kind stored Hliteral))|]. split;[exact Hhelper|]. split.
   + unfold SchemaLiteralProtocol.result. rewrite SchemaNode.result_input. reflexivity.
   + split.
     * unfold SchemaLiteralProtocol.result. rewrite SchemaNode.result_output. reflexivity.
     * split;[apply SchemaLiteralProtocol.result_meta_length|]. apply SchemaLiteralProtocol.result_meta_other;lia.
 - destruct (SchemaNodeMeaning.reference_metadata s logical kind a b c d expression Hmeta Hbuild Hrefs)
     as [Hflag [Hwidth Htype]].
   pose proof (SchemaNode.generated_reference s (fun _=>false)
     (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))
     (Protocol.expressions logical) kind a b c d (length (Protocol.expressions logical)) observations
     Hmeta (proj1 Hschemas) eq_refl eq_refl eq_refl eq_refl eq_refl Hrefs ltac:(rewrite Hflag;lia)
     Hcount Hcapacity Hprint) as Hhelper.
   cbn zeta in Hhelper. rewrite Hwidth,Htype in Hhelper.
   exists (SchemaReferenceProtocol.result s logical kind a b c d expression). split;[exact(reference_flat s logical kind a b c d expression Hsource Hbound Hallowed)|]. split;[exact Hhelper|]. split.
   + unfold SchemaReferenceProtocol.result. rewrite SchemaNode.result_input. apply SchemaNode.reference_input.
   + split.
     * unfold SchemaReferenceProtocol.result. rewrite SchemaNode.result_output,SchemaNode.reference_output. reflexivity.
     * split;[apply SchemaReferenceProtocol.result_meta_length|]. apply SchemaReferenceProtocol.result_meta_other;lia.
Qed.
Theorem generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
 decimalBytes 22=ch::chars -> Guarantees.safe logical ->
 Protocol.builds_node logical [kind;a;b;c;d] expression ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 Z.of_nat (length (Protocol.expressions logical))<maximum -> NativeState.represents s logical ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
 stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
 flat s -> allowed kind a ->
 exists final, flat final /\ NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final
   (Protocol.OK (length (Protocol.expressions logical))) (SchemaRepresentation.with_expression logical expression).
Proof.
 intros Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound Hallowed.
 pose proof (NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof (NativeState.class_representation _ _ Hstate) as Hclasses.
 pose proof (NativeState.history_representation _ _ Hstate) as Hhistory.
 pose proof (NativeState.name_representation _ _ Hstate) as Hnames.
 pose proof (NativeState.schema_representation _ _ Hstate) as Hschemas.
 destruct (SchemaNodeTotal.generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations
   Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity
   Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput) as [final Hchecked].
 assert (Hkind:Z.of_nat kind<=maximum).
 { assert (Hsmall:(kind<=11)%nat) by (inversion Hbuild;subst;lia). unfold maximum;lia. }
 destruct (ReadFive.generated_reads s 22 ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
   ltac:(lia) Htoken Hprint Hpending Herror ltac:(unfold maximum;lia) Hencoding Hkind
   Ha Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput)
   as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hfifth & Hargbuffer & Hin & Hout).
 set (arg:=ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail).
 assert (Hargmeta:(19<length (memory arg arraydef_0__meta))%nat).
 { unfold arg. now rewrite ReadFive.fifth_meta_length. }
 assert (Hargstate:NativeState.represents arg logical) by (unfold arg;exact (NativeSchemaBoundary.argument_represents s logical ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail Hmeta Hstate)).
 destruct (accepted_helper arg logical kind a b c d expression observations Hbuild Hargmeta Hargbuffer
   Ha Hb Hc Hd Hcapacity Hargstate (argument_flat s ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail Hbound) Hallowed) as (expected & Hfields & Hhelper & Hfinalin & Hfinalout & Hfinalmeta & Hfinalerror).
 assert (Hexpectedmeta:(8<length (memory expected arraydef_0__meta))%nat) by lia.
 assert (Hexpectederror:meta_value expected 8=0).
 { rewrite Hfinalerror. unfold arg. rewrite ReadFive.fifth_meta_other by lia. exact Herror. }
 pose proof (SchemaNodeCommand.generated_command s bs ns _ _ _ _ _ arg expected (Z.of_nat kind) (Z.of_nat a)
   (Z.of_nat b) (Z.of_nat c) (Z.of_nat d) observations _ Hopcode Hfirst Hsecond Hthird Hfourth Hfifth Hhelper Hexpectedmeta Hexpectederror) as Hexpected.
 change (stdin arg=tail) in Hin. change (stdout arg=stdout s) in Hout. rewrite Hin,Hout in Hexpected.
 pose proof (proj1 Hchecked) as Hactual. assert (Heq:final=expected) by congruence. subst expected.
 assert (Houtcome:NativeSchemaBoundary.outcome logical kind a b c d (Protocol.OK (length (Protocol.expressions logical))) (SchemaRepresentation.with_expression logical expression)).
 { left. exists expression. repeat split;assumption || reflexivity. }
 exists final. split;[exact Hfields|]. exact (NativeSchemaBoundary.from_checked s logical bs ns ch chars kind a b c d sep0
   (decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail)
   tail observations final _ _ Hencoding Hmeta Htoken Hprint Hpending Herror Hsep0 Hinput Hchecked Houtcome
   (eq_trans Hfinalin Hin) (eq_trans Hfinalout (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)))) Hout))).
Qed.
Theorem generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
 decimalBytes 22=ch::chars -> Guarantees.safe logical ->
 (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat kind<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum ->
 Z.of_nat c<=maximum -> Z.of_nat d<=maximum -> NativeState.represents s logical ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
 stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
 flat s ->
 exists final, flat final /\ NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final Protocol.NO logical.
Proof.
 intros Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound.
 destruct (NativeSchemaBoundary.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
   Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput) as [final Hcomplete].
 pose proof (proj1(proj1 Hcomplete)) as Hactual.
 pose proof (NativeState.formula_representation _ _ Hstate) as Harena.
 pose proof (NativeState.class_representation _ _ Hstate) as Hclasses.
 pose proof (NativeState.history_representation _ _ Hstate) as Hhistory.
 pose proof (NativeState.name_representation _ _ Hstate) as Hnames.
 pose proof (NativeState.schema_representation _ _ Hstate) as Hschemas.
 assert (Hcases:SchemaBasicRejectionProtocol.basic kind \/ (3<=kind<=10)%nat).
 { unfold SchemaBasicRejectionProtocol.basic;lia. }
 exists final. split;[|exact Hcomplete].
 destruct Hcases as [Hbasic|Href].
 - destruct (SchemaBasicRejectionProtocol.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
       Hencoding Hbasic Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd
       Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput)
       as (expected & Hresult & Hrun & Hrest).
   assert (Heq:final=expected) by congruence. subst final expected.
   eapply frame;[rewrite SchemaBasicRejectionProtocol.result_other by discriminate;
      apply ReadFive.fifth_other;discriminate|exact Hbound].
 - destruct (SchemaReferenceRejection.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
       Hencoding Href Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd
       Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput)
       as (expected & Hresult & Hrun & Hrest).
   assert (Heq:final=expected) by congruence. subst final expected.
   eapply frame;[rewrite SchemaReferenceRejection.result_other by discriminate;
      apply ReadFive.fifth_other;discriminate|exact Hbound].
Qed.
Theorem generated_total s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
 decimalBytes 22=ch::chars -> Guarantees.safe logical ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 ->
 Z.of_nat kind<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum ->
 Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 Z.of_nat (length (Protocol.expressions logical))<maximum -> NativeState.represents s logical ->
 TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
 stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
 flat s -> allowed kind a ->
 exists final reply next, flat final /\ NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final reply next.
Proof.
 intros Hencoding Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound Hallowed.
 destruct (SchemaNodeTotal.builds_decidable s logical kind a b c d Hmeta Hsafe) as [[expression Hbuild]|Hnone].
 - destruct (generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations
     Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity Hstate
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound Hallowed) as [final Hcomplete].
   exists final,(Protocol.OK (length (Protocol.expressions logical))),(SchemaRepresentation.with_expression logical expression).
   exact Hcomplete.
 - destruct (generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
     Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hstate
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound) as [final Hcomplete].
   exists final,Protocol.NO,logical. exact Hcomplete.
Qed.
Theorem preserves native logical request bs ns tail observations final trace :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (19<length(memory native arraydef_0__meta))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 ->
 meta_value native 8=0 -> NativeState.represents native logical -> Guarantees.safe logical ->
 Z.of_nat(length(Protocol.expressions logical))<maximum ->
 flat native -> request_allowed request ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 flat final.
Proof.
 intros Hshape Hrange Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hroom Hfields Hallow Hinput Hactual.
 destruct (Nat.eq_dec (Protocol.opcode request) 22%nat) as [Hnode|Hother].
 - destruct request as [opcode args name]. cbn [Protocol.opcode] in Hnode. subst opcode.
   destruct Hshape as [Hwords Hformat]. change (length args=5%nat /\ name=[]) in Hformat.
   destruct Hformat as [Hlen ->].
   destruct args as [|kind args];[discriminate|]. destruct args as [|a args];[discriminate|].
   destruct args as [|b args];[discriminate|]. destruct args as [|c args];[discriminate|].
   destruct args as [|d args];[discriminate|]. destruct args as [|extra args];[|discriminate].
   cbn [Protocol.arguments] in Hwords.
   inversion Hwords as [|kind' rest Hkind W1];subst kind' rest.
   inversion W1 as [|a' rest Ha W2];subst a' rest.
   inversion W2 as [|b' rest Hb W3];subst b' rest.
   inversion W3 as [|c' rest Hc W4];subst c' rest.
   inversion W4 as [|d' rest Hd W5];subst d' rest.
   change(allowed kind a) in Hallow.
   change (meta_value native 15=51) in Hpending. rewrite NativeFullDispatcher.node_rest in Hinput.
   destruct (generated_total native logical bs ns 50 [50] kind a b c d 32 32 32 32 32 10 tail observations
     eq_refl Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hroom Hstate
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
     Hinput Hfields Hallow) as (expected & reply & next & HnextFields & Hcomplete).
   pose proof (proj1(proj1 Hcomplete)) as Hrun.
   assert (Hsame:final=expected) by congruence. now subst final.
 - destruct (NativeGeneralCommandInvariant.request_parts request Hshape Hrange)
     as (chars & sep & payload & Hencoding & Hsep & Hrest).
   eapply frame;[|exact Hfields].
   eapply NativeGeneralCommandInvariant.canonical_array with
     (opcode:=Protocol.opcode request) (ch:=NativeBasicDispatcher.first(Protocol.opcode request))
     (chars:=chars) (bs:=bs) (ns:=ns) (separator:=sep) (payload:=payload++tail)
     (observations:=observations) (trace:=trace);try eassumption;try discriminate.
   + exact (CommandSchemaFrame.nodes_ro (Protocol.opcode request) ltac:(lia) Hother).
   + lia.
   + rewrite Hinput,Hrest. now rewrite <-app_assoc.
Qed.
Lemma children_zero kind tag b c d child extra : allowed kind tag ->
 In(child,extra)(SchemaGraph.children_fields kind tag b c d) -> extra=0%nat.
Proof.
 intros [Hkind Htag] Hin.
 assert(Hall:Forall(fun edge=>snd edge=0%nat)(SchemaGraph.children_fields kind tag b c d)).
 { cbn in Hkind. destruct Hkind as [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | [Hk | []]]]]]]]]];subst kind.
   all:cbn [SchemaGraph.children_fields];try (repeat constructor;reflexivity).
   destruct(SchemaGraph.need_p tag), (SchemaGraph.need_q tag), (SchemaGraph.need_r tag);
     cbn;repeat constructor;reflexivity. }
 apply List.Forall_forall with (x:=(child,extra)) in Hall;[exact Hall|exact Hin].
Qed.
Lemma node_flat native node : flat native -> raw_flat(SchemaMetadata.node_at native node).
Proof.
 intro Hflat. unfold SchemaMetadata.node_at.
 destruct(nth_error(memory native arraydef_0__schemaNodes)node) as [raw|] eqn:Hlookup.
 - match goal with |- context[@List.nth ?A node ?entries ?zero]=>
    rewrite(List.nth_error_nth entries node zero Hlookup) end.
   exact(Hflat node raw Hlookup).
 - apply nth_error_None in Hlookup. rewrite nth_overflow by exact Hlookup.
   unfold raw_flat,allowed. split;[cbn;tauto|discriminate].
Qed.
Lemma reachable_depth native root node depth : flat native -> SchemaGraph.reachable native root node depth -> depth=0%nat.
Proof.
 intros Hflat Hreachable. induction Hreachable as [|parent depth child extra Hparent IH Hin];[reflexivity|].
 pose proof(node_flat native parent Hflat) as Hnode.
 unfold raw_flat in Hnode. unfold SchemaGraph.children in Hin.
 destruct(SchemaMetadata.node_at native parent) as [[[[[[kind tag] b] c] d] ty] ar].
 pose proof(children_zero (Z.to_nat kind)(Z.to_nat tag)(Z.to_nat b)(Z.to_nat c)(Z.to_nat d) child extra Hnode Hin).
 lia.
Qed.
Theorem fragment native root : flat native -> SchemaEvaluationSetRun.fragment native root.
Proof.
 intros Hflat node depth kind a b c d expression Hreachable Hlookup.
 pose proof(Hflat node _ Hlookup) as Hallowed.
 unfold raw_flat,SchemaRepresentation.encode in Hallowed. rewrite !Nat2Z.id in Hallowed.
 pose proof(reachable_depth native root node depth Hflat Hreachable) as Hdepth.
 destruct Hallowed as [Hkind Htag]. unfold SchemaEvaluationSetCell.supported. split.
 - cbn in Hkind. lia.
 - split;[intros Hzero;exact Hdepth|exact Htag].
Qed.
Lemma empty native : memory native arraydef_0__schemaNodes=[] -> flat native.
Proof. intros Hempty node raw Hlookup. rewrite Hempty in Hlookup. destruct node;discriminate. Qed.
Lemma input native bytes : flat native -> flat(withInput native bytes).
Proof. apply frame. reflexivity. Qed.
Lemma output native bytes : flat native -> flat(withOutput native bytes).
Proof. apply frame. reflexivity. Qed.
Lemma entered native request tail : flat native -> flat(NativeFullTapeStep.entered native request tail).
Proof. apply frame. apply NativeFullTapeStep.entered_arrays;discriminate. Qed.
End NativeSchemaFlat.
