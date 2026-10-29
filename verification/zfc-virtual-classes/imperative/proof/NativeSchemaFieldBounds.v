From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte SchemaNodeTotal SchemaRepresentation
 NativeState NativeCommandBoundary NativeCommandStop ReadFive SchemaNode SchemaNodeRejection
 SchemaBasicRejectionProtocol SchemaReferenceRejection ReplyNO DecimalInput ReadNat ReadToken ReadFour ReadTwo ReadOne CommandInput SchemaNodeProtocol SchemaLiteralProtocol SchemaReferenceProtocol
 SchemaMetadata SchemaNodeCommand SchemaNodeMeaning ArenaFrame SemanticFrames Representation ClassStorage HistoryRefinement NameRepresentation.
From NativeProof Require Import NativeSchemaBoundary NativeGeneralCommandInvariant NativeBasicDispatcher NativeFullDispatcher CommandSchemaFrame SchemaUniformBudget.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaFieldBounds.
Import IndexExecution SipHashExecution.

Definition raw_bound (cap:nat) (raw:Z*Z*Z*Z*Z*Z*Z) :=
 let '(_,_,b,c,d,_,_):=raw in
 (Z.to_nat b<=cap /\ Z.to_nat c<=cap /\ Z.to_nat d<=cap)%nat.
Definition fields (native:Machine) cap := forall node raw,
 nth_error (memory native arraydef_0__schemaNodes) node=Some raw -> raw_bound cap raw.
Lemma fields_frame native final cap :
 memory final arraydef_0__schemaNodes=memory native arraydef_0__schemaNodes ->
 fields native cap -> fields final cap.
Proof. intros Hsame Hbound node raw Hlookup. apply (Hbound node raw). now rewrite <-Hsame. Qed.
Lemma fields_mono native lower upper : (lower<=upper)%nat -> fields native lower -> fields native upper.
Proof. intros Hle Hbound node [[[[[[k a] b] c] d] ty] ar] Hlookup.
 specialize (Hbound _ _ Hlookup). unfold raw_bound in *. lia. Qed.
Lemma encoded_bound cap k a b c d expression :
 (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 raw_bound cap (SchemaRepresentation.encode k a b c d expression).
Proof. intros Hb Hc Hd. unfold raw_bound,SchemaRepresentation.encode. now rewrite !Nat2Z.id. Qed.
Lemma result_fields native count raw cap :
 length (memory native arraydef_0__schemaNodes)=count ->
 fields native cap -> raw_bound cap raw -> fields (SchemaNode.result native count raw) cap.
Proof.
 intros Hcount Hbound Hraw node value Hlookup. rewrite SchemaNode.result_nodes in Hlookup by exact Hcount.
 rewrite nth_error_app in Hlookup.
 destruct (node <? length(memory native arraydef_0__schemaNodes))%nat.
 - exact (Hbound _ _ Hlookup).
 - destruct (node-length(memory native arraydef_0__schemaNodes))%nat as [|index];cbn in Hlookup.
   + injection Hlookup as <-. exact Hraw.
   + destruct index;discriminate.
Qed.
Lemma variable_fields native logical variable b c d cap :
 NativeState.represents native logical -> fields native cap ->
 (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 fields (SchemaNodeProtocol.variable_result native variable b c d (length(Protocol.expressions logical))) cap.
Proof.
 intros Hstate Hbound Hb Hc Hd. unfold SchemaNodeProtocol.variable_result.
 apply result_fields.
 - unfold SchemaNode.variable_state,SchemaNode.initialized. rewrite !store_meta_other by discriminate.
   exact (SchemaMetadata.represents_length native _ (proj1(NativeState.schema_representation _ _ Hstate))).
 - eapply fields_frame;[|exact Hbound]. unfold SchemaNode.variable_state,SchemaNode.initialized.
   now rewrite !store_meta_other by discriminate.
 - unfold raw_bound,SchemaNodeProtocol.variable_raw. now rewrite !Nat2Z.id.
Qed.
Lemma literal_fields native logical k a b c d expression cap :
 NativeState.represents native logical -> fields native cap ->
 (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 fields (SchemaLiteralProtocol.result native logical k a b c d expression) cap.
Proof.
 intros Hstate Hbound Hb Hc Hd. unfold SchemaLiteralProtocol.result.
 apply result_fields.
 - unfold SchemaNode.initialized. rewrite !store_meta_other by discriminate.
   exact (SchemaMetadata.represents_length native _ (proj1(NativeState.schema_representation _ _ Hstate))).
 - eapply fields_frame;[|exact Hbound]. unfold SchemaNode.initialized.
   now rewrite !store_meta_other by discriminate.
 - now apply encoded_bound.
Qed.
Lemma reference_fields native logical k a b c d expression cap :
 NativeState.represents native logical -> fields native cap ->
 (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 fields (SchemaReferenceProtocol.result native logical k a b c d expression) cap.
Proof.
 intros Hstate Hbound Hb Hc Hd. unfold SchemaReferenceProtocol.result.
 apply result_fields.
 - rewrite SchemaNode.reference_other by discriminate.
   exact (SchemaMetadata.represents_length native _ (proj1(NativeState.schema_representation _ _ Hstate))).
 - eapply fields_frame;[apply SchemaNode.reference_other;discriminate|exact Hbound].
 - now apply encoded_bound.
Qed.
Lemma argument_fields native ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail cap :
 fields native cap -> fields (ReadFive.fifth_state native ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail) cap.
Proof. intro Hbound. eapply fields_frame;[apply ReadFive.fifth_other;discriminate|exact Hbound]. Qed.
Lemma accepted_helper s logical kind a b c d expression cap observations :
 Protocol.builds_node logical [kind;a;b;c;d] expression ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 Z.of_nat (length (Protocol.expressions logical))<maximum -> NativeState.represents s logical ->
 fields s cap -> (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 exists final, fields final cap /\
 execObserved (funcdef_0__schemaNode (fun _=>false)
   (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)))
   (s,observations)=Some(tt,(final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)));unreadInput:=stdin s|}])) /\
 stdin final=stdin s /\ stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical))) /\
 length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\ meta_value final 8=meta_value s 8.
Proof.
 intros Hbuild Hmeta Hprint Ha Hb Hc Hd Hcapacity Hstate Hbound Hbc Hcc Hdc.
 pose proof Hstate as Hsource.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 assert (Hcount:meta_value s 16=Z.of_nat (length (Protocol.expressions logical))) by exact (proj1 (proj1 Hschemas)).
 assert (Hcases:kind=0%nat \/ (kind=1%nat \/ kind=2%nat \/ kind=11%nat) \/ (3<=kind<=10)%nat).
 { inversion Hbuild;subst;lia. }
 destruct Hcases as [Hzero|[Hliteral|Hrefs]].
 - subst kind. assert (Hsmall:Z.of_nat (S a)<=maximum).
   { assert (Hlt:Z.of_nat a<maximum) by (inversion Hbuild;subst;assumption). lia. }
   exists (SchemaNodeProtocol.variable_result s a b c d (length (Protocol.expressions logical))). split;[exact(variable_fields s logical a b c d cap Hsource Hbound Hbc Hcc Hdc)|]. split.
   + exact (SchemaNode.generated_variable s (fun _=>false)
       (SchemaNodeCommand.arguments 0 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))
       a (length (Protocol.expressions logical)) observations Hmeta eq_refl eq_refl Hsmall Hcount Hcapacity Hprint).
   + split;[unfold SchemaNodeProtocol.variable_result;rewrite SchemaNode.result_input;reflexivity|]. split.
     * unfold SchemaNodeProtocol.variable_result. rewrite SchemaNode.result_output. reflexivity.
     * split;[apply SchemaNodeProtocol.variable_meta_length|]. apply SchemaNodeProtocol.variable_meta_other;lia.
 - destruct (SchemaLiteralProtocol.generated_literal_helper s logical kind a b c d expression observations
     Hliteral Hbuild Hmeta Ha Hb Hc Hd Hcapacity Harena Hclasses Hhistory Hschemas Hprint) as [stored [Hentry Hhelper]].
   exists (SchemaLiteralProtocol.result s logical kind stored b c d expression). split;[exact(literal_fields s logical kind stored b c d expression cap Hsource Hbound Hbc Hcc Hdc)|]. split;[exact Hhelper|]. split.
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
   exists (SchemaReferenceProtocol.result s logical kind a b c d expression). split;[exact(reference_fields s logical kind a b c d expression cap Hsource Hbound Hbc Hcc Hdc)|]. split;[exact Hhelper|]. split.
   + unfold SchemaReferenceProtocol.result. rewrite SchemaNode.result_input. apply SchemaNode.reference_input.
   + split.
     * unfold SchemaReferenceProtocol.result. rewrite SchemaNode.result_output,SchemaNode.reference_output. reflexivity.
     * split;[apply SchemaReferenceProtocol.result_meta_length|]. apply SchemaReferenceProtocol.result_meta_other;lia.
Qed.
Theorem generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail cap observations :
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
 fields s cap -> (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 exists final, fields final cap /\ NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final
   (Protocol.OK (length (Protocol.expressions logical))) (SchemaRepresentation.with_expression logical expression).
Proof.
 intros Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound Hbc Hcc Hdc.
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
 destruct (accepted_helper arg logical kind a b c d expression cap observations Hbuild Hargmeta Hargbuffer
   Ha Hb Hc Hd Hcapacity Hargstate (argument_fields s ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail cap Hbound) Hbc Hcc Hdc) as (expected & Hfields & Hhelper & Hfinalin & Hfinalout & Hfinalmeta & Hfinalerror).
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
Theorem generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail cap observations :
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
 fields s cap ->
 exists final, fields final cap /\ NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final Protocol.NO logical.
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
   eapply fields_frame;[rewrite SchemaBasicRejectionProtocol.result_other by discriminate;
      apply ReadFive.fifth_other;discriminate|exact Hbound].
 - destruct (SchemaReferenceRejection.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
       Hencoding Href Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd
       Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput)
       as (expected & Hresult & Hrun & Hrest).
   assert (Heq:final=expected) by congruence. subst final expected.
   eapply fields_frame;[rewrite SchemaReferenceRejection.result_other by discriminate;
      apply ReadFive.fifth_other;discriminate|exact Hbound].
Qed.
Theorem generated_total s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail cap observations :
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
 fields s cap -> (b<=cap)%nat -> (c<=cap)%nat -> (d<=cap)%nat ->
 exists final reply next, fields final cap /\ NativeSchemaBoundary.complete s logical bs ns kind a b c d tail observations final reply next.
Proof.
 intros Hencoding Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound Hbc Hcc Hdc.
 destruct (SchemaNodeTotal.builds_decidable s logical kind a b c d Hmeta Hsafe) as [[expression Hbuild]|Hnone].
 - destruct (generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail cap observations
     Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity Hstate
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound Hbc Hcc Hdc) as [final Hcomplete].
   exists final,(Protocol.OK (length (Protocol.expressions logical))),(SchemaRepresentation.with_expression logical expression).
   exact Hcomplete.
 - destruct (generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail cap observations
     Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hstate
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput Hbound) as [final Hcomplete].
   exists final,Protocol.NO,logical. exact Hcomplete.
Qed.
Theorem preserves native logical request bs ns tail observations final trace cap :
 Protocol.shape request -> (1<=Protocol.opcode request<=26)%nat ->
 (19<length(memory native arraydef_0__meta))%nat ->
 (1024<=length(memory native arraydef_0__token))%nat ->
 (20<=length(memory native arraydef_0__printBuffer))%nat ->
 meta_value native 15=NativeBasicDispatcher.first(Protocol.opcode request)+1 ->
 meta_value native 8=0 -> NativeState.represents native logical -> Guarantees.safe logical ->
 Z.of_nat(length(Protocol.expressions logical))<maximum ->
 fields native cap -> Forall(fun argument=>(argument<=cap)%nat)(Protocol.arguments request) ->
 stdin native=NativeBasicDispatcher.rest request++tail ->
 execObserved(funcdef_0__command bs ns)(native,observations)=Some(tt,(final,trace)) ->
 fields final cap.
Proof.
 intros Hshape Hrange Hmeta Htoken Hprint Hpending Herror Hstate Hsafe Hroom Hfields Hargs Hinput Hactual.
 destruct (Nat.eq_dec (Protocol.opcode request) 22%nat) as [Hnode|Hother].
 - destruct request as [opcode args name]. cbn [Protocol.opcode] in Hnode. subst opcode.
   destruct Hshape as [Hwords Hformat]. change (length args=5%nat /\ name=[]) in Hformat.
   destruct Hformat as [Hlen ->].
   destruct args as [|kind args];[discriminate|]. destruct args as [|a args];[discriminate|].
   destruct args as [|b args];[discriminate|]. destruct args as [|c args];[discriminate|].
   destruct args as [|d args];[discriminate|]. destruct args as [|extra args];[|discriminate].
   cbn [Protocol.arguments] in Hwords,Hargs.
   inversion Hwords as [|kind' rest Hkind W1];subst kind' rest.
   inversion W1 as [|a' rest Ha W2];subst a' rest.
   inversion W2 as [|b' rest Hb W3];subst b' rest.
   inversion W3 as [|c' rest Hc W4];subst c' rest.
   inversion W4 as [|d' rest Hd W5];subst d' rest.
   inversion Hargs as [|kind' rest Hkc A1];subst kind' rest.
   inversion A1 as [|a' rest Hac A2];subst a' rest.
   inversion A2 as [|b' rest Hbc A3];subst b' rest.
   inversion A3 as [|c' rest Hcc A4];subst c' rest.
   inversion A4 as [|d' rest Hdc A5];subst d' rest.
   change (meta_value native 15=51) in Hpending. rewrite NativeFullDispatcher.node_rest in Hinput.
   destruct (generated_total native logical bs ns 50 [50] kind a b c d 32 32 32 32 32 10 tail cap observations
     eq_refl Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hroom Hstate
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
     ltac:(unfold TokenByteExecution.separator;tauto) ltac:(unfold TokenByteExecution.separator;tauto)
     Hinput Hfields Hbc Hcc Hdc) as (expected & reply & next & HnextFields & Hcomplete).
   pose proof (proj1(proj1 Hcomplete)) as Hrun.
   assert (Hsame:final=expected) by congruence. now subst final.
 - destruct (NativeGeneralCommandInvariant.request_parts request Hshape Hrange)
     as (chars & sep & payload & Hencoding & Hsep & Hrest).
   eapply fields_frame;[|exact Hfields].
   eapply NativeGeneralCommandInvariant.canonical_array with
     (opcode:=Protocol.opcode request) (ch:=NativeBasicDispatcher.first(Protocol.opcode request))
     (chars:=chars) (bs:=bs) (ns:=ns) (separator:=sep) (payload:=payload++tail)
     (observations:=observations) (trace:=trace);try eassumption;try discriminate.
   + exact (CommandSchemaFrame.nodes_ro (Protocol.opcode request) ltac:(lia) Hother).
   + lia.
   + rewrite Hinput,Hrest. now rewrite <-app_assoc.
Qed.
Lemma encoded_fields native cap : fields native cap -> SchemaUniformBudget.encoded_fields native cap.
Proof.
 intros Hfields node kind a b c d expression Hlookup.
 specialize(Hfields _ _ Hlookup). unfold raw_bound,SchemaRepresentation.encode in Hfields.
 now rewrite !Nat2Z.id in Hfields.
Qed.
End NativeSchemaFieldBounds.
