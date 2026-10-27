From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte SchemaNodeTotal SchemaRepresentation
 NativeState NativeCommandBoundary NativeCommandStop ReadFive SchemaNode SchemaNodeRejection
 SchemaBasicRejectionProtocol SchemaReferenceRejection ReplyNO DecimalInput ReadNat ReadToken ReadFour ReadTwo ReadOne CommandInput SchemaNodeProtocol SchemaLiteralProtocol SchemaReferenceProtocol
 SchemaNodeCommand SchemaNodeMeaning ArenaFrame SemanticFrames Representation ClassStorage HistoryRefinement NameRepresentation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeSchemaBoundary.
Import IndexExecution SipHashExecution.

Definition outcome logical kind a b c d reply next :=
 ((exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression /\
   reply=Protocol.OK (length (Protocol.expressions logical)) /\
   next=SchemaRepresentation.with_expression logical expression) \/
 ((~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) /\
   reply=Protocol.NO /\ next=logical)).
Definition unchanged logical next :=
 Protocol.formulas next=Protocol.formulas logical /\
 Protocol.classes next=Protocol.classes logical /\
 Protocol.history next=Protocol.history logical /\
 Protocol.bindings next=Protocol.bindings logical /\
 (length (Protocol.expressions next)<=S (length (Protocol.expressions logical)))%nat.
Definition complete s logical bs ns kind a b c d tail observations final reply next :=
 SchemaNodeTotal.checked_step s logical bs ns kind a b c d tail observations final reply next /\
 NativeState.represents final next /\
 NativeCommandBoundary.io s final reply tail /\
 unchanged logical next /\ outcome logical kind a b c d reply next.

Lemma outcome_unchanged logical kind a b c d reply next :
 outcome logical kind a b c d reply next -> unchanged logical next.
Proof.
 intros [[expression [Hbuild [Hreply ->]]]|[Hnone [Hreply ->]]];unfold unchanged.
 - cbn [SchemaRepresentation.with_expression Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
   repeat split;try reflexivity. rewrite length_app. cbn;lia.
 - repeat split;try reflexivity. lia.
Qed.

Lemma from_checked s logical bs ns ch chars kind a b c d sep payload tail observations final reply next :
 decimalBytes 22=ch::chars ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (1024<=length (memory s arraydef_0__token))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> TokenByteExecution.separator sep ->
 stdin s=chars++sep::payload ->
 SchemaNodeTotal.checked_step s logical bs ns kind a b c d tail observations final reply next ->
 outcome logical kind a b c d reply next ->
 stdin final=tail -> stdout final=stdout s++Protocol.reply_bytes reply ->
 complete s logical bs ns kind a b c d tail observations final reply next.
Proof.
 intros Hencoding Hmeta Htoken Hprint Hpending Herror Hsep Hinput Hchecked Houtcome Hin Hout.
 destruct Hchecked as (Hrun & Hstep & Harena & Hclasses & Hhistory & Hnames & Hschemas & Hlength & Herror' & Htop & Hsafe).
 assert (Hstop:meta_value final 9=meta_value s 9).
 { exact (NativeCommandStop.canonical 22 ch chars s bs ns sep payload observations final _
     ltac:(lia) Hencoding ltac:(lia) Htoken Hpending Herror Hsep Hinput Hrun Herror'). }
 unfold complete. split.
 - unfold SchemaNodeTotal.checked_step. repeat first [assumption|split].
 - split.
   + constructor;assumption.
   + split.
     * unfold NativeCommandBoundary.io. split;[exact Hin|]. split;[exact Hout|].
       split;[rewrite Hlength by discriminate;exact Htoken|].
       split;[rewrite Hlength by discriminate;exact Hprint|]. split;assumption.
     * split;[eapply outcome_unchanged;exact Houtcome|exact Houtcome].
Qed.
Lemma argument_io s ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail :
 stdin (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail)=tail /\
 stdout (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail)=stdout s.
Proof.
 split;[reflexivity|].
 assert (Hencoded:forall s value tail,stdout (DecimalInput.encoded_result s value tail)=stdout s).
 { intros native value suffix. unfold DecimalInput.encoded_result,ReadNatExecution.token_number.
   change (stdout (ReadTokenExecution.read_result native (decimalBytes value) suffix)=stdout native).
   apply ReadTokenExecution.result_output. }
 unfold ReadFive.fifth_state,ReadFive.fourth_state,ReadFour.fourth_state,ReadFour.third_state,
   ReadFour.second_state,ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
 rewrite !Hencoded. apply CommandInput.parsed_output.
Qed.

Lemma basic_rejected_io s logical kind a b c d :
 stdin (SchemaBasicRejectionProtocol.result s logical kind a b c d)=stdin s /\
 stdout (SchemaBasicRejectionProtocol.result s logical kind a b c d)=stdout s++Protocol.reply_bytes Protocol.NO.
Proof. split;reflexivity. Qed.

Lemma reference_rejected_io s logical kind a b c d :
 stdin (SchemaReferenceRejection.result s logical kind a b c d)=stdin s /\
 stdout (SchemaReferenceRejection.result s logical kind a b c d)=stdout s++Protocol.reply_bytes Protocol.NO.
Proof.
 unfold SchemaReferenceRejection.result. rewrite ReplyNOExecution.reply_input,ReplyNOExecution.reply_output.
 rewrite SchemaNode.reference_input,SchemaNode.reference_output. split;reflexivity.
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
 exists final, complete s logical bs ns kind a b c d tail observations final Protocol.NO logical.
Proof.
 intros Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 destruct (SchemaNodeTotal.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
   Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd
   Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput) as [final Hchecked].
 pose proof (proj1 Hchecked) as Hactual.
 assert (Houtcome:outcome logical kind a b c d Protocol.NO logical).
 { right. repeat split;assumption || reflexivity. }
 destruct (argument_io s ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail) as [Hin Hout].
 assert (Hcases:SchemaBasicRejectionProtocol.basic kind \/ (3<=kind<=10)%nat).
 { unfold SchemaBasicRejectionProtocol.basic;lia. }
 assert (Hio:stdin final=tail /\ stdout final=stdout s++Protocol.reply_bytes Protocol.NO).
 { destruct Hcases as [Hbasic|Href].
   - destruct (SchemaBasicRejectionProtocol.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
       Hencoding Hbasic Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd
       Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput)
       as (expected & Hresult & Hrun & Hrest).
     assert (Heq:final=expected) by congruence. subst final expected.
     destruct (basic_rejected_io (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail) logical kind a b c d) as [Hfinalin Hfinalout].
     split;[exact (eq_trans Hfinalin Hin)|].
     exact (eq_trans Hfinalout (f_equal (fun bytes=>bytes++Protocol.reply_bytes Protocol.NO) Hout)).
   - destruct (SchemaReferenceRejection.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
       Hencoding Href Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd
       Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput)
       as (expected & Hresult & Hrun & Hrest).
     assert (Heq:final=expected) by congruence. subst final expected.
     destruct (reference_rejected_io (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail) logical kind a b c d) as [Hfinalin Hfinalout].
     split;[exact (eq_trans Hfinalin Hin)|].
     exact (eq_trans Hfinalout (f_equal (fun bytes=>bytes++Protocol.reply_bytes Protocol.NO) Hout)). }
 exists final. exact (from_checked s logical bs ns ch chars kind a b c d sep0
   (decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail)
   tail observations final Protocol.NO logical Hencoding Hmeta Htoken Hprint Hpending Herror Hsep0 Hinput
   Hchecked Houtcome (proj1 Hio) (proj2 Hio)).
Qed.
Lemma accepted_helper s logical kind a b c d expression observations :
 Protocol.builds_node logical [kind;a;b;c;d] expression ->
 (19<length (memory s arraydef_0__meta))%nat ->
 (20<=length (memory s arraydef_0__printBuffer))%nat ->
 Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
 Z.of_nat (length (Protocol.expressions logical))<maximum -> NativeState.represents s logical ->
 exists final,
 execObserved (funcdef_0__schemaNode (fun _=>false)
   (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)))
   (s,observations)=Some(tt,(final,observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)));unreadInput:=stdin s|}])) /\
 stdin final=stdin s /\ stdout final=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical))) /\
 length (memory final arraydef_0__meta)=length (memory s arraydef_0__meta) /\ meta_value final 8=meta_value s 8.
Proof.
 intros Hbuild Hmeta Hprint Ha Hb Hc Hd Hcapacity Hstate.
 destruct Hstate as [Harena Hclasses Hhistory Hnames Hschemas].
 assert (Hcount:meta_value s 16=Z.of_nat (length (Protocol.expressions logical))) by exact (proj1 (proj1 Hschemas)).
 assert (Hcases:kind=0%nat \/ (kind=1%nat \/ kind=2%nat \/ kind=11%nat) \/ (3<=kind<=10)%nat).
 { inversion Hbuild;subst;lia. }
 destruct Hcases as [Hzero|[Hliteral|Hrefs]].
 - subst kind. assert (Hsmall:Z.of_nat (S a)<=maximum).
   { assert (Hlt:Z.of_nat a<maximum) by (inversion Hbuild;subst;assumption). lia. }
   exists (SchemaNodeProtocol.variable_result s a b c d (length (Protocol.expressions logical))). split.
   + exact (SchemaNode.generated_variable s (fun _=>false)
       (SchemaNodeCommand.arguments 0 (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))
       a (length (Protocol.expressions logical)) observations Hmeta eq_refl eq_refl Hsmall Hcount Hcapacity Hprint).
   + split;[unfold SchemaNodeProtocol.variable_result;rewrite SchemaNode.result_input;reflexivity|]. split.
     * unfold SchemaNodeProtocol.variable_result. rewrite SchemaNode.result_output. reflexivity.
     * split;[apply SchemaNodeProtocol.variable_meta_length|]. apply SchemaNodeProtocol.variable_meta_other;lia.
 - destruct (SchemaLiteralProtocol.generated_literal_helper s logical kind a b c d expression observations
     Hliteral Hbuild Hmeta Ha Hb Hc Hd Hcapacity Harena Hclasses Hhistory Hschemas Hprint) as [stored [Hentry Hhelper]].
   exists (SchemaLiteralProtocol.result s logical kind stored b c d expression). split;[exact Hhelper|]. split.
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
   exists (SchemaReferenceProtocol.result s logical kind a b c d expression). split;[exact Hhelper|]. split.
   + unfold SchemaReferenceProtocol.result. rewrite SchemaNode.result_input. apply SchemaNode.reference_input.
   + split.
     * unfold SchemaReferenceProtocol.result. rewrite SchemaNode.result_output,SchemaNode.reference_output. reflexivity.
     * split;[apply SchemaReferenceProtocol.result_meta_length|]. apply SchemaReferenceProtocol.result_meta_other;lia.
Qed.
Lemma argument_represents s logical ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail :
 (19<length (memory s arraydef_0__meta))%nat -> NativeState.represents s logical ->
 NativeState.represents (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail) logical.
Proof.
 intros Hmeta [Harena Hclasses Hhistory Hnames Hschemas].
 set (arg:=ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail).
 constructor.
 - eapply ArenaFrame.storage_arena;[unfold arg;apply ReadFive.fifth_storage;lia|exact Harena].
 - replace (Protocol.formulas logical) with (Protocol.formulas logical++[]) at 1 by apply app_nil_r.
   eapply SemanticFrames.classes_extend;[unfold arg;apply ReadFive.fifth_meta_other;lia|
     unfold arg;apply ReadFive.fifth_other;discriminate|exact Hclasses].
 - eapply SemanticFrames.history_transport;[unfold arg;apply ReadFive.fifth_meta_other;lia|
     unfold arg;apply ReadFive.fifth_other;discriminate|exact Hhistory].
 - unfold NameRepresentation.represents in *. unfold arg.
   rewrite !ReadFive.fifth_meta_other by lia. rewrite !ReadFive.fifth_other by discriminate. exact Hnames.
 - eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
   + unfold arg. apply ReadFive.fifth_meta_other;lia.
   + unfold arg. apply ReadFive.fifth_other;discriminate.
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
 exists final, complete s logical bs ns kind a b c d tail observations final
   (Protocol.OK (length (Protocol.expressions logical))) (SchemaRepresentation.with_expression logical expression).
Proof.
 intros Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput.
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
 assert (Hargstate:NativeState.represents arg logical) by (unfold arg;exact (argument_represents s logical ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail Hmeta Hstate)).
 destruct (accepted_helper arg logical kind a b c d expression observations Hbuild Hargmeta Hargbuffer
   Ha Hb Hc Hd Hcapacity Hargstate) as (expected & Hhelper & Hfinalin & Hfinalout & Hfinalmeta & Hfinalerror).
 assert (Hexpectedmeta:(8<length (memory expected arraydef_0__meta))%nat) by lia.
 assert (Hexpectederror:meta_value expected 8=0).
 { rewrite Hfinalerror. unfold arg. rewrite ReadFive.fifth_meta_other by lia. exact Herror. }
 pose proof (SchemaNodeCommand.generated_command s bs ns _ _ _ _ _ arg expected (Z.of_nat kind) (Z.of_nat a)
   (Z.of_nat b) (Z.of_nat c) (Z.of_nat d) observations _ Hopcode Hfirst Hsecond Hthird Hfourth Hfifth Hhelper Hexpectedmeta Hexpectederror) as Hexpected.
 change (stdin arg=tail) in Hin. change (stdout arg=stdout s) in Hout. rewrite Hin,Hout in Hexpected.
 pose proof (proj1 Hchecked) as Hactual. assert (Heq:final=expected) by congruence. subst expected.
 assert (Houtcome:outcome logical kind a b c d (Protocol.OK (length (Protocol.expressions logical))) (SchemaRepresentation.with_expression logical expression)).
 { left. exists expression. repeat split;assumption || reflexivity. }
 exists final. exact (from_checked s logical bs ns ch chars kind a b c d sep0
   (decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail)
   tail observations final _ _ Hencoding Hmeta Htoken Hprint Hpending Herror Hsep0 Hinput Hchecked Houtcome
   (eq_trans Hfinalin Hin) (eq_trans Hfinalout (f_equal (fun bytes=>bytes++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)))) Hout))).
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
 exists final reply next, complete s logical bs ns kind a b c d tail observations final reply next.
Proof.
 intros Hencoding Hsafe Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hcapacity Hstate
   Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput.
 destruct (SchemaNodeTotal.builds_decidable s logical kind a b c d Hmeta Hsafe) as [[expression Hbuild]|Hnone].
 - destruct (generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations
     Hencoding Hsafe Hbuild Hmeta Htoken Hprint Hpending Herror Ha Hb Hc Hd Hcapacity Hstate
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput) as [final Hcomplete].
   exists final,(Protocol.OK (length (Protocol.expressions logical))),(SchemaRepresentation.with_expression logical expression).
   exact Hcomplete.
 - destruct (generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
     Hencoding Hsafe Hnone Hmeta Htoken Hprint Hpending Herror Hkind Ha Hb Hc Hd Hstate
     Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hinput) as [final Hcomplete].
   exists final,Protocol.NO,logical. exact Hcomplete.
Qed.
End NativeSchemaBoundary.
