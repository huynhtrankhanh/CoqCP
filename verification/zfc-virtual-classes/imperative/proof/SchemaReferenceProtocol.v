From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFive ReadFour ReadTwo ReadOne DecimalInput CommandArgs
  SchemaNode SchemaNodeMeaning SchemaNodeCommand SchemaRepresentation SchemaMetadata
  ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement NameRepresentation SemanticFrames
  ReplyOK FormulaTopology HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaReferenceProtocol.
Import IndexExecution SipHashExecution.

Definition result s logical kind a b c d expression :=
  SchemaNode.result (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d)
    (length (Protocol.expressions logical)) (SchemaRepresentation.encode kind a b c d expression).
Lemma result_meta_length s logical kind a b c d expression :
  length (memory (result s logical kind a b c d expression) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result. now rewrite SchemaNode.result_meta_length,SchemaNode.reference_length. Qed.
Lemma result_meta_other s logical kind a b c d expression i :
  i<>16%nat -> i<>18%nat -> i<>19%nat -> meta_value (result s logical kind a b c d expression) i=meta_value s i.
Proof. intros H16 H18 H19. unfold result. rewrite SchemaNode.result_meta_other by exact H16. now apply SchemaNode.reference_meta_other. Qed.
Lemma result_other s logical kind a b c d expression name :
  name<>arraydef_0__meta -> name<>arraydef_0__schemaNodes -> name<>arraydef_0__printBuffer ->
  memory (result s logical kind a b c d expression) name=memory s name.
Proof. intros Hmeta Hnodes Hprint. unfold result. rewrite SchemaNode.result_other by assumption. now apply SchemaNode.reference_other. Qed.
Lemma result_projection s logical kind a b c d expression : FormulaProjection.storage s (result s logical kind a b c d expression).
Proof. unfold result. eapply FormulaProjection.storage_trans;[apply SchemaNode.reference_projection|apply SchemaNode.result_projection]. Qed.
Lemma result_allocation s logical kind a b c d expression watched : watched<>arraydef_0__schemaNodes ->
  length (memory (result s logical kind a b c d expression) watched)=length (memory s watched).
Proof.
  intro Hnodes. destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply result_meta_length|].
  destruct (decide (watched=arraydef_0__printBuffer)) as [->|Hprint].
  - unfold result,SchemaNode.result. rewrite store_meta_other by discriminate.
    rewrite ReplyOKExecution.reply_buffer_length,SchemaNode.written_other by discriminate.
    now rewrite SchemaNode.reference_other by discriminate.
  - now rewrite result_other by assumption.
Qed.
Lemma argument_allocation s ch chars kind a b c d sep1 sep2 sep3 sep4 sep5 tail watched :
  length (memory (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail) watched)=length (memory s watched).
Proof.
  destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply ReadFive.fifth_meta_length|].
  destruct (decide (watched=arraydef_0__token)) as [->|Htoken].
  - unfold ReadFive.fifth_state,ReadFive.fourth_state,ReadFour.fourth_state,ReadFour.third_state,ReadFour.second_state,
      ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
    now rewrite !DecimalInput.encoded_token_length,CommandArgs.pending_token_length.
  - now rewrite ReadFive.fifth_other by assumption.
Qed.

Theorem generated_reference s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars -> (3<=kind<=10)%nat -> Protocol.builds_node logical [kind;a;b;c;d] expression ->
  (19<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
  Z.of_nat (length (Protocol.expressions logical))<maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaRepresentation.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
  stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 22 [kind;a;b;c;d] []) (Protocol.OK (length (Protocol.expressions logical)))
      (SchemaRepresentation.with_expression logical expression) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final (SchemaRepresentation.with_expression logical expression) /\
    NameRepresentation.represents final (Protocol.bindings logical) /\
    SchemaRepresentation.represents final (SchemaRepresentation.with_expression logical expression) /\
    (forall watched,watched<>arraydef_0__schemaNodes -> length (memory final watched)=length (memory s watched)) /\
    meta_value final 8=0 /\
    (FormulaTopology.ordered s (length (Protocol.formulas logical)) -> FormulaTopology.ordered final (length (Protocol.formulas logical))) /\
    (Guarantees.safe logical -> Guarantees.safe (SchemaRepresentation.with_expression logical expression)).
Proof.
  intros Hencoding Hrange Hbuild Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hc Hd Hcapacity
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  destruct (ReadFive.generated_reads s 22 ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
    ltac:(lia) Htoken Hbuffer Hpending Herror ltac:(unfold maximum;lia) Hencoding ltac:(unfold maximum;lia)
    Ha Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hfifth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail).
  set (final:=result arg logical kind a b c d expression).
  assert (Hargmeta:(19<length (memory arg arraydef_0__meta))%nat).
  { unfold arg. now rewrite ReadFive.fifth_meta_length. }
  assert (Harg_schema:SchemaRepresentation.represents arg logical).
  { eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
    - unfold arg. apply ReadFive.fifth_meta_other;lia.
    - unfold arg. apply ReadFive.fifth_other;discriminate. }
  destruct (SchemaNodeMeaning.reference_metadata arg logical kind a b c d expression Hargmeta Hbuild Hrange)
    as [Hflag [Hwidth Htype]].
  assert (Hcount:meta_value arg 16=Z.of_nat (length (Protocol.expressions logical))) by exact (proj1 (proj1 Harg_schema)).
  pose proof (SchemaNode.generated_reference arg (fun _=>false)
    (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))
    (Protocol.expressions logical) kind a b c d (length (Protocol.expressions logical)) observations
    Hargmeta (proj1 Harg_schema) eq_refl eq_refl eq_refl eq_refl eq_refl Hrange ltac:(rewrite Hflag;lia)
    Hcount Hcapacity Hargbuffer) as Hhelper.
  cbn zeta in Hhelper. rewrite Hwidth,Htype in Hhelper.
  change (execObserved (funcdef_0__schemaNode (fun _=>false)
    (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)))
    (arg,observations)=Some (tt,(final,observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)));unreadInput:=stdin arg|}]))) in Hhelper.
  assert (Hfinalmeta:(8<length (memory final arraydef_0__meta))%nat).
  { unfold final. rewrite result_meta_length. lia. }
  assert (Hfinalerror:meta_value final 8=0).
  { unfold final. rewrite result_meta_other by lia. unfold arg. rewrite ReadFive.fifth_meta_other by lia. exact Herror. }
  pose proof (SchemaNodeCommand.generated_command s bs ns _ _ _ _ _ arg final (Z.of_nat kind) (Z.of_nat a)
    (Z.of_nat b) (Z.of_nat c) (Z.of_nat d) observations _ Hopcode Hfirst Hsecond Hthird Hfourth Hfifth Hhelper Hfinalmeta Hfinalerror) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput. rewrite Hinput,Houtput in Hrun.
  assert (Harrays:forall name,name<>arraydef_0__meta -> name<>arraydef_0__token ->
    name<>arraydef_0__schemaNodes -> name<>arraydef_0__printBuffer -> memory final name=memory s name).
  { intros name Hm Ht Hn Hp. unfold final. rewrite result_other by assumption. unfold arg. now apply ReadFive.fifth_other. }
  assert (Hcells:forall i,i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>15%nat -> i<>16%nat ->
    i<>17%nat -> i<>18%nat -> i<>19%nat -> meta_value final i=meta_value s i).
  { intros i H6 H11 H14 H15 H16 H17 H18 H19. unfold final. rewrite result_meta_other by assumption.
    unfold arg. apply ReadFive.fifth_meta_other;[lia|exact H6|exact H11|exact H14|exact H15|exact H17]. }
  assert (Hstep:Protocol.step logical (Protocol.Req 22 [kind;a;b;c;d] []) (Protocol.OK (length (Protocol.expressions logical)))
    (SchemaRepresentation.with_expression logical expression)).
  { eapply Protocol.step_accept;[apply Protocol.accept_node;exact Hbuild|].
    apply HistoryRefinement.retained_refl. exact (SemanticFrames.arena_NoDup s _ Harena). }
  assert (Hentry:SchemaRepresentation.entry (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical)
    (SchemaRepresentation.encode kind a b c d expression) expression).
  { destruct (SchemaNodeMeaning.builds_plan logical kind a b c d expression Hbuild Hrange) as [_ [_ [_ Htype']]].
    unfold SchemaRepresentation.encode. rewrite <-Htype'. eapply SchemaNodeMeaning.entry_bridge;[exact Hbuild|exact Hrange| |].
    - repeat (constructor;[unfold word,maximum in *;lia|]);constructor.
    - exact (SchemaNodeMeaning.builds_arity_word arg logical kind a b c d expression (proj1 Harg_schema) Hbuild Hrange). }
  assert (Hfinal_schema:SchemaRepresentation.represents final (SchemaRepresentation.with_expression logical expression)).
  { eapply (SchemaRepresentation.append arg final logical (SchemaRepresentation.encode kind a b c d expression) expression);
      [exact Harg_schema|exact Hentry| | |].
    - unfold final,result. rewrite SchemaNode.result_nodes.
      + now rewrite SchemaNode.reference_other by discriminate.
      + rewrite SchemaNode.reference_other by discriminate. exact (SchemaMetadata.represents_length arg _ (proj1 Harg_schema)).
    - unfold final,result. rewrite SchemaNode.result_count.
      + f_equal. lia.
      + rewrite SchemaNode.reference_length. lia.
    - lia. }
  exists final. split;[exact Hrun|]. split;[exact Hstep|]. split.
  - eapply FormulaProjection.storage_arena;[unfold final;apply result_projection|].
    eapply ArenaFrame.storage_arena;[unfold arg;apply ReadFive.fifth_storage;lia|exact Harena].
  - split.
    + replace (Protocol.formulas logical) with (Protocol.formulas logical++[]) at 1 by apply app_nil_r.
      eapply SemanticFrames.classes_extend;[apply Hcells;lia|apply Harrays;discriminate|exact Hclasses].
    + split.
      * change (HistoryRefinement.represents final logical).
        eapply SemanticFrames.history_transport;[apply Hcells;lia|apply Harrays;discriminate|exact Hhistory].
      * split.
        -- unfold NameRepresentation.represents in *. rewrite (Hcells 4%nat),(Hcells 5%nat) by lia.
           rewrite (Harrays arraydef_0__names),(Harrays arraydef_0__bindings) by discriminate. exact Hnames.
        -- split;[exact Hfinal_schema|]. split.
           ++ intros watched Hnodes. unfold final. rewrite result_allocation by exact Hnodes. unfold arg. apply argument_allocation.
           ++ split;[exact Hfinalerror|]. split.
              ** intro Hordered. apply (FormulaTopology.same s final _ Hordered). intros parent Hparent.
                 unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate.
              ** intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End SchemaReferenceProtocol.
