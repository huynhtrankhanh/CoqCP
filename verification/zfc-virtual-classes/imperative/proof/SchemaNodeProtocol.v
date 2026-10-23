From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFive AxiomCommand SchemaNodeCommand SchemaNode
  SchemaRepresentation SchemaMetadata ArenaFrame FormulaProjection Representation ClassStorage
  HistoryRefinement NameRepresentation SemanticFrames ReplyOK ReadFour ReadTwo ReadOne DecimalInput CommandArgs FormulaTopology HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaNodeProtocol.
Import IndexExecution SipHashExecution.

Definition variable_raw variable b c d : Z*Z*Z*Z*Z*Z*Z :=
  (0,Z.of_nat variable,Z.of_nat b,Z.of_nat c,Z.of_nat d,0,Z.of_nat (S variable)).
Definition variable_result s variable b c d n :=
  SchemaNode.result (SchemaNode.variable_state s variable) n (variable_raw variable b c d).

Lemma variable_meta_length s variable b c d n :
  length (memory (variable_result s variable b c d n) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold variable_result. rewrite SchemaNode.result_meta_length. unfold SchemaNode.variable_state,SchemaNode.initialized. now rewrite !store_meta_length. Qed.
Lemma variable_meta_other s variable b c d n i :
  i<>16%nat -> i<>18%nat -> i<>19%nat ->
  meta_value (variable_result s variable b c d n) i=meta_value s i.
Proof.
  intros H16 H18 H19. unfold variable_result. rewrite SchemaNode.result_meta_other by exact H16.
  unfold SchemaNode.variable_state,SchemaNode.initialized. now rewrite !meta_store_other by assumption.
Qed.
Lemma variable_other s variable b c d n name :
  name<>arraydef_0__meta -> name<>arraydef_0__schemaNodes -> name<>arraydef_0__printBuffer ->
  memory (variable_result s variable b c d n) name=memory s name.
Proof.
  intros Hmeta Hnodes Hprint. unfold variable_result. rewrite SchemaNode.result_other by assumption.
  unfold SchemaNode.variable_state,SchemaNode.initialized. now rewrite !store_meta_other by exact Hmeta.
Qed.
Lemma variable_projection s variable b c d n : FormulaProjection.storage s (variable_result s variable b c d n).
Proof.
  unfold variable_result. eapply FormulaProjection.storage_trans;[|apply SchemaNode.result_projection].
  apply FormulaProjection.strong_storage. unfold SchemaNode.variable_state,SchemaNode.initialized. ArenaFrame.storage_steps.
Qed.
Lemma variable_allocation s variable b c d n watched : watched<>arraydef_0__schemaNodes ->
  length (memory (variable_result s variable b c d n) watched)=length (memory s watched).
Proof.
  intro Hnodes. destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply variable_meta_length|].
  destruct (decide (watched=arraydef_0__printBuffer)) as [->|Hprint].
  - unfold variable_result,SchemaNode.result. rewrite store_meta_other by discriminate.
    rewrite ReplyOKExecution.reply_buffer_length,SchemaNode.written_other by discriminate.
    unfold SchemaNode.variable_state,SchemaNode.initialized. now rewrite !store_meta_other by discriminate.
  - now rewrite variable_other by assumption.
Qed.
Lemma argument_allocation s ch chars variable b c d sep1 sep2 sep3 sep4 sep5 tail watched :
  length (memory (ReadFive.fifth_state s ch chars 0 sep1 variable sep2 b sep3 c sep4 d sep5 tail) watched)=length (memory s watched).
Proof.
  destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply ReadFive.fifth_meta_length|].
  destruct (decide (watched=arraydef_0__token)) as [->|Htoken].
  - unfold ReadFive.fifth_state,ReadFive.fourth_state,ReadFour.fourth_state,ReadFour.third_state,ReadFour.second_state,
      ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
    now rewrite !DecimalInput.encoded_token_length,CommandArgs.pending_token_length.
  - now rewrite ReadFive.fifth_other by assumption.
Qed.
Lemma variable_entry fs classes prior variable b c d :
  Z.of_nat (S variable)<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
  SchemaRepresentation.entry fs classes prior (variable_raw variable b c d) (Protocol.CE (Schemata.metavariable variable)).
Proof.
  intros Hvariable Hb Hc Hd.
  change (SchemaRepresentation.entry fs classes prior
    (SchemaRepresentation.encode 0 variable b c d (Protocol.CE (Schemata.metavariable variable))) (Protocol.CE (Schemata.metavariable variable))).
  apply SchemaRepresentation.entry_builds.
  - discriminate.
  - unfold SchemaRepresentation.fields_fit. cbn [SchemaMetadata.arity Schemata.class_arity].
    repeat (constructor;[unfold word,maximum in *;lia|]);constructor.
  - apply Protocol.node_meta. change (Z.of_nat variable<maximum). lia.
Qed.

Theorem generated_variable s logical bs ns ch chars variable b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars ->
  (19<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat (S variable)<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
  Z.of_nat (length (Protocol.expressions logical))<maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaRepresentation.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
  stdin s=chars++sep0::decimalBytes 0++sep1::decimalBytes variable++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
  exists final,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes (Protocol.OK (length (Protocol.expressions logical)));unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 22 [0;variable;b;c;d]%nat []) (Protocol.OK (length (Protocol.expressions logical)))
      (SchemaRepresentation.with_expression logical (Protocol.CE (Schemata.metavariable variable))) /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final (SchemaRepresentation.with_expression logical (Protocol.CE (Schemata.metavariable variable))) /\
    NameRepresentation.represents final (Protocol.bindings logical) /\
    SchemaRepresentation.represents final (SchemaRepresentation.with_expression logical (Protocol.CE (Schemata.metavariable variable))) /\
    (forall watched,watched<>arraydef_0__schemaNodes -> length (memory final watched)=length (memory s watched)) /\
    meta_value final 8=0 /\
    (FormulaTopology.ordered s (length (Protocol.formulas logical)) -> FormulaTopology.ordered final (length (Protocol.formulas logical))) /\
    (Guarantees.safe logical -> Guarantees.safe (SchemaRepresentation.with_expression logical (Protocol.CE (Schemata.metavariable variable)))).
Proof.
  intros Hencoding Hmeta Htoken Hbuffer Hpending Herror Hvariable Hb Hc Hd Hcapacity
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  destruct (ReadFive.generated_reads s 22 ch chars 0 variable b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
    ltac:(lia) Htoken Hbuffer Hpending Herror ltac:(unfold maximum;lia) Hencoding ltac:(unfold maximum;lia)
    ltac:(lia) Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hfifth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFive.fifth_state s ch chars 0 sep1 variable sep2 b sep3 c sep4 d sep5 tail).
  set (n:=length (Protocol.expressions logical)).
  set (final:=variable_result arg variable b c d n).
  assert (Hargmeta:(19<length (memory arg arraydef_0__meta))%nat).
  { unfold arg. now rewrite ReadFive.fifth_meta_length. }
  assert (Hargcount:meta_value arg 16=Z.of_nat n).
  { unfold arg. rewrite ReadFive.fifth_meta_other by lia. exact (proj1 (proj1 Hschemas)). }
  assert (Hargerror:meta_value arg 8=0).
  { unfold arg. rewrite ReadFive.fifth_meta_other by lia. exact Herror. }
  pose proof (SchemaNode.generated_variable arg (fun _=>false)
    (SchemaNodeCommand.arguments 0 (Z.of_nat variable) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)) variable n observations
    Hargmeta eq_refl eq_refl Hvariable Hargcount Hcapacity Hargbuffer) as Hhelper.
  change (execObserved (funcdef_0__schemaNode (fun _=>false) (SchemaNodeCommand.arguments 0 (Z.of_nat variable) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))) (arg,observations)=Some (tt,(final,
    observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin arg|}]))) in Hhelper.
  assert (Hfinalmeta:(8<length (memory final arraydef_0__meta))%nat).
  { unfold final. rewrite variable_meta_length. lia. }
  assert (Hfinalerror:meta_value final 8=0).
  { unfold final. rewrite variable_meta_other by lia. exact Hargerror. }
  pose proof (SchemaNodeCommand.generated_command s bs ns _ _ _ _ _ arg final 0 (Z.of_nat variable)
    (Z.of_nat b) (Z.of_nat c) (Z.of_nat d) observations _ Hopcode Hfirst Hsecond Hthird Hfourth Hfifth Hhelper Hfinalmeta Hfinalerror) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  rewrite Hinput,Houtput in Hrun.
  assert (Harrays:forall name,name<>arraydef_0__meta -> name<>arraydef_0__token ->
    name<>arraydef_0__schemaNodes -> name<>arraydef_0__printBuffer -> memory final name=memory s name).
  { intros name Hm Ht Hn Hp. unfold final. rewrite variable_other by assumption. unfold arg. now apply ReadFive.fifth_other. }
  assert (Hcells:forall i,i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>15%nat -> i<>16%nat ->
    i<>17%nat -> i<>18%nat -> i<>19%nat -> meta_value final i=meta_value s i).
  { intros i H6 H11 H14 H15 H16 H17 H18 H19. unfold final. rewrite variable_meta_other by assumption.
    unfold arg. apply ReadFive.fifth_meta_other;[lia|exact H6|exact H11|exact H14|exact H15|exact H17]. }
  assert (Hstep:Protocol.step logical (Protocol.Req 22 [0;variable;b;c;d]%nat []) (Protocol.OK n)
    (SchemaRepresentation.with_expression logical (Protocol.CE (Schemata.metavariable variable)))).
  { eapply Protocol.step_accept.
    - apply Protocol.accept_node. apply Protocol.node_meta. change (Z.of_nat variable<maximum). lia.
    - apply HistoryRefinement.retained_refl. exact (SemanticFrames.arena_NoDup s _ Harena). }
  assert (Harg_schema:SchemaRepresentation.represents arg logical).
  { eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
    - unfold arg. apply ReadFive.fifth_meta_other;lia.
    - unfold arg. apply ReadFive.fifth_other;discriminate. }
  assert (Hfinal_schema:SchemaRepresentation.represents final
    (SchemaRepresentation.with_expression logical (Protocol.CE (Schemata.metavariable variable)))).
  { eapply (SchemaRepresentation.append arg final logical (variable_raw variable b c d) (Protocol.CE (Schemata.metavariable variable)));[exact Harg_schema|exact (variable_entry _ _ _ variable b c d Hvariable Hb Hc Hd)| | |].
    - unfold final,variable_result. rewrite SchemaNode.result_nodes.
      + unfold SchemaNode.variable_state,SchemaNode.initialized. now rewrite !store_meta_other by discriminate.
      + unfold SchemaNode.variable_state,SchemaNode.initialized. rewrite !store_meta_other by discriminate.
        exact (SchemaMetadata.represents_length arg _ (proj1 Harg_schema)).
    - unfold final,variable_result. rewrite SchemaNode.result_count.
      + unfold n. f_equal. lia.
      + unfold SchemaNode.variable_state,SchemaNode.initialized. rewrite !store_meta_length. lia.
    - lia. }
  exists final. split;[exact Hrun|]. split;[exact Hstep|]. split.
  - eapply FormulaProjection.storage_arena;[unfold final;apply variable_projection|].
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
           ++ intros watched Hnodes. unfold final. rewrite variable_allocation by exact Hnodes.
              unfold arg. apply argument_allocation.
           ++ split;[exact Hfinalerror|]. split.
              ** intro Hordered. apply (FormulaTopology.same s final _ Hordered).
                 intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate.
              ** intro Hsafe. eapply Guarantees.step_safe;eassumption.
Qed.
End SchemaNodeProtocol.
