From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal TokenByte ReadFive ReadFour ReadTwo ReadOne DecimalInput CommandArgs
  SchemaNode SchemaNodeRejection SchemaNodeCommand SchemaRepresentation SchemaMetadata
  ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement NameRepresentation SemanticFrames
  ReplyNO FormulaTopology HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaBasicRejectionProtocol.
Import IndexExecution SipHashExecution ObservedLocal.

Definition result (s:Machine) (logical:Protocol.state) (kind a b c d:nat) :=
  ReplyNOExecution.reply_state (SchemaNodeRejection.state s).
Lemma result_meta_length s logical kind a b c d :
  length (memory (result s logical kind a b c d) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result. rewrite ReplyNOExecution.reply_memory. unfold SchemaNodeRejection.state. now rewrite store_meta_length,SchemaNode.initialized_length. Qed.
Lemma result_meta_other s logical kind a b c d i : i<>18%nat -> i<>19%nat ->
  meta_value (result s logical kind a b c d) i=meta_value s i.
Proof. intros H18 H19. change (meta_value (SchemaNodeRejection.state s) i=meta_value s i). unfold SchemaNodeRejection.state,SchemaNode.initialized. now rewrite !meta_store_other by assumption. Qed.
Lemma result_other s logical kind a b c d name : name<>arraydef_0__meta ->
  memory (result s logical kind a b c d) name=memory s name.
Proof. intro Hmeta. unfold result. rewrite ReplyNOExecution.reply_memory. unfold SchemaNodeRejection.state,SchemaNode.initialized. now rewrite !store_meta_other by exact Hmeta. Qed.
Lemma result_projection s logical kind a b c d : FormulaProjection.storage s (result s logical kind a b c d).
Proof. change (FormulaProjection.storage s (SchemaNodeRejection.state s)). apply FormulaProjection.strong_storage. unfold SchemaNodeRejection.state,SchemaNode.initialized. ArenaFrame.storage_steps. Qed.
Lemma result_allocation s logical kind a b c d watched :
  length (memory (result s logical kind a b c d) watched)=length (memory s watched).
Proof. destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply result_meta_length|now rewrite result_other by assumption]. Qed.
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
Lemma accepted_impossible logical kind a b c d :
  (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) ->
  forall reply next, ~Protocol.accepted logical (Protocol.Req 22 [kind;a;b;c;d] []) reply next.
Proof.
  intros Hnone reply next Haccepted. inversion Haccepted;subst;
    first [match goal with H:Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H:Protocol.proof_request _ _ _ |- _ => inversion H end
      |apply Hnone;eexists;eassumption].
Qed.
Theorem logical_rejected logical kind a b c d :
  (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) ->
  NoDup (Protocol.formulas logical) ->
  Protocol.step logical (Protocol.Req 22 [kind;a;b;c;d] []) Protocol.NO logical.
Proof.
  intros Hnone Hunique. apply Protocol.step_reject;[now apply accepted_impossible|now apply HistoryRefinement.retained_refl].
Qed.

Definition basic kind := kind=0%nat \/ kind=1%nat \/ kind=2%nat \/ kind=11%nat \/ (12<=kind)%nat.
Lemma invalid_of_absence s logical kind a b c d : basic kind -> Guarantees.safe logical -> Z.of_nat a<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical ->
  (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) ->
  SchemaNodeRejection.invalid s kind a.
Proof.
  intros Hbasic Hsafe Ha Harena Hclasses Hhistory Hnone.
  destruct Hbasic as [->|[->|[->|[->|Hlarge]]]].
  - left. split;[reflexivity|].
    assert (Hnot:~Z.of_nat a<maximum).
    { intro Hsmall. apply Hnone. exists (Protocol.CE (Schemata.metavariable a)). constructor. exact Hsmall. }
    lia.
  - right;left. split;[reflexivity|].
    destruct (nth_error (Protocol.classes logical) a) as [cls|] eqn:Hlookup.
    + exfalso. apply Hnone. exists (Protocol.CE (Schemata.literal_class cls)). constructor. exact Hlookup.
    + apply nth_error_None in Hlookup. rewrite (proj1 Hclasses). lia.
  - right;right;left. split;[reflexivity|].
    destruct (nth_error (Protocol.formulas logical) a) as [formula|] eqn:Hlookup.
    + exfalso. apply Hnone. exists (Protocol.FE (Schemata.literal_formula formula)). constructor. exact Hlookup.
    + apply nth_error_None in Hlookup. rewrite (proj1 (proj2 (proj1 Harena))). lia.
  - right;right;right;left. split;[reflexivity|].
    destruct (nth_error (Protocol.history logical) a) as [fid|] eqn:Hlookup.
    + destruct ((proj1 Hsafe) a fid Hlookup) as [formula [Hformula Hchecked]].
      exfalso. apply Hnone. exists (Protocol.PE (Schemata.saved_theorem formula Hchecked)). constructor.
      unfold Protocol.theorem_at. rewrite Hlookup. exact Hformula.
    + apply nth_error_None in Hlookup. rewrite (proj1 Hhistory). lia.
  - right;right;right;right. exact Hlarge.
Qed.

Theorem generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars -> basic kind -> Guarantees.safe logical ->
  (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) ->
  (19<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat kind<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaRepresentation.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
  stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
  exists final,
    final=result (ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail) logical kind a b c d /\
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 22 [kind;a;b;c;d] []) Protocol.NO logical /\
    NativeRepresentation.canonical_arena final (Protocol.formulas logical) /\
    ClassStorage.represents final (Protocol.formulas logical) (Protocol.classes logical) /\
    HistoryRefinement.represents final logical /\
    NameRepresentation.represents final (Protocol.bindings logical) /\
    SchemaRepresentation.represents final logical /\
    (forall watched,length (memory final watched)=length (memory s watched)) /\
    meta_value final 8=0 /\
    (FormulaTopology.ordered s (length (Protocol.formulas logical)) -> FormulaTopology.ordered final (length (Protocol.formulas logical))) /\
    (Guarantees.safe logical -> Guarantees.safe logical).
Proof.
  intros Hencoding Hbasic Hsafe Hnone Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  destruct (ReadFive.generated_reads s 22 ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
    ltac:(lia) Htoken Hbuffer Hpending Herror ltac:(unfold maximum;lia) Hencoding Hkind
    Ha Hb Hc Hd Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hfifth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFive.fifth_state s ch chars kind sep1 a sep2 b sep3 c sep4 d sep5 tail).
  set (final:=result arg logical kind a b c d).
  assert (Hargmeta:(19<length (memory arg arraydef_0__meta))%nat).
  { unfold arg. now rewrite ReadFive.fifth_meta_length. }
  assert (Harg_schema:SchemaRepresentation.represents arg logical).
  { eapply SchemaRepresentation.transport;[exact Hschemas| | |reflexivity|reflexivity|reflexivity].
    - unfold arg. apply ReadFive.fifth_meta_other;lia.
    - unfold arg. apply ReadFive.fifth_other;discriminate. }
  assert (Hinvalid:SchemaNodeRejection.invalid s kind a).
  { exact (invalid_of_absence s logical kind a b c d Hbasic Hsafe Ha Harena Hclasses Hhistory Hnone). }
  assert (Harginvalid:SchemaNodeRejection.invalid arg kind a).
  { unfold SchemaNodeRejection.invalid,arg. rewrite !ReadFive.fifth_meta_other by lia. exact Hinvalid. }
  pose proof (SchemaNodeRejection.generated_rejected arg (fun _=>false)
    (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d))
    kind a observations Hargmeta eq_refl eq_refl Harginvalid) as Hhelper.
  change (execObserved (funcdef_0__schemaNode (fun _=>false)
    (SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)))
    (arg,observations)=Some (tt,(final,observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin arg|}]))) in Hhelper.
  assert (Hfinalmeta:(8<length (memory final arraydef_0__meta))%nat).
  { unfold final. rewrite result_meta_length. lia. }
  assert (Hfinalerror:meta_value final 8=0).
  { unfold final. rewrite result_meta_other by lia. unfold arg. rewrite ReadFive.fifth_meta_other by lia. exact Herror. }
  pose proof (SchemaNodeCommand.generated_command s bs ns _ _ _ _ _ arg final (Z.of_nat kind) (Z.of_nat a)
    (Z.of_nat b) (Z.of_nat c) (Z.of_nat d) observations _ Hopcode Hfirst Hsecond Hthird Hfourth Hfifth Hhelper Hfinalmeta Hfinalerror) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput. rewrite Hinput,Houtput in Hrun.
  assert (Harrays:forall name,name<>arraydef_0__meta -> name<>arraydef_0__token -> memory final name=memory s name).
  { intros name Hm Ht. unfold final. rewrite result_other by assumption. unfold arg. now apply ReadFive.fifth_other. }
  assert (Hcells:forall i,i<>6%nat -> i<>11%nat -> i<>14%nat -> i<>15%nat ->
    i<>17%nat -> i<>18%nat -> i<>19%nat -> meta_value final i=meta_value s i).
  { intros i H6 H11 H14 H15 H17 H18 H19. unfold final. rewrite result_meta_other by assumption.
    unfold arg. apply ReadFive.fifth_meta_other;[lia|exact H6|exact H11|exact H14|exact H15|exact H17]. }
  exists final. split;[reflexivity|]. split;[exact Hrun|]. split.
  - apply logical_rejected;[exact Hnone|exact (SemanticFrames.arena_NoDup s _ Harena)].
  - split.
    + eapply FormulaProjection.storage_arena;[unfold final;apply result_projection|].
      eapply ArenaFrame.storage_arena;[unfold arg;apply ReadFive.fifth_storage;lia|exact Harena].
    + split.
      * replace (Protocol.formulas logical) with (Protocol.formulas logical++[]) at 1 by apply app_nil_r.
        eapply SemanticFrames.classes_extend;[apply Hcells;lia|apply Harrays;discriminate|exact Hclasses].
      * split.
        -- eapply SemanticFrames.history_transport;[apply Hcells;lia|apply Harrays;discriminate|exact Hhistory].
        -- split.
           ++ unfold NameRepresentation.represents in *. rewrite (Hcells 4%nat),(Hcells 5%nat) by lia.
              rewrite (Harrays arraydef_0__names),(Harrays arraydef_0__bindings) by discriminate. exact Hnames.
           ++ split.
              ** eapply SchemaRepresentation.transport;[exact Hschemas|apply Hcells;lia|apply Harrays;discriminate|reflexivity|reflexivity|reflexivity].
              ** split.
                 --- intro watched. unfold final. rewrite result_allocation. unfold arg. apply argument_allocation.
                 --- split;[exact Hfinalerror|]. split.
                     +++ intro Hordered. apply (FormulaTopology.same s final _ Hordered). intros parent Hparent.
                         unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate.
                     +++ auto.
Qed.
End SchemaBasicRejectionProtocol.
