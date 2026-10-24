From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal TokenByte ReadFive ReadFour ReadTwo ReadOne DecimalInput CommandArgs
  SchemaNode SchemaNodeMeaning SchemaNodeCommand SchemaRepresentation SchemaMetadata
  ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement NameRepresentation SemanticFrames
  ReplyNO FormulaTopology HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaReferenceRejection.
Import IndexExecution SipHashExecution ObservedLocal.

Definition result s logical kind a b c d :=
  ReplyNOExecution.reply_state (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d).
Lemma result_meta_length s logical kind a b c d :
  length (memory (result s logical kind a b c d) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result. rewrite ReplyNOExecution.reply_memory. apply SchemaNode.reference_length. Qed.
Lemma result_meta_other s logical kind a b c d i : i<>18%nat -> i<>19%nat ->
  meta_value (result s logical kind a b c d) i=meta_value s i.
Proof. intros H18 H19. unfold result,meta_value. rewrite ReplyNOExecution.reply_memory. apply SchemaNode.reference_meta_other;assumption. Qed.
Lemma result_other s logical kind a b c d name : name<>arraydef_0__meta ->
  memory (result s logical kind a b c d) name=memory s name.
Proof. intro Hmeta. unfold result. rewrite ReplyNOExecution.reply_memory. now apply SchemaNode.reference_other. Qed.
Lemma result_projection s logical kind a b c d : FormulaProjection.storage s (result s logical kind a b c d).
Proof. change (FormulaProjection.storage s (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d)). apply SchemaNode.reference_projection. Qed.
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

Theorem generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars -> (3<=kind<=10)%nat ->
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
  intros Hencoding Hrange Hnone Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd
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
  set (arguments:=SchemaNodeCommand.arguments (Z.of_nat kind) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) (Z.of_nat d)).
  set (validated:=setMachine (SchemaNode.typed_frame {|machine:=arg;bools:=fun _=>false;nums:=arguments|} (SchemaNode.reference_type kind))
    (SchemaNode.reference_state arg (Protocol.expressions logical) kind a b c d)).
  assert (Hprefix:execLocalObserved SchemaNode.prefix ({|machine:=arg;bools:=fun _=>false;nums:=arguments|},observations)=Some (tt,(validated,observations))).
  { apply SchemaNode.generated_reference_prefix_total;try assumption;try reflexivity. exact (proj1 Harg_schema). }
  assert (HvalidatedMeta:(19<length (memory (machine validated) arraydef_0__meta))%nat).
  { unfold validated. cbn [machine setMachine]. now rewrite SchemaNode.reference_length. }
  assert (Hrejected:meta_value (machine validated) 18=0).
  { unfold validated. cbn [machine setMachine]. now apply SchemaNodeMeaning.reference_rejected. }
  pose proof (SchemaNode.generated_after_prefix_rejected arg (fun _=>false) arguments validated observations Hprefix HvalidatedMeta Hrejected) as Hhelper.
  unfold validated in Hhelper. cbn [machine setMachine] in Hhelper.
  rewrite SchemaNode.reference_output,SchemaNode.reference_input in Hhelper.
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
End SchemaReferenceRejection.
