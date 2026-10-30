From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives TokenByte ReadFour ReadTwo ReadOne DecimalInput CommandArgs
  AxiomCommand AxiomDispatch AxiomReject AxiomReferenceReject CommandQuit CommandStructure CommandDispatch CommandChain RenameMemoControl
  ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation SemanticFrames
  ReplyNO FormulaTopology HashTable InternInvariant.
From NativeProof Require Import NativeArgumentReadsFour AxiomRejectionProtocol.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeWhitespaceAxiomReject.
Import IndexExecution SipHashExecution AxiomRejectionProtocol.
Theorem generated_rejected s logical bs ns ch chars tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations :
  decimalBytes 11=ch::chars -> Protocol.concrete_axiom logical tag a b c=None ->
  (17<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat tag<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaRepresentation.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 ->
  Forall TokenByteExecution.separator sp1 -> Forall TokenByteExecution.separator sp2 -> Forall TokenByteExecution.separator sp3 -> Forall TokenByteExecution.separator sp4 ->
  stdin s=chars++sep0::sp1++decimalBytes tag++sep1::sp2++decimalBytes a++sep2::sp3++decimalBytes b++sep3::sp4++decimalBytes c++sep4::tail ->
  exists final,
    final=result (ReadFour.fourth_state s ch chars tag sep1 a sep2 b sep3 c sep4 tail) /\
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.NO;unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 11 [tag;a;b;c] []) Protocol.NO logical /\
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
  intros Hencoding Hnone Hmeta Htoken Hbuffer Hpending Herror Htag Ha Hb Hc
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hin.
  destruct (NativeArgumentReadsFour.generated_reads s 11 ch chars tag a b c sep0 sp1 sep1 sp2 sep2 sp3 sep3 sp4 sep4 tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum;lia) Hencoding Htag
    Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsp1 Hsp2 Hsp3 Hsp4 Hin)
    as (Hopcode & Hfirst & Hsecond & Hthird & Hfourth & Hargbuffer & Hinput & Houtput).
  set (arg:=ReadFour.fourth_state s ch chars tag sep1 a sep2 b sep3 c sep4 tail).
  set (final:=result arg).
  assert (Hargmeta:(17<length (memory arg arraydef_0__meta))%nat).
  { unfold arg. now rewrite ReadFour.fourth_meta_length. }
  assert (Hcount:meta_value arg 1=Z.of_nat (length (Protocol.formulas logical))).
  { unfold arg. rewrite ReadFour.fourth_meta_other by (try exact Hmeta;lia).
    exact (proj1 (proj2 (proj1 Harena))). }
  assert (Hhelper:execObserved (funcdef_0__axiom (fun _=>false)
    (AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)))
    (arg,observations)=Some (tt,(AxiomReject.result arg,observations))).
  { destruct (rejection_cases arg logical tag a b c Hcount Hnone) as [Hunsupported|Hinvalid].
    - apply AxiomReject.generated;[lia|]. right. unfold AxiomCommand.arguments.
      repeat first [progress rewrite RenameMemoControl.updated_same|progress rewrite RenameMemoControl.updated_other by discriminate]. lia.
    - apply AxiomReferenceReject.generated;[lia|].
      change (~AxiomDispatch.references_valid {|machine:=arg;bools:=fun _=>false;
        nums:=AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)|}
        ((AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) vardef_0__axiom_tag)).
      replace ((AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)) vardef_0__axiom_tag) with (Z.of_nat tag).
      + exact Hinvalid.
      + unfold AxiomCommand.arguments. repeat first [progress rewrite RenameMemoControl.updated_same|progress rewrite RenameMemoControl.updated_other by discriminate]. reflexivity. }
  assert (Hbuiltmeta:(17<length (memory (AxiomReject.result arg) arraydef_0__meta))%nat).
  { unfold AxiomReject.result. now rewrite store_meta_length. }
  assert (Hbuilterror:meta_value (AxiomReject.result arg) 8=0).
  { unfold AxiomReject.result. rewrite meta_store_other by lia. unfold arg.
    rewrite ReadFour.fourth_meta_other by (try exact Hmeta;lia). exact Herror. }
  pose proof (generated_command s bs ns _ _ _ _ arg (AxiomReject.result arg) (Z.of_nat tag)
    (Z.of_nat a) (Z.of_nat b) (Z.of_nat c) observations Hopcode Hfirst Hsecond Hthird Hfourth
    Hhelper Hbuiltmeta (AxiomReject.rejected_flag arg ltac:(lia)) Hbuilterror) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  change (execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
    observations++[{|flushedOutput:=stdout arg++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin arg|}]))) in Hrun.
  rewrite Hinput,Houtput in Hrun.
  assert (Harrays:forall name,name<>arraydef_0__meta -> name<>arraydef_0__token -> memory final name=memory s name).
  { intros name Hm Ht. unfold final. rewrite result_other by assumption. unfold arg. now apply ReadFour.fourth_other. }
  assert (Hcells:forall i,i<>6%nat -> i<>11%nat -> i<>13%nat -> i<>14%nat -> i<>15%nat ->
    i<>17%nat -> meta_value final i=meta_value s i).
  { intros i H6 H11 H13 H14 H15 H17. unfold final. rewrite result_meta_other by assumption.
    unfold arg. apply ReadFour.fourth_meta_other;[lia|exact H6|exact H11|exact H14|exact H15|exact H17]. }
  exists final. split;[reflexivity|]. split;[exact Hrun|]. split.
  - apply logical_rejected;[exact Hnone|exact (SemanticFrames.arena_NoDup s _ Harena)].
  - split.
    + eapply ArenaFrame.storage_arena;[|exact Harena].
      split.
      * unfold final. rewrite result_meta_length. unfold arg. apply ReadFour.fourth_meta_length.
      * split;[exact Harrays|]. repeat split;apply Hcells;lia.
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
                 --- split;[exact Hbuilterror|]. split.
                     +++ intro Hordered. apply (FormulaTopology.same s final _ Hordered). intros parent Hparent.
                         unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate.
                     +++ auto.
Qed.
End NativeWhitespaceAxiomReject.
