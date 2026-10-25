From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Schemata Protocol Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives TokenByte ReadFour ReadTwo ReadOne DecimalInput CommandArgs
  AxiomCommand AxiomDispatch AxiomReject AxiomReferenceReject CommandQuit CommandStructure CommandDispatch CommandChain RenameMemoControl
  ArenaFrame FormulaProjection Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation SemanticFrames
  ReplyNO FormulaTopology HashTable InternInvariant.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomRejectionProtocol.
Import IndexExecution SipHashExecution ObservedLocal.

Local Opaque funcdef_0__axiom funcdef_0__appendTheorem funcdef_0__no Imperative.update.
Theorem generated_handler reader (f:AxiomCommand.Frame) first second third fourth built tag a b c observations :
  (17<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  AxiomCommand.read_result reader (machine f) first tag observations ->
  AxiomCommand.read_result reader first second a observations ->
  AxiomCommand.read_result reader second third b observations ->
  AxiomCommand.read_result reader third fourth c observations ->
  execObserved (funcdef_0__axiom (fun _=>false) (AxiomCommand.arguments tag a b c)) (fourth,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 13=0 -> meta_value built 8=0 ->
  execLocalObserved (CommandStructure.handler_11 reader) (f,observations)=
    Some (tt,(setMachine (AxiomCommand.locals f tag a b c) (ReplyNOExecution.reply_state built),
      observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}])).
Proof.
  intros Hinitial Herror [Hread1 [Hmeta1 [Hvalue1 [Hvalid1 Herror1]]]]
    [Hread2 [Hmeta2 [Hvalue2 [Hvalid2 Herror2]]]]
    [Hread3 [Hmeta3 [Hvalue3 [Hvalid3 Herror3]]]]
    [Hread4 [Hmeta4 [Hvalue4 [Hvalid4 Herror4]]]] Haxiom Hbuilt Hsuccess Hbuilt_error.
  destruct f as [s bs ns]; cbn [machine] in *; unfold CommandStructure.handler_11.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hbuilt]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta4]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta3]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta2]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta1]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?callee ?bo ?no) ?state] =>
       let expression:=constr:(@execObserved I T EI R (callee bo no) state) in
       let Hrun:=fresh in first
         [assert (Hrun:expression=Some (tt,(first,observations))) by exact Hread1
         |assert (Hrun:expression=Some (tt,(second,observations))) by exact Hread2
         |assert (Hrun:expression=Some (tt,(third,observations))) by exact Hread3
         |assert (Hrun:expression=Some (tt,(fourth,observations))) by exact Hread4
         |assert (Hrun:expression=Some (tt,(built,observations))) by exact Haxiom]; rewrite Hrun;clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(ReplyNOExecution.reply_state current,
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}]))) by
         apply ReplyNOExecution.generated_no;rewrite Hrun;clear Hrun end
    |progress rewrite Herror |progress rewrite Herror1 |progress rewrite Herror2 |progress rewrite Herror3 |progress rewrite Herror4
    |progress rewrite Hvalid1 |progress rewrite Hvalid2 |progress rewrite Hvalid3 |progress rewrite Hvalid4
    |progress rewrite Hvalue1 |progress rewrite Hvalue2 |progress rewrite Hvalue3 |progress rewrite Hvalue4
    |progress rewrite Hsuccess
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 13) with 13%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
  unfold AxiomCommand.locals;reflexivity.
Qed.
Theorem generated_command s bs ns opstate first second third fourth built tag a b c observations :
  AxiomCommand.read_result funcdef_0__readNat s opstate 11 observations ->
  AxiomCommand.read_result funcdef_0__readNat opstate first tag observations ->
  AxiomCommand.read_result funcdef_0__readNat first second a observations ->
  AxiomCommand.read_result funcdef_0__readNat second third b observations ->
  AxiomCommand.read_result funcdef_0__readNat third fourth c observations ->
  execObserved (funcdef_0__axiom (fun _=>false) (AxiomCommand.arguments tag a b c)) (fourth,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 13=0 -> meta_value built 8=0 ->
  execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(ReplyNOExecution.reply_state built,
    observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}])).
Proof.
  intros [Hopcode [Hopmeta [Hopnumber [Hopvalid Hoperror]]]] Hfirst Hsecond Hthird Hfourth
    Haxiom Hbuilt Hsuccess Herror.
  set (initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} opstate 11).
  set (after:=setMachine (AxiomCommand.locals initial tag a b c) (ReplyNOExecution.reply_state built)).
  apply (CommandDispatch.generated_positive_command s bs ns after opstate 11 observations
    (observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}])) ; try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandChain.handler_for funcdef_0__readNat 11) (initial,observations)=
      Some (tt,(after,observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin built|}]))).
    eapply generated_handler; eassumption.
  - change (8<length (memory (ReplyNOExecution.reply_state built) arraydef_0__meta))%nat.
    rewrite ReplyNOExecution.reply_memory. lia.
Qed.

Lemma valid_concrete s logical tag a b c :
  meta_value s 1=Z.of_nat (length (Protocol.formulas logical)) ->
  (tag<18)%nat ->
  AxiomDispatch.references_valid {|machine:=s;bools:=fun _=>false;nums:=AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)|} (Z.of_nat tag) ->
  exists formula, Protocol.concrete_axiom logical tag a b c=Some formula.
Proof.
  intros Hcount Htag Hvalid.
  unfold AxiomDispatch.references_valid in Hvalid. cbn [machine] in Hvalid.
  rewrite Hcount in Hvalid.
  let rec cases count tag := lazymatch count with
  | O=>idtac
  | S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next]
  end in cases 18%nat tag.
  all: try lia.
  all: lazymatch type of Hvalid with Forall ?P (AxiomDispatch.reference_names ?selector) =>
    let names:=eval compute in (AxiomDispatch.reference_names selector) in change (Forall P names) in Hvalid end.
  all: repeat match goal with H:Forall _ (_::_) |- _ => inversion H;clear H end.
  all: unfold AxiomCommand.arguments in *;cbn [nums] in *.
  all: repeat first [progress rewrite RenameMemoControl.updated_same in *
    |progress rewrite RenameMemoControl.updated_other in * by discriminate].
  all: unfold Protocol.concrete_axiom,Protocol.formula_at;cbn.
  all: destruct (nth_error (Protocol.formulas logical) a) as [pa|] eqn:Ha;
      destruct (nth_error (Protocol.formulas logical) b) as [pb|] eqn:Hb;
      destruct (nth_error (Protocol.formulas logical) c) as [pc|] eqn:Hc.
  all: cbn;try (eexists;reflexivity).
  all: repeat match goal with H:nth_error _ _=None |- _=>apply nth_error_None in H end.
  all: exfalso;lia.
Qed.
Lemma rejection_cases s logical tag a b c :
  meta_value s 1=Z.of_nat (length (Protocol.formulas logical)) ->
  Protocol.concrete_axiom logical tag a b c=None ->
  (18<=tag)%nat \/
  ~AxiomDispatch.references_valid {|machine:=s;bools:=fun _=>false;nums:=AxiomCommand.arguments (Z.of_nat tag) (Z.of_nat a) (Z.of_nat b) (Z.of_nat c)|} (Z.of_nat tag).
Proof.
  intros Hcount Hnone. destruct (lt_dec tag 18) as [Hsupported|Hunsupported];[right|left;lia].
  intro Hvalid. destruct (valid_concrete s logical tag a b c Hcount Hsupported Hvalid) as [formula Hsome]. congruence.
Qed.
Lemma accepted_impossible logical tag a b c : Protocol.concrete_axiom logical tag a b c=None ->
  forall reply next, ~Protocol.accepted logical (Protocol.Req 11 [tag;a;b;c] []) reply next.
Proof.
  intros Hnone reply next Haccepted. inversion Haccepted;subst;
    first [match goal with H:Protocol.formula_request _ _ _ |- _ => inversion H end
      |match goal with H:Protocol.proof_request _ _ _ |- _ => inversion H;subst;congruence end].
Qed.
Theorem logical_rejected logical tag a b c : Protocol.concrete_axiom logical tag a b c=None ->
  NoDup (Protocol.formulas logical) -> Protocol.step logical (Protocol.Req 11 [tag;a;b;c] []) Protocol.NO logical.
Proof. intros Hnone Hunique. apply Protocol.step_reject;[now apply accepted_impossible|now apply HistoryRefinement.retained_refl]. Qed.

Definition result s := ReplyNOExecution.reply_state (AxiomReject.result s).
Lemma result_meta_length s : length (memory (result s) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result,AxiomReject.result. rewrite ReplyNOExecution.reply_memory. apply store_meta_length. Qed.
Lemma result_meta_other s i : i<>13%nat -> meta_value (result s) i=meta_value s i.
Proof. intro Hi. unfold result,meta_value. rewrite ReplyNOExecution.reply_memory. apply meta_store_other;exact Hi. Qed.
Lemma result_other s name : name<>arraydef_0__meta -> memory (result s) name=memory s name.
Proof. intro Hi. unfold result,AxiomReject.result. rewrite ReplyNOExecution.reply_memory. apply store_meta_other;exact Hi. Qed.
Lemma result_allocation s watched : length (memory (result s) watched)=length (memory s watched).
Proof. destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply result_meta_length|now rewrite result_other by assumption]. Qed.
Lemma argument_allocation s ch chars tag a b c sep1 sep2 sep3 sep4 tail watched :
  length (memory (ReadFour.fourth_state s ch chars tag sep1 a sep2 b sep3 c sep4 tail) watched)=length (memory s watched).
Proof.
  destruct (decide (watched=arraydef_0__meta)) as [->|Hmeta];[apply ReadFour.fourth_meta_length|].
  destruct (decide (watched=arraydef_0__token)) as [->|Htoken].
  - unfold ReadFour.fourth_state,ReadFour.third_state,ReadFour.second_state,
      ReadTwo.second_state,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state.
    now rewrite !DecimalInput.encoded_token_length,CommandArgs.pending_token_length.
  - now rewrite ReadFour.fourth_other by assumption.
Qed.
Theorem generated_rejected s logical bs ns ch chars tag a b c sep0 sep1 sep2 sep3 sep4 tail observations :
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
  stdin s=chars++sep0::decimalBytes tag++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::tail ->
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
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin.
  destruct (ReadFour.generated_reads s 11 ch chars tag a b c sep0 sep1 sep2 sep3 sep4 tail observations
    Hmeta Htoken Hbuffer Hpending Herror ltac:(unfold maximum;lia) Hencoding Htag
    Ha Hb Hc Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hin)
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
End AxiomRejectionProtocol.
