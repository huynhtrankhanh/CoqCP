From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash TokenByte ReadFive SchemaNode SchemaNodeMeaning
  SchemaNodeProtocol SchemaLiteralProtocol SchemaReferenceProtocol SchemaBasicRejectionProtocol SchemaReferenceRejection
  SchemaRepresentation Representation ClassStorage HistoryRefinement NameRepresentation FormulaTopology.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaNodeTotal.
Import IndexExecution SipHashExecution.

(** Constructive decision of descriptor formation. Saved proof constants use the
    existing history invariant; reference nodes use the native finite validator. *)
Theorem builds_decidable (s:Machine) logical kind a b c d :
  (19<length (memory s arraydef_0__meta))%nat -> Guarantees.safe logical ->
  (exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) \/
  (~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression).
Proof.
  intros Hmeta Hsafe.
  assert (Hcases:kind=0%nat \/ kind=1%nat \/ kind=2%nat \/ (3<=kind<=10)%nat \/ kind=11%nat \/ (12<=kind)%nat) by lia.
  destruct Hcases as [->|[->|[->|[Hrefs|[->|Hunknown]]]]].
  - destruct (Z_lt_dec (Z.of_nat a) maximum) as [Hsmall|Hlarge].
    + left. exists (Protocol.CE (Schemata.metavariable a)). constructor. exact Hsmall.
    + right. intros [expression Hbuild]. inversion Hbuild;subst. apply Hlarge. assumption.
  - destruct (Protocol.class_at logical a) as [cls|] eqn:Hlookup.
    + left. exists (Protocol.CE (Schemata.literal_class cls)). constructor. exact Hlookup.
    + right. intros [expression Hbuild]. inversion Hbuild;subst;congruence.
  - destruct (Protocol.formula_at logical a) as [formula|] eqn:Hlookup.
    + left. exists (Protocol.FE (Schemata.literal_formula formula)). constructor. exact Hlookup.
    + right. intros [expression Hbuild]. inversion Hbuild;subst;congruence.
  - destruct (Z.eq_dec (meta_value (SchemaNode.reference_state s (Protocol.expressions logical) kind a b c d) 18) 0) as [Hzero|Hnonzero].
    + right. intros [expression Hbuild].
      destruct (SchemaNodeMeaning.reference_metadata s logical kind a b c d expression Hmeta Hbuild Hrefs) as [Hflag _].
      lia.
    + left. exact (SchemaNodeMeaning.reference_builds s logical kind a b c d Hmeta Hrefs Hnonzero).
  - destruct (Protocol.theorem_at logical a) as [formula|] eqn:Hlookup.
    + left. pose proof (Guarantees.theorem_sound logical a formula (proj1 Hsafe) Hlookup) as Hderive.
      exists (Protocol.PE (Schemata.saved_theorem formula Hderive)). constructor. exact Hlookup.
    + right. intros [expression Hbuild]. inversion Hbuild;subst;congruence.
  - right. intros [expression Hbuild]. inversion Hbuild;subst;lia.
Qed.

(** One actual separator-terminated opcode 22 command, including its observable
    reply, unread suffix, object-calculus transition and complete storage relation. *)
Definition checked_step s logical bs ns kind a b c d tail observations final reply next : Prop :=
  execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
    observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
  Protocol.step logical (Protocol.Req 22 [kind;a;b;c;d] []) reply next /\
  NativeRepresentation.canonical_arena final (Protocol.formulas next) /\
  ClassStorage.represents final (Protocol.formulas next) (Protocol.classes next) /\
  HistoryRefinement.represents final next /\
  NameRepresentation.represents final (Protocol.bindings next) /\
  SchemaRepresentation.represents final next /\
  (forall watched,watched<>arraydef_0__schemaNodes -> length (memory final watched)=length (memory s watched)) /\
  meta_value final 8=0 /\
  (FormulaTopology.ordered s (length (Protocol.formulas logical)) -> FormulaTopology.ordered final (length (Protocol.formulas next))) /\
  Guarantees.safe next.

Theorem generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars -> Guarantees.safe logical -> Protocol.builds_node logical [kind;a;b;c;d] expression ->
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
  exists final, checked_step s logical bs ns kind a b c d tail observations final
    (Protocol.OK (length (Protocol.expressions logical))) (SchemaRepresentation.with_expression logical expression).
Proof.
  intros Hencoding Hsafe Hbuild Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hc Hd Hcapacity
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  assert (Hcases:kind=0%nat \/ (kind=1%nat \/ kind=2%nat \/ kind=11%nat) \/ (3<=kind<=10)%nat).
  { inversion Hbuild;subst;lia. }
  destruct Hcases as [Hzero|[Hliteral|Hrefs]].
  - subst kind. inversion Hbuild;subst.
    assert (Hsmall:Z.of_nat a<maximum) by assumption.
    destruct (SchemaNodeProtocol.generated_variable s logical bs ns ch chars a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hmeta Htoken Hbuffer Hpending Herror ltac:(lia) Hb Hc Hd Hcapacity
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
      as (final & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hlen & Herror' & Htop & Hsafe').
    exists final. unfold checked_step. cbn [SchemaRepresentation.with_expression Protocol.formulas Protocol.classes Protocol.bindings].
    repeat first [assumption|exact (Hsafe' Hsafe)|split].
  - destruct (SchemaLiteralProtocol.generated_literal s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hliteral Hbuild Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hc Hd Hcapacity
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
      as (final & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hlen & Herror' & Htop & Hsafe').
    exists final. unfold checked_step. cbn [SchemaRepresentation.with_expression Protocol.formulas Protocol.classes Protocol.bindings].
    repeat first [assumption|exact (Hsafe' Hsafe)|split].
  - destruct (SchemaReferenceProtocol.generated_reference s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hrefs Hbuild Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hc Hd Hcapacity
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
      as (final & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hlen & Herror' & Htop & Hsafe').
    exists final. unfold checked_step. cbn [SchemaRepresentation.with_expression Protocol.formulas Protocol.classes Protocol.bindings].
    repeat first [assumption|exact (Hsafe' Hsafe)|split].
Qed.
Theorem generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars -> Guarantees.safe logical ->
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
  exists final, checked_step s logical bs ns kind a b c d tail observations final Protocol.NO logical.
Proof.
  intros Hencoding Hsafe Hnone Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  assert (Hcases:SchemaBasicRejectionProtocol.basic kind \/ (3<=kind<=10)%nat).
  { unfold SchemaBasicRejectionProtocol.basic. lia. }
  destruct Hcases as [Hbasic|Hrefs].
  - destruct (SchemaBasicRejectionProtocol.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hbasic Hsafe Hnone Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
      as (final & Hresult & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hlen & Herror' & Htop & Hsafe').
    exists final. unfold checked_step. repeat first [assumption|split]. intros watched _. apply Hlen.
  - destruct (SchemaReferenceRejection.generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hrefs Hnone Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin)
      as (final & Hresult & Hrun & Hstep & Hfa & Hfc & Hfh & Hfn & Hfs & Hlen & Herror' & Htop & Hsafe').
    exists final. unfold checked_step. repeat first [assumption|split]. intros watched _. apply Hlen.
Qed.
Theorem generated_total s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations :
  decimalBytes 22=ch::chars -> Guarantees.safe logical ->
  (19<length (memory s arraydef_0__meta))%nat -> (1024<=length (memory s arraydef_0__token))%nat ->
  (20<=length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15=ch+1 -> meta_value s 8=0 ->
  Z.of_nat kind<=maximum -> Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> Z.of_nat c<=maximum -> Z.of_nat d<=maximum ->
  Z.of_nat (length (Protocol.expressions logical))<maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaRepresentation.represents s logical ->
  TokenByteExecution.separator sep0 -> TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  TokenByteExecution.separator sep3 -> TokenByteExecution.separator sep4 -> TokenByteExecution.separator sep5 ->
  stdin s=chars++sep0::decimalBytes kind++sep1::decimalBytes a++sep2::decimalBytes b++sep3::decimalBytes c++sep4::decimalBytes d++sep5::tail ->
  exists final reply next,
    checked_step s logical bs ns kind a b c d tail observations final reply next /\
    ((exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression /\
      reply=Protocol.OK (length (Protocol.expressions logical)) /\ next=SchemaRepresentation.with_expression logical expression) \/
     ((~exists expression, Protocol.builds_node logical [kind;a;b;c;d] expression) /\ reply=Protocol.NO /\ next=logical)).
Proof.
  intros Hencoding Hsafe Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd Hcapacity
    Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin.
  destruct (builds_decidable s logical kind a b c d Hmeta Hsafe) as [[expression Hbuild]|Hnone].
  - destruct (generated_accepted s logical bs ns ch chars kind a b c d expression sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hsafe Hbuild Hmeta Htoken Hbuffer Hpending Herror Ha Hb Hc Hd Hcapacity
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin) as [final Hchecked].
    exists final,(Protocol.OK (length (Protocol.expressions logical))),(SchemaRepresentation.with_expression logical expression).
    split;[exact Hchecked|]. left. exists expression. repeat split;try assumption.
  - destruct (generated_rejected s logical bs ns ch chars kind a b c d sep0 sep1 sep2 sep3 sep4 sep5 tail observations
      Hencoding Hsafe Hnone Hmeta Htoken Hbuffer Hpending Herror Hkind Ha Hb Hc Hd
      Harena Hclasses Hhistory Hnames Hschemas Hsep0 Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hin) as [final Hchecked].
    exists final,Protocol.NO,logical. split;[exact Hchecked|]. right. repeat split;try assumption.
Qed.
End SchemaNodeTotal.
