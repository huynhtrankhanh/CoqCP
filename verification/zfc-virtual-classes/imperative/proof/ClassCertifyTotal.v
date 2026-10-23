From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash TokenByte ClassCertifyProtocol ClassCertifyRejection ClassCertifyCommand
  RenameMemoClassSetness RenameMemoResourceBounds FormulaTopology Representation ClassStorage ClassLookup HistoryRefinement
  NameRepresentation SchemaMetadata LogicalNames LogicalHistory.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassCertifyTotal.
Import IndexExecution SipHashExecution.
Definition capacity s logical name tid reserve := forall cls flag c p,
  Protocol.lookup name (Protocol.bindings logical)=Some (Protocol.class_binding cls flag) ->
  Protocol.class_at logical cls=Some c -> Protocol.theorem_at logical tid=Some p ->
  RenameMemoClassSetness.ready s (Protocol.formulas logical) cls c /\
  Z.of_nat (length (Protocol.formulas logical)+RenameMemoClassSetness.work s cls c+reserve)<=RenameMemoResourceBounds.doubling_limit.
Theorem generated_total_protocol s logical bs ns name tid first middle last tail reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  (1024<=length (memory s arraydef_0__token))%nat -> (20<=length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15=50 -> meta_value s 8=0 -> Protocol.valid_name name -> Z.of_nat tid<=maximum ->
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) -> FormulaTopology.ordered s (length (Protocol.formulas logical)) ->
  nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
  ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
  HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
  SchemaMetadata.represents s (Protocol.expressions logical) -> NoDup (map fst (Protocol.bindings logical)) ->
  LogicalNames.valid logical -> LogicalHistory.valid logical -> capacity s logical name tid reserve ->
  TokenByteExecution.separator first -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s=52::first::name++middle::decimalBytes tid++last::tail ->
  exists final reply after,
    execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(final,
      observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes reply;unreadInput:=tail|}])) /\
    Protocol.step logical (Protocol.Req 14 [tid] name) reply after /\
    NativeRepresentation.canonical_arena final (Protocol.formulas after) /\
    ClassStorage.represents final (Protocol.formulas after) (Protocol.classes after) /\
    HistoryRefinement.represents final after /\ NameRepresentation.represents final (Protocol.bindings after) /\
    SchemaMetadata.represents final (Protocol.expressions after).
Proof.
  intros Hmeta Hsip Htoken Hbuffer Hpending Herror Hvalid Htidword Harena Htopology Hfalse Hclasses Hwellformed Hhistory
    Hnames Hschemas Hunique Hvalidnames Hvalidhistory Hcapacity Hsep1 Hsep2 Hsep3 Hin.
  destruct (Protocol.lookup name (Protocol.bindings logical)) as [meaning|] eqn:Hlookup.
  - destruct meaning as [cls flag|formula|root].
    + destruct (LogicalNames.lookup_valid logical name _ Hvalidnames Hlookup) as [c Hclass].
      destruct (nth_error (Protocol.history logical) tid) as [fid|] eqn:Hhistoryentry.
      * destruct (Hvalidhistory tid fid Hhistoryentry) as [p Hformula].
        assert (Htheorem : Protocol.theorem_at logical tid=Some p).
        { unfold Protocol.theorem_at. now rewrite Hhistoryentry. }
        destruct (Hcapacity cls flag c p Hlookup Hclass Htheorem) as [Hready Hbudget].
        destruct (ClassCertifyProtocol.generated_named_protocol s logical bs ns name cls c flag tid p first middle last tail reserve observations
          Hmeta Hsip Htoken Hbuffer Hpending Herror Hvalid Htidword Harena Htopology Hfalse Hclasses Hwellformed Hhistory Hnames Hschemas Hunique
          Hlookup Hclass Htheorem Hready Hbudget Hsep1 Hsep2 Hsep3 Hin)
          as (final & next & matches & Hrun & Hmatches & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next & Hprefix & Hremaining).
        exists final,(ClassCertifyCommand.reply cls matches),(ClassCertifyProtocol.target logical next name cls matches).
        repeat first [assumption|split].
      * assert (Hinvalid : ClassCertifyRejection.invalid logical name tid).
        { intros other cert Hbinding. exact Hhistoryentry. }
        destruct (ClassCertifyRejection.generated_rejected_protocol s logical bs ns name tid first middle last tail observations
          ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Hinvalid Hsep1 Hsep2 Hsep3 Hin)
          as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next).
        exists final,Protocol.NO,logical. repeat first [assumption|split].
    + assert (Hinvalid : ClassCertifyRejection.invalid logical name tid) by (intros other cert Hbinding; congruence).
      destruct (ClassCertifyRejection.generated_rejected_protocol s logical bs ns name tid first middle last tail observations
        ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Hinvalid Hsep1 Hsep2 Hsep3 Hin)
        as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next).
      exists final,Protocol.NO,logical. repeat first [assumption|split].
    + assert (Hinvalid : ClassCertifyRejection.invalid logical name tid) by (intros other cert Hbinding; congruence).
      destruct (ClassCertifyRejection.generated_rejected_protocol s logical bs ns name tid first middle last tail observations
        ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Hinvalid Hsep1 Hsep2 Hsep3 Hin)
        as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next).
      exists final,Protocol.NO,logical. repeat first [assumption|split].
  - assert (Hinvalid : ClassCertifyRejection.invalid logical name tid) by (intros other cert Hbinding; congruence).
    destruct (ClassCertifyRejection.generated_rejected_protocol s logical bs ns name tid first middle last tail observations
      ltac:(lia) Htoken Hpending Herror Hvalid Htidword Harena Hclasses Hhistory Hnames Hschemas Hinvalid Hsep1 Hsep2 Hsep3 Hin)
      as (final & Hrun & Hstep & Harena_next & Hclasses_next & Hhistory_next & Hnames_next & Hschemas_next).
    exists final,Protocol.NO,logical. repeat first [assumption|split].
Qed.
End ClassCertifyTotal.
