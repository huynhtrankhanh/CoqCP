From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal FormulaEncoding Representation FormulaTopology ArenaFrame
  Intern InternReserve AxiomRefl AxiomK AxiomSRefinement AxiomStorage FormulaCircuit
  AxiomReplacementCircuits AxiomReplacementRaw RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition AxiomReplacementRefinement SchemaEvaluationIndexReplacementCircuit SchemaEvaluationIndexAxiomCircuits SchemaEvaluationIndexBounds SchemaEvaluationIndexCircuit.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexAxiomReplacement.
Import IndexExecution SipHashExecution ObservedLocal AxiomReplacementRefinement SchemaEvaluationIndexAxiomCircuits.
Module C:=AxiomReplacementCircuits.
Theorem generated_refines s bs ns fs p root bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs root=Some p -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__axiom_tag=16 -> ns vardef_0__axiom_p=Z.of_nat root ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+2<=maximum -> Z.of_nat (RenameMemoTransition.height p)<=maximum ->
  Z.of_nat (length fs+3*(S root*S root)+21+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists built next, SchemaEvaluationIndexBounds.raw_arena (AxiomRefl.finished built) (length next) (bound+3) /\
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)) /\
    NativeRepresentation.canonical_arena (AxiomRefl.finished built) next /\
    meta_value (AxiomRefl.finished built) 13=1 /\ meta_value (AxiomRefl.finished built) 8=0 /\
    word (meta_value (AxiomRefl.finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (AxiomRefl.finished built) 0))=Some (SetTheory.replacement p) /\
    SetTheory.derives (SetTheory.replacement p) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (AxiomRefl.finished built) (length next) /\
    (length next<=length fs+3*(S root*S root)+21)%nat /\ AxiomStorage.logical_frame s (AxiomRefl.finished built).
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hlookup Hfalse Htag Hroot Hfuel Hbound Hindices Hheight Hbudget HrawInitial.
  assert (Hrootword:word (Z.of_nat root)).
  { assert (Hlt:(root<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. unfold word,maximum. rewrite !Nat2Z.inj_add in Hbudget. lia. }
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hclear_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Htopology) as Hclear_topology.
  assert (Hclear_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  assert (Hclear_meta:(31<length (memory (AxiomRefl.cleared s) arraydef_0__meta))%nat)
    by (unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  assert (Hclear_sip:(0<length (memory (AxiomRefl.cleared s) arraydef_0__sipState))%nat)
    by (unfold AxiomRefl.cleared;rewrite store_meta_other by discriminate;exact Hsip).
  assert (Hrep:FormulaCircuit.represents fs [0] [SetTheory.falsity]).
  { constructor;[split;[unfold word,maximum;lia|exact Hfalse]|constructor]. }
  assert (Hreserve:Z.of_nat (length fs+C.reserve_cost root C.plan+reserve)<=9223372036854775807)
    by (rewrite plan_cost;replace (length fs+(3*(S root*S root)+21)+reserve)%nat with (length fs+3*(S root*S root)+21+reserve)%nat by lia;exact Hbudget).
  destruct (SchemaEvaluationIndexReplacementCircuit.complete (bound+3)%nat C.plan (AxiomRefl.cleared s) fs [0] [SetTheory.falsity] p root bound (C.values p) reserve observations
    Hclear_meta Hclear_sip Hclear_arena Hclear_topology Hclear_error Hlookup Hfalse Hfuel Hbound Hindices Hheight Hrep
    C.plan_fits (C.inferred p) Hreserve
    (SchemaEvaluationIndexBounds.raw_arena_mono (AxiomRefl.cleared s) (length fs) bound (bound+3) ltac:(lia)
      (storage_raw s (AxiomRefl.cleared s) (length fs) bound Hclear HrawInitial)) ltac:(lia)
    ltac:(unfold C.plan;repeat constructor;cbn [SchemaEvaluationIndexReplacementCircuit.instruction_bound SchemaEvaluationIndexCircuit.operation_bound];lia))
    as (built & next & ids & HrawBuilt & Htrace & Hnext & Hnexttopology & Hnexterror & Hnextrep & Hprefix & Hgrowth & Hremaining & Hm & Hs).
  assert (Hrun:execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations))).
  { apply (AxiomReplacementRaw.generated_helper s bs ns (Z.of_nat root) built ids observations);try assumption;[lia|].
    eapply AxiomSRefinement.source_reference;[exact Harena|exact Hrootword|now rewrite Nat2Z.id,Hlookup]. }
  destruct (C.result observations (Z.of_nat root) (AxiomRefl.cleared s) built ids next p Htrace Hnextrep)
    as (Hword & Hmeaning & Hderives).
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat) by (rewrite Hm;lia).
  destruct (AxiomK.finishing_result built Hbuiltmeta) as (Hsuccess & Hfinalerror & Hfinalid).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hfinalid.
  exists built,next. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) _ (AxiomRefl.finished_storage built) HrawBuilt)|]. split;[exact Hrun|].
  split;[eapply ArenaFrame.storage_arena;[apply AxiomRefl.finished_storage|exact Hnext]|].
  split;[exact Hsuccess|]. split;[unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hnexterror|].
  split;[now rewrite Hfinalid|]. split;[now rewrite Hfinalid|]. split;[exact Hderives|].
  split;[exact Hprefix|]. split;[exact Hremaining|].
  split;[eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Hnexttopology]|].
  split;[rewrite plan_cost in Hgrowth;lia|]. eapply AxiomStorage.generated_frame;exact Hrun.
Qed.
End SchemaEvaluationIndexAxiomReplacement.
