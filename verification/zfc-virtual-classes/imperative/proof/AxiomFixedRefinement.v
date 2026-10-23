From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal ArenaFrame Intern InternLengths
  FormulaEncoding FormulaTopology Representation FormulaCircuit FormulaCircuitProperties
  AxiomCircuits AxiomRefl AxiomK AxiomFixedCircuits NativeAxiomBuilder AxiomDispatch AxiomStorage.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomFixedRefinement.
Import IndexExecution SipHashExecution ObservedLocal.

Theorem generated_helper which s bs ns built ids observations :
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=AxiomFixedCircuits.selector which ->
  FormulaCircuit.executes observations (AxiomFixedCircuits.plan which) (AxiomRefl.cleared s) [0%Z] built ids ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)).
Proof.
  intros Hmeta Htag Htrace.
  destruct (NativeAxiomBuilder.generated which (AxiomDispatch.cleared_frame {|machine:=s;bools:=bs;nums:=ns|}) built ids observations)
    as [after [Hrun [Hmachine Hafter]]].
  - unfold AxiomDispatch.cleared_frame. cbn [machine setMachine]. now rewrite store_meta_length.
  - exact Htrace.
  - rewrite <- Hmachine. eapply AxiomDispatch.generated_helper; [|exact Htag| |exact Hmeta| |exact Hrun].
    + destruct which;cbn [AxiomFixedCircuits.selector];lia.
    + destruct which;unfold AxiomDispatch.references_valid;cbn [AxiomFixedCircuits.selector AxiomDispatch.reference_names];constructor.
    + rewrite Hafter. exact Htag.
Qed.

Theorem generated_refines which s bs ns fs reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (length fs+length (AxiomFixedCircuits.plan which)+reserve)<=9223372036854775807 ->
  ns vardef_0__axiom_tag=AxiomFixedCircuits.selector which ->
  exists final next index,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)) /\
    SetTheory.derives (SetTheory.axiom_formula (AxiomFixedCircuits.witness which)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
    AxiomRefl.logical_frame s final /\ AxiomStorage.logical_frame s final /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered final (length next) /\
    (length next<=length fs+length (AxiomFixedCircuits.plan which))%nat.
Proof.
  intros Harena Hordered Herror Hmeta Hfalse Hbudget Htag.
  pose proof (AxiomK.clearing_storage s) as Hstorage.
  assert (Hclear : NativeRepresentation.canonical_arena (AxiomRefl.cleared s) fs).
  { exact (ArenaFrame.storage_arena s _ fs Hstorage Harena). }
  assert (Hclearerror : meta_value (AxiomRefl.cleared s) 8=0).
  { unfold AxiomRefl.cleared. rewrite meta_store_other by discriminate. exact Herror. }
  assert (Hclearordered : FormulaTopology.ordered (AxiomRefl.cleared s) (length fs)).
  { exact (AxiomK.storage_topology s _ (length fs) Hstorage Hordered). }
  destruct (AxiomFixedCircuits.construct which (AxiomRefl.cleared s) fs reserve observations
    Hclear Hclearordered Hclearerror Hfalse Hbudget)
    as [built [next [ids [Htrace [Hframe [Hnext [Hflag [Hrep [Hprefix [Hreserve [Htopology Hgrowth]]]]]]]]]]].
  destruct (AxiomFixedCircuits.result observations which (AxiomRefl.cleared s) built ids next Htrace Hrep)
    as [Hresultword [Hmeaning Hderives]].
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuilt : (13<length (memory built arraydef_0__meta))%nat).
  { rewrite Hlength. unfold AxiomRefl.cleared. now rewrite store_meta_length. }
  destruct (AxiomK.finishing_result built Hbuilt) as [Hsuccess [Herrorfinal Hresult]].
  change (meta_value (AxiomRefl.finished built) 13=1) in Hsuccess.
  change (meta_value (AxiomRefl.finished built) 8=meta_value built 8) in Herrorfinal.
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hresult.
  pose proof (generated_helper which s bs ns built ids observations Hmeta Htag Htrace) as Hrun.
  exists (AxiomRefl.finished built),next,(Z.to_nat (meta_value built 0)). split;[exact Hrun|].
  split;[exact (ArenaFrame.storage_arena built _ next (AxiomRefl.finished_storage built) Hnext)|].
  split.
  - rewrite Hresult,Z2Nat.id;[reflexivity|unfold word in Hresultword;lia].
  - split.
    + rewrite Z2Nat.id;[exact Hresultword|unfold word in Hresultword;lia].
    + split;[exact Hmeaning|]. split;[exact Hderives|]. split;[exact Hprefix|].
      split;[now rewrite Herrorfinal|]. split;[exact Hsuccess|].
      split;[exact (AxiomRefl.frame s built Hframe)|].
      split;[exact (AxiomStorage.generated_frame s bs ns _ observations observations Hrun)|].
      split;[exact Hreserve|]. split.
      * exact (AxiomK.storage_topology built _ (length next) (AxiomRefl.finished_storage built) Htopology).
      * exact Hgrowth.
Qed.

Theorem generated_extensionality s bs ns fs reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (length fs+10+reserve)<=9223372036854775807 -> ns vardef_0__axiom_tag=9 ->
  exists final next index,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (SetTheory.axiom_formula SetTheory.Ext) /\
    SetTheory.derives (SetTheory.axiom_formula SetTheory.Ext) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
    AxiomRefl.logical_frame s final /\ AxiomStorage.logical_frame s final /\
    Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+10)%nat.
Proof. exact (generated_refines AxiomFixedCircuits.extensionality s bs ns fs reserve observations). Qed.
End AxiomFixedRefinement.
