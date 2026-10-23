From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash AxiomRefl AxiomCircuits AxiomEqualityCircuits AxiomEqualityRaw AxiomK
  FormulaCircuit FormulaCircuitProperties ArenaFrame FormulaTopology Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomEqualityRefinement.
Import IndexExecution SipHashExecution.
Theorem generated_refines which s bs ns fs i j k reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=AxiomEqualityCircuits.selector which ->
  ns vardef_0__axiom_p=Z.of_nat i -> ns vardef_0__axiom_q=Z.of_nat j -> ns vardef_0__axiom_r=Z.of_nat k ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat k) ->
  Z.of_nat (length fs+5+reserve)<=9223372036854775807 ->
  exists built next,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)) /\
    NativeRepresentation.canonical_arena (AxiomRefl.finished built) next /\
    meta_value (AxiomRefl.finished built) 13=1 /\ meta_value (AxiomRefl.finished built) 8=0 /\
    word (meta_value (AxiomRefl.finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (AxiomRefl.finished built) 0))=Some (SetTheory.axiom_formula (AxiomEqualityCircuits.witness which i j k)) /\
    SetTheory.derives (SetTheory.axiom_formula (AxiomEqualityCircuits.witness which i j k)) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (AxiomRefl.finished built) (length next) /\ (length next<=length fs+5)%nat /\
    AxiomRefl.logical_frame s (AxiomRefl.finished built).
Proof.
  intros Harena Hordered Herror Hmeta Htag Hp Hq Hr Hpword Hqword Hrword Hbudget.
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hcleared_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Hordered) as Hcleared_ordered.
  assert (Hcleared_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (AxiomEqualityCircuits.construct which i j k (AxiomRefl.cleared s) fs reserve observations
    Hcleared_arena Hcleared_ordered Hcleared_error Hpword Hqword Hrword Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hrep & Hprefix & Hreserve & Htopology & Hgrowth).
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  destruct (AxiomEqualityCircuits.result observations which i j k (AxiomRefl.cleared s) built ids next Htrace Hrep)
    as (Hword & Hmeaning & Hderives).
  destruct (AxiomK.finishing_result built Hbuiltmeta) as (Hsuccess & Hresult_error & Hresult).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hresult.
  exists built,next. split.
  - eapply AxiomEqualityRaw.generated_helper; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (AxiomRefl.finished built) next (AxiomRefl.finished_storage built) Hnext)|].
    split; [exact Hsuccess|]. split; [unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hflag|]. split; [now rewrite Hresult|].
    split; [now rewrite Hresult|]. split; [exact Hderives|]. split; [exact Hprefix|].
    split; [exact Hreserve|]. split; [eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Htopology]|].
    split; [destruct which; exact Hgrowth|exact (AxiomRefl.frame s built Hframe)].
Qed.
End AxiomEqualityRefinement.
