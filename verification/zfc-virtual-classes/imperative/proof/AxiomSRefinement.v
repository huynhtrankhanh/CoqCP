From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash AxiomRefl AxiomCircuits AxiomS AxiomK
  FormulaCircuit FormulaCircuitProperties ArenaFrame FormulaTopology Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomSRefinement.
Import IndexExecution SipHashExecution.
Lemma source_reference s fs id p : NativeRepresentation.canonical_arena s fs ->
  word id -> nth_error fs (Z.to_nat id)=Some p -> id<meta_value s 1.
Proof.
  intros Harena Hword Hlookup. pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
  pose proof (proj1 Hword) as Hnonneg.
  assert (Hlt:(Z.to_nat id<length fs)%nat) by (apply nth_error_Some;congruence).
  apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by exact Hnonneg. lia.
Qed.
Theorem generated_refines s bs ns fs p_id q_id r_id p q r reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=1 -> ns vardef_0__axiom_p=p_id -> ns vardef_0__axiom_q=q_id -> ns vardef_0__axiom_r=r_id ->
  word p_id -> word q_id -> word r_id ->
  nth_error fs (Z.to_nat p_id)=Some p -> nth_error fs (Z.to_nat q_id)=Some q -> nth_error fs (Z.to_nat r_id)=Some r ->
  Z.of_nat (length fs+6+reserve)<=9223372036854775807 ->
  exists built next,
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)) /\
    NativeRepresentation.canonical_arena (AxiomRefl.finished built) next /\
    meta_value (AxiomRefl.finished built) 13=1 /\ meta_value (AxiomRefl.finished built) 8=0 /\
    word (meta_value (AxiomRefl.finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (AxiomRefl.finished built) 0))=Some (SetTheory.axiom_formula (SetTheory.Srule p q r)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.Srule p q r)) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (AxiomRefl.finished built) (length next) /\ (length next<=length fs+6)%nat /\
    AxiomRefl.logical_frame s (AxiomRefl.finished built).
Proof.
  intros Harena Hordered Herror Hmeta Htag Hp Hq Hr Hpword Hqword Hrword Hplookup Hqlookup Hrlookup Hbudget.
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hcleared_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Hordered) as Hcleared_ordered.
  assert (Hcleared_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (AxiomCircuits.construct_s (AxiomRefl.cleared s) fs p_id q_id r_id p q r reserve observations
    Hcleared_arena Hcleared_ordered Hcleared_error Hpword Hqword Hrword Hplookup Hqlookup Hrlookup Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hrep & Hprefix & Hreserve & Htopology & Hgrowth).
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  destruct (AxiomCircuits.s_result observations (AxiomRefl.cleared s) p_id q_id r_id built ids next p q r Htrace Hrep)
    as (Hword & Hmeaning & Hderives).
  destruct (AxiomK.finishing_result built Hbuiltmeta) as (Hsuccess & Hresult_error & Hresult).
  exists built,next. split.
  - eapply AxiomS.generated_helper; try eassumption; eapply source_reference; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (AxiomRefl.finished built) next (AxiomRefl.finished_storage built) Hnext)|].
    split; [exact Hsuccess|]. split; [congruence|]. split; [now rewrite Hresult|].
    split; [now rewrite Hresult|]. split; [exact Hderives|]. split; [exact Hprefix|].
    split; [exact Hreserve|]. split; [eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Htopology]|].
    split; [exact Hgrowth|exact (AxiomRefl.frame s built Hframe)].
Qed.
End AxiomSRefinement.
