From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Intern InternLengths FormulaEncoding FormulaTopology Representation FormulaCircuit FormulaCircuitProperties AxiomCircuits RenameMemoControl AxiomRefl HashTable AxiomS AxiomK AxiomDNE AxiomEqualityCircuits AxiomEqualityRaw AxiomFixedCircuits NativeAxiomBuilder AxiomDispatch AxiomStorage AxiomSRefinement AxiomDNERefinement AxiomEqualityRefinement AxiomFixedRefinement SchemaEvaluationIndexBounds SchemaEvaluationIndexCircuit SchemaEvaluationIndexCircuitTrace.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexAxiomCircuits.
Import IndexExecution SipHashExecution ObservedLocal.
Lemma storage_raw s t count bound : ArenaFrame.storage s t ->
 SchemaEvaluationIndexBounds.raw_arena s count bound -> SchemaEvaluationIndexBounds.raw_arena t count bound.
Proof. intros [_ [Harrays _]] Hraw. eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply Harrays;discriminate|exact Hraw]. Qed.
Module K.
Import AxiomK.
Theorem generated_refines s bs ns fs p_id q_id p q reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=0 -> ns vardef_0__axiom_p=p_id -> ns vardef_0__axiom_q=q_id ->
  word p_id -> word q_id -> nth_error fs (Z.to_nat p_id)=Some p -> nth_error fs (Z.to_nat q_id)=Some q ->
  Z.of_nat (length fs+2+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists built next, SchemaEvaluationIndexBounds.raw_arena (AxiomRefl.finished built) (length next) bound /\
    execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(finished built,observations)) /\
    NativeRepresentation.canonical_arena (finished built) next /\
    meta_value (finished built) 13=1 /\ meta_value (finished built) 8=0 /\
    word (meta_value (finished built) 0) /\
    nth_error next (Z.to_nat (meta_value (finished built) 0))=Some (SetTheory.axiom_formula (SetTheory.K p q)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.K p q)) /\
    (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered (finished built) (length next) /\ (length next<=length fs+2)%nat /\
    AxiomRefl.logical_frame s (finished built).
Proof.
  intros Harena Hordered Herror Hmeta Htag Hp Hq Hpword Hqword Hplookup Hqlookup Hbudget HrawInitial.
  pose proof (clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (cleared s) fs Hclear Harena) as Hcleared_arena.
  pose proof (storage_topology s (cleared s) (length fs) Hclear Hordered) as Hcleared_ordered.
  assert (Hcleared_error:meta_value (cleared s) 8=0) by (unfold cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (AxiomCircuits.construct_k (cleared s) fs p_id q_id p q reserve observations
    Hcleared_arena Hcleared_ordered Hcleared_error Hpword Hqword Hplookup Hqlookup Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hrep & Hprefix & Hreserve & Htopology & Hgrowth).
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) bound).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hcleared_arena|exact Hcleared_error| | | |exact Hnext].
    - exact (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - cbn [AxiomCircuits.k_plan length] in *;repeat rewrite Nat2Z.inj_add in Hbudget;lia.
    - repeat constructor. }
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold cleared;rewrite store_meta_length;exact Hmeta).
  destruct (AxiomCircuits.k_result observations (cleared s) p_id q_id built ids next p q Htrace Hrep)
    as (Hword & Hmeaning & Hderives).
  destruct (finishing_result built Hbuiltmeta) as (Hsuccess & Hresult_error & Hresult).
  assert (Hpbound:p_id<meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    pose proof (proj1 Hpword) as Hpnonneg.
    assert (Hlt:(Z.to_nat p_id<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by exact Hpnonneg. lia. }
  assert (Hqbound:q_id<meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    pose proof (proj1 Hqword) as Hqnonneg.
    assert (Hlt:(Z.to_nat q_id<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hlt. rewrite Z2Nat.id in Hlt by exact Hqnonneg. lia. }
  exists built,next. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) bound (AxiomRefl.finished_storage built) HrawBuilt)|]. split; [eapply generated_helper;eassumption|].
  split; [exact (ArenaFrame.storage_arena built (finished built) next (finishing_storage built) Hnext)|].
  split; [exact Hsuccess|]. split; [congruence|]. split; [now rewrite Hresult|].
  split; [now rewrite Hresult|]. split; [exact Hderives|]. split; [exact Hprefix|].
  split; [exact Hreserve|]. split; [eapply storage_topology;[apply finishing_storage|exact Htopology]|].
  split; [exact Hgrowth|exact (AxiomRefl.frame s built Hframe)].
Qed.
End K.
Module SRule.
Import AxiomSRefinement.
Theorem generated_refines s bs ns fs p_id q_id r_id p q r reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=1 -> ns vardef_0__axiom_p=p_id -> ns vardef_0__axiom_q=q_id -> ns vardef_0__axiom_r=r_id ->
  word p_id -> word q_id -> word r_id ->
  nth_error fs (Z.to_nat p_id)=Some p -> nth_error fs (Z.to_nat q_id)=Some q -> nth_error fs (Z.to_nat r_id)=Some r ->
  Z.of_nat (length fs+6+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists built next, SchemaEvaluationIndexBounds.raw_arena (AxiomRefl.finished built) (length next) bound /\
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
  intros Harena Hordered Herror Hmeta Htag Hp Hq Hr Hpword Hqword Hrword Hplookup Hqlookup Hrlookup Hbudget HrawInitial.
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hcleared_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Hordered) as Hcleared_ordered.
  assert (Hcleared_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (AxiomCircuits.construct_s (AxiomRefl.cleared s) fs p_id q_id r_id p q r reserve observations
    Hcleared_arena Hcleared_ordered Hcleared_error Hpword Hqword Hrword Hplookup Hqlookup Hrlookup Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hrep & Hprefix & Hreserve & Htopology & Hgrowth).
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) bound).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hcleared_arena|exact Hcleared_error| | | |exact Hnext].
    - exact (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - cbn [AxiomCircuits.s_plan length] in *;repeat rewrite Nat2Z.inj_add in Hbudget;lia.
    - repeat constructor. }
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  destruct (AxiomCircuits.s_result observations (AxiomRefl.cleared s) p_id q_id r_id built ids next p q r Htrace Hrep)
    as (Hword & Hmeaning & Hderives).
  destruct (AxiomK.finishing_result built Hbuiltmeta) as (Hsuccess & Hresult_error & Hresult).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hresult.
  exists built,next. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) bound (AxiomRefl.finished_storage built) HrawBuilt)|]. split.
  - eapply AxiomS.generated_helper; try eassumption; eapply source_reference; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (AxiomRefl.finished built) next (AxiomRefl.finished_storage built) Hnext)|].
    split; [exact Hsuccess|]. split; [unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hflag|]. split; [now rewrite Hresult|].
    split; [now rewrite Hresult|]. split; [exact Hderives|]. split; [exact Hprefix|].
    split; [exact Hreserve|]. split; [eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Htopology]|].
    split; [exact Hgrowth|exact (AxiomRefl.frame s built Hframe)].
Qed.
End SRule.
Module DNE.
Import AxiomDNERefinement AxiomDNE.
Theorem generated_refines s bs ns fs p_id p reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13 < length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  word p_id -> nth_error fs (Z.to_nat p_id)=Some p ->
  Z.of_nat (length fs+3+reserve)<=9223372036854775807 ->
  ns vardef_0__axiom_tag=2 -> ns vardef_0__axiom_p=p_id ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) bound /\ execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (SetTheory.axiom_formula (SetTheory.DNE p)) /\
    SetTheory.derives (SetTheory.axiom_formula (SetTheory.DNE p)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
    AxiomRefl.logical_frame s final /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+3)%nat.
Proof.
  intros Harena Hordered Herror Hmeta Hfalse Hpword Hp Hbudget Htag Hpinput HrawInitial.
  assert (Hstorage : ArenaFrame.storage s (cleared s)).
  { unfold cleared. apply ArenaFrame.storage_meta; lia. }
  assert (Hclear : NativeRepresentation.canonical_arena (cleared s) fs).
  { exact (ArenaFrame.storage_arena s (cleared s) fs Hstorage Harena). }
  assert (Hclearerror : meta_value (cleared s) 8=0).
  { unfold cleared. rewrite meta_store_other by discriminate. exact Herror. }
  assert (Hclearordered : FormulaTopology.ordered (cleared s) (length fs)).
  { exact (storage_topology s (cleared s) (length fs) Hstorage Hordered). }
  destruct (AxiomCircuits.construct_dne (cleared s) fs p_id p reserve observations Hclear Hclearordered Hclearerror Hfalse Hpword Hp Hbudget)
    as [built [next [ids [Htrace [Hframe [Hnext [Hflag [Hrep [Hprefix [Hreserve [Htopology Hgrowth]]]]]]]]]]].
  destruct (AxiomCircuits.dne_result observations (cleared s) p_id built ids next p Htrace Hrep) as [Hresultword [Hmeaning Hderives]].
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) bound).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hclear|exact Hclearerror| | | |exact Hnext].
    - exact (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - cbn [AxiomCircuits.dne_plan length] in *;repeat rewrite Nat2Z.inj_add in Hbudget;lia.
    - repeat constructor. }
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuilt : (13<length (memory built arraydef_0__meta))%nat).
  { rewrite Hlength. unfold cleared. now rewrite store_meta_length. }
  assert (Hpbound : p_id<meta_value s 1).
  { pose proof (proj1 (proj2 (proj1 Harena))) as Hcount.
    assert (Hbound : (Z.to_nat p_id<length fs)%nat) by (apply nth_error_Some;congruence).
    apply Nat2Z.inj_lt in Hbound. unfold word in Hpword. rewrite Z2Nat.id in Hbound by lia. lia. }
  assert (Hresult : meta_value (finished built) 0=meta_value built 0).
  { unfold finished. rewrite meta_store_other by discriminate. now rewrite meta_store_same by lia. }
  exists (finished built),next,(Z.to_nat (meta_value built 0)). split;[exact (storage_raw built (finished built) (length next) bound (AxiomRefl.finished_storage built) HrawBuilt)|]. split.
  - eapply generated_helper; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (finished built) next (AxiomRefl.finished_storage built) Hnext)|].
    split.
    + rewrite Hresult,Z2Nat.id;[reflexivity|unfold word in Hresultword;lia].
    + split.
      * rewrite Z2Nat.id;[exact Hresultword|unfold word in Hresultword;lia].
      * split;[exact Hmeaning|]. split;[exact Hderives|]. split;[exact Hprefix|]. split.
        -- unfold finished. rewrite !meta_store_other by discriminate. exact Hflag.
        -- split.
           ++ unfold finished. rewrite meta_store_same;[reflexivity|rewrite store_meta_length;exact Hbuilt].
           ++ split;[exact (AxiomRefl.frame s built Hframe)|]. split;[exact Hreserve|]. split.
              ** exact (storage_topology built (finished built) (length next) (AxiomRefl.finished_storage built) Htopology).
              ** exact Hgrowth.
Qed.
End DNE.
Module Equality.
Import AxiomEqualityRefinement.
Theorem generated_refines which s bs ns fs i j k reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=AxiomEqualityCircuits.selector which ->
  ns vardef_0__axiom_p=Z.of_nat i -> ns vardef_0__axiom_q=Z.of_nat j -> ns vardef_0__axiom_r=Z.of_nat k ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat k) ->
  Z.of_nat (length fs+5+reserve)<=9223372036854775807 ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  Forall (SchemaEvaluationIndexCircuit.operation_bound bound) (AxiomEqualityCircuits.plan which i j k) ->
  exists built next, SchemaEvaluationIndexBounds.raw_arena (AxiomRefl.finished built) (length next) bound /\
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
  intros Harena Hordered Herror Hmeta Htag Hp Hq Hr Hpword Hqword Hrword Hbudget HrawInitial Hops.
  pose proof (AxiomK.clearing_storage s) as Hclear.
  pose proof (ArenaFrame.storage_arena s (AxiomRefl.cleared s) fs Hclear Harena) as Hcleared_arena.
  pose proof (AxiomK.storage_topology s (AxiomRefl.cleared s) (length fs) Hclear Hordered) as Hcleared_ordered.
  assert (Hcleared_error:meta_value (AxiomRefl.cleared s) 8=0)
    by (unfold AxiomRefl.cleared;rewrite meta_store_other by lia;exact Herror).
  destruct (AxiomEqualityCircuits.construct which i j k (AxiomRefl.cleared s) fs reserve observations
    Hcleared_arena Hcleared_ordered Hcleared_error Hpword Hqword Hrword Hbudget)
    as (built & next & ids & Htrace & Hframe & Hnext & Hflag & Hrep & Hprefix & Hreserve & Htopology & Hgrowth).
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) bound).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hcleared_arena|exact Hcleared_error| | | |exact Hnext].
    - exact (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - cbn [AxiomEqualityCircuits.plan length] in *;repeat rewrite Nat2Z.inj_add in Hbudget;lia.
    - exact Hops. }
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hlength;unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  destruct (AxiomEqualityCircuits.result observations which i j k (AxiomRefl.cleared s) built ids next Htrace Hrep)
    as (Hword & Hmeaning & Hderives).
  destruct (AxiomK.finishing_result built Hbuiltmeta) as (Hsuccess & Hresult_error & Hresult).
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hresult.
  exists built,next. split;[exact (storage_raw built (AxiomRefl.finished built) (length next) bound (AxiomRefl.finished_storage built) HrawBuilt)|]. split.
  - eapply AxiomEqualityRaw.generated_helper; eassumption.
  - split; [exact (ArenaFrame.storage_arena built (AxiomRefl.finished built) next (AxiomRefl.finished_storage built) Hnext)|].
    split; [exact Hsuccess|]. split; [unfold AxiomRefl.finished;rewrite !meta_store_other by lia;exact Hflag|]. split; [now rewrite Hresult|].
    split; [now rewrite Hresult|]. split; [exact Hderives|]. split; [exact Hprefix|].
    split; [exact Hreserve|]. split; [eapply AxiomK.storage_topology;[apply AxiomRefl.finished_storage|exact Htopology]|].
    split; [destruct which; exact Hgrowth|exact (AxiomRefl.frame s built Hframe)].
Qed.
End Equality.
Module Fixed.
Import AxiomFixedRefinement.
Theorem generated_refines which s bs ns fs reserve bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  (13<length (memory s arraydef_0__meta))%nat -> nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (length fs+length (AxiomFixedCircuits.plan which)+reserve)<=9223372036854775807 ->
  ns vardef_0__axiom_tag=AxiomFixedCircuits.selector which ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  Forall (SchemaEvaluationIndexCircuit.operation_bound bound) (AxiomFixedCircuits.plan which) ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) bound /\
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
  intros Harena Hordered Herror Hmeta Hfalse Hbudget Htag HrawInitial Hops.
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
  assert (HrawBuilt:SchemaEvaluationIndexBounds.raw_arena built (length next) bound).
  { eapply SchemaEvaluationIndexCircuitTrace.trace_arena;[exact Htrace|exact Hclear|exact Hclearerror| | | |exact Hnext].
    - exact (storage_raw s (AxiomRefl.cleared s) (length fs) bound (AxiomK.clearing_storage s) HrawInitial).
    - repeat rewrite Nat2Z.inj_add in Hbudget;lia.
    - exact Hops. }
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hlength.
  assert (Hbuilt : (13<length (memory built arraydef_0__meta))%nat).
  { rewrite Hlength. unfold AxiomRefl.cleared. now rewrite store_meta_length. }
  destruct (AxiomK.finishing_result built Hbuilt) as [Hsuccess [Herrorfinal Hresult]].
  change (meta_value (AxiomRefl.finished built) 13=1) in Hsuccess.
  change (meta_value (AxiomRefl.finished built) 8=meta_value built 8) in Herrorfinal.
  change (meta_value (AxiomRefl.finished built) 0=meta_value built 0) in Hresult.
  pose proof (generated_helper which s bs ns built ids observations Hmeta Htag Htrace) as Hrun.
  exists (AxiomRefl.finished built),next,(Z.to_nat (meta_value built 0)). split;[exact (storage_raw built (AxiomRefl.finished built) (length next) bound (AxiomRefl.finished_storage built) HrawBuilt)|]. split;[exact Hrun|].
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
End Fixed.
End SchemaEvaluationIndexAxiomCircuits.
