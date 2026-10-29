From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash HashTable ObservedLocal InternReserve ClassStorage ClassLookup ClassEqualSets
  RenameMemoClassSetnessRaw RenameMemoClassEqual RenameMemoClassMember RenameMemoCallers RenameMemoLengths
  RenameMemoResourceBounds RenameStorage FormulaCircuit FormulaCircuitProperties Representation ArenaFrame FormulaTopology Intern RenameMemoClassSetness SchemaEvaluationIndexHelpers SchemaEvaluationIndexCircuit SchemaEvaluationIndexBounds SchemaEvaluationIndexBudget.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexSetness.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoClassEqual RenameMemoClassSetness.
Theorem generated_abstract s bs ns fs classes a body reserve bound observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some (VirtualClasses.abstract body) -> ns vardef_0__setness_cls=Z.of_nat a ->
  RenameMemoCallers.predicate_ready s fs a 2 0 ->
  Z.of_nat (length fs+RenameMemoCallers.predicate_growth s a+10+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  SchemaEvaluationIndexBounds.class_bound bound (VirtualClasses.abstract body) -> Z.of_nat bound+2<=maximum ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+2) /\
    execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,observations)) /\
    post s fs classes (Protocol.class_setness (VirtualClasses.abstract body)) reserve (RenameMemoCallers.predicate_growth s a+10) final next index.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hna Hready Hbudget HrawInitial HclassBound HindexRoom.
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Htwo : word 2) by (unfold word,maximum; lia).
  destruct (RenameMemoClassMember.record s fs classes a (VirtualClasses.abstract body) Hclasses Hwellformed Ha ltac:(intros i Hbad; discriminate))
    as (value & Hbound & Hrecord).
  destruct (SchemaEvaluationIndexHelpers.generated_predicate s (fun _=>false) (RenameMemoClassSetnessRaw.predicate_arguments (Z.of_nat a) 2)
    fs classes (VirtualClasses.abstract body) a 2 0 bound observations Hmeta Hsip (arena_positive _ _ Harena) Herror Harena Htopology Hfalse
    Hclasses Hwellformed Ha eq_refl eq_refl eq_refl Htwo Hzero Hready HrawInitial HclassBound ltac:(cbn [Nat.max];exact HindexRoom))
    as (first & fs_a & left & HrawFirst & Hfirst & Harena_a & Hleft & Hleftword & Hmeaning & Hprefix & Hflag & Hgrowth & Hframe & Hclasses_a & Hwellformed_a & Htopology_a).
  assert (Hfalse_a : nth_error fs_a 0=Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hinitial : FormulaCircuit.represents fs_a [0;Z.of_nat left]
    [SetTheory.falsity;VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0]).
  { constructor; [split; assumption|]. constructor; [split; [exact Hleftword|now rewrite Nat2Z.id]|constructor]. }
  assert (Hbudget_a : Z.of_nat (length fs_a+10+reserve)<=9223372036854775807).
  { repeat rewrite Nat2Z.inj_add in *. unfold RenameMemoResourceBounds.doubling_limit in *. lia. }
  destruct (SchemaEvaluationIndexCircuit.complete RenameMemoClassSetnessRaw.plan first fs_a [0;Z.of_nat left]
    [SetTheory.falsity;VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0]
    (RenameMemoClassSetnessRaw.values (VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0)) reserve (bound+2)%nat observations
    Harena_a Htopology_a Hflag Hinitial RenameMemoClassSetnessRaw.fits (RenameMemoClassSetnessRaw.infer _) Hbudget_a HrawFirst
    ltac:(unfold RenameMemoClassSetnessRaw.plan;repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];lia))
    as (built & next & ids & HrawBuilt & Htrace & Hbuiltframe & Harena_next & Hflag_next & Hrep & Hprefix_next & Hremaining & Htopology_next & Hgrowth_next).
  pose proof (RenameMemoClassSetnessRaw.result_semantics observations first (Z.of_nat left) built ids next _ Htrace Hrep) as [Hword Hresult].
  pose proof (proj1 (proj1 Harena_a)) as [Hmeta_a Hrest].
  exists (store_meta built 0 (meta_value built 0)),next,(Z.to_nat (meta_value built 0)). split.
  { eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply store_meta_other;discriminate|exact HrawBuilt]. }
  split.
  - eapply eq_trans; [exact (eliminate_correct funcdef_0__setness_body bs ns s observations)|].
    eapply eq_trans; [exact (unit_projection (execLocalObserved funcdef_0__setness_body ({|machine:=s;bools:=bs;nums:=ns|},observations)) (fun after=>(machine (fst after),snd after)))|].
    exact (RenameMemoClassSetnessRaw.generated_general {|machine:=s;bools:=bs;nums:=ns|} first built ids a 1 value (Z.of_nat left) observations
      Hna Hbound Hrecord ltac:(discriminate) Hfirst ltac:(lia) Hleft Htrace).
  - eapply finish; try eassumption.
    + unfold Protocol.class_setness,RenameMemoClassSetnessRaw.result. rewrite <-RenameMemoClassMember.predicate_double. exact Hresult.
    + eapply InternReserve.extends_trans; eassumption.
    + eapply frame_trans; [exact Hframe|exact (ClassEqualSets.intern_frame _ _ Hbuiltframe)].
    + cbn [RenameMemoClassSetnessRaw.plan length] in Hgrowth_next. lia.
Qed.
Theorem generated_set s bs ns fs classes a variable reserve bound observations :
  (8<length (memory s arraydef_0__meta))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some (VirtualClasses.set variable) -> ns vardef_0__setness_cls=Z.of_nat a ->
  word (Z.of_nat (S variable)) ->
  Z.of_nat (length fs+4+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound -> (variable<=bound)%nat ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+2) /\
    execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,observations)) /\
    post s fs classes (Protocol.class_setness (VirtualClasses.set variable)) reserve 4 final next index.
Proof.
  intros Hmetadata Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hna Hsuccessor Hbudget HrawInitial HvariableBound.
  destruct (ClassEqualSets.set_lookup s fs classes a variable Hclasses Hwellformed Ha) as [Hbound [Hvariable Hrecord]].
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Hinitial : FormulaCircuit.represents fs [0] [SetTheory.falsity]) by
    (constructor; [split; assumption|constructor]).
  destruct (SchemaEvaluationIndexCircuit.complete (RenameMemoClassSetnessRaw.set_plan variable) s fs [0] [SetTheory.falsity]
    (RenameMemoClassSetnessRaw.set_values variable) reserve (bound+2)%nat observations Harena Htopology Herror Hinitial
    (RenameMemoClassSetnessRaw.set_fits variable Hsuccessor) (RenameMemoClassSetnessRaw.set_infer variable) Hbudget
    (SchemaEvaluationIndexBounds.raw_arena_mono s (length fs) bound (bound+2) ltac:(lia) HrawInitial)
    ltac:(unfold RenameMemoClassSetnessRaw.set_plan;repeat constructor;cbn [SchemaEvaluationIndexCircuit.operation_bound];lia))
    as (built & next & ids & HrawBuilt & Htrace & Hbuiltframe & Harena_next & Hflag_next & Hrep & Hprefix & Hremaining & Htopology_next & Hgrowth).
  pose proof (RenameMemoClassSetnessRaw.set_result_semantics observations s built ids next variable Htrace Hrep) as [Hword Hresult].
  pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest].
  exists (store_meta built 0 (meta_value built 0)),next,(Z.to_nat (meta_value built 0)). split.
  { eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply store_meta_other;discriminate|exact HrawBuilt]. }
  split.
  - eapply eq_trans; [exact (eliminate_correct funcdef_0__setness_body bs ns s observations)|].
    eapply eq_trans; [exact (unit_projection (execLocalObserved funcdef_0__setness_body ({|machine:=s;bools:=bs;nums:=ns|},observations)) (fun after=>(machine (fst after),snd after)))|].
    exact (RenameMemoClassSetnessRaw.generated_set {|machine:=s;bools:=bs;nums:=ns|} built ids a variable observations
      Hna Hbound Hrecord Hmetadata Herror Hsuccessor Htrace).
  - eapply finish; try eassumption.
    + exact (ClassEqualSets.intern_frame _ _ Hbuiltframe).
Qed.
Theorem generated_refines s bs ns fs classes a cls reserve bound observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some cls -> ns vardef_0__setness_cls=Z.of_nat a -> ready s fs a cls ->
  Z.of_nat (length fs+work s a cls+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  SchemaEvaluationIndexBounds.class_bound bound cls -> Z.of_nat bound+2<=maximum ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+2) /\
    execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,observations)) /\
    post s fs classes (Protocol.class_setness cls) reserve (work s a cls) final next index.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hna Hready Hbudget HrawInitial HclassBound HindexRoom.
  destruct cls as [variable|body]; cbn [work ready] in Hready,Hbudget |- *.
  - eapply generated_set with (bound:=bound); try eassumption; lia.
  - eapply generated_abstract with (bound:=bound); try eassumption.
    replace (length fs+RenameMemoCallers.predicate_growth s a+10+reserve)%nat with
      (length fs+(RenameMemoCallers.predicate_growth s a+10)+reserve)%nat by lia. exact Hbudget.
Qed.
Theorem uniform_ready native fs classes bound capacity reserve :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 ClassStorage.represents native fs classes -> ClassLookup.wellformed native ->
 nth_error fs 0=Some SetTheory.falsity ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> SchemaEvaluationIndexBounds.classes bound classes ->
 (length fs<=capacity)%nat -> Z.of_nat (5*(capacity*capacity)+1)<=maximum -> Z.of_nat bound+2<=maximum ->
 Z.of_nat (capacity+capacity*capacity+10+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 forall index cls,nth_error classes index=Some cls ->
 RenameMemoClassSetness.ready native fs index cls /\
 Z.of_nat (length fs+RenameMemoClassSetness.work native index cls+reserve)<=RenameMemoResourceBounds.doubling_limit.
Proof.
 intros Harena Htop Hclasses Hgood Hfalse Hraw Hbounds Hcapacity Hfuel Hindices Hroom index cls Hlookup.
 assert (Hpositive:(0<length fs)%nat) by (apply nth_error_Some;congruence).
 pose proof (SchemaEvaluationIndexBudget.classes_lookup bound classes index cls Hbounds Hlookup) as HclassBound.
 pose proof (SchemaEvaluationIndexBudget.growth_bound native fs classes index cls capacity Hclasses Hgood Hlookup Hpositive Hcapacity) as Hgrowth.
 assert (HpredicateRoom:Z.of_nat (length fs+capacity*capacity)<=RenameMemoResourceBounds.doubling_limit).
 { repeat rewrite Nat2Z.inj_add in *. lia. }
 split.
 - destruct cls as [variable|body];cbn [RenameMemoClassSetness.ready].
   + cbn [SchemaEvaluationIndexBounds.class_bound] in HclassBound. unfold word. rewrite Nat2Z.inj_succ. lia.
   + eapply SchemaEvaluationIndexBudget.predicate_ready;try eassumption;lia.
 - destruct cls;cbn [RenameMemoClassSetness.work];repeat rewrite Nat2Z.inj_add in *;lia.
Qed.
End SchemaEvaluationIndexSetness.
