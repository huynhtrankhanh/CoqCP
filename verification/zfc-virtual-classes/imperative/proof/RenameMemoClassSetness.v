From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash HashTable ObservedLocal InternReserve ClassStorage ClassLookup ClassEqualSets
  RenameMemoClassSetnessRaw RenameMemoClassEqual RenameMemoClassMember RenameMemoCallers RenameMemoLengths
  RenameMemoResourceBounds RenameStorage FormulaCircuit FormulaCircuitProperties Representation ArenaFrame FormulaTopology Intern.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoClassSetness.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoClassEqual.
Definition post s fs classes result reserve work final next index :=
  NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
  nth_error next index=Some result /\ (exists extra,next=fs++extra) /\ meta_value final 8=0 /\
  RenameStorage.logical_frame s final /\ ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
  Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next) /\
  (length next<=length fs+work)%nat.
Lemma finish s built fs next classes result reserve work :
  NativeRepresentation.canonical_arena built next -> meta_value built 8=0 ->
  word (meta_value built 0) -> nth_error next (Z.to_nat (meta_value built 0))=Some result ->
  (exists extra,next=fs++extra) -> RenameStorage.logical_frame s built ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit -> FormulaTopology.ordered built (length next) ->
  (length next<=length fs+work)%nat ->
  post s fs classes result reserve work (store_meta built 0 (meta_value built 0)) next (Z.to_nat (meta_value built 0)).
Proof.
  intros Harena Herror Hword Hmeaning Hprefix Hframe Hclasses Hwellformed Hreserve Htopology Hgrowth.
  pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest].
  assert (Hfinalframe : RenameStorage.logical_frame s (store_meta built 0 (meta_value built 0))) by
    (eapply frame_trans; [exact Hframe|apply result_frame]).
  unfold post. split; [apply (ArenaFrame.storage_arena built); [apply ArenaFrame.storage_meta; lia|exact Harena]|].
  split; [rewrite meta_store_same by lia; now rewrite Z2Nat.id by exact (proj1 Hword)|].
  split; [now rewrite Z2Nat.id by exact (proj1 Hword)|]. split; [exact Hmeaning|].
  split; [exact Hprefix|]. split; [now rewrite meta_store_other by discriminate|]. split; [exact Hfinalframe|]. split.
  - destruct Hprefix as [extra ->]. exact (RenameStorage.classes_transport _ _ _ _ _ Hfinalframe Hclasses).
  - split; [now apply (ClassLookup.frame_wellformed s)|]. split; [exact Hreserve|]. split; [|exact Hgrowth].
    intros parent child Hparent Hchild. apply Htopology; [exact Hparent|].
    unfold HashTableInvariant.tuple_at in Hchild. now rewrite store_meta_other in Hchild by discriminate.
Qed.
Theorem generated_abstract s bs ns fs classes a body reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some (VirtualClasses.abstract body) -> ns vardef_0__setness_cls=Z.of_nat a ->
  RenameMemoCallers.predicate_ready s fs a 2 0 ->
  Z.of_nat (length fs+RenameMemoCallers.predicate_growth s a+10+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,observations)) /\
    post s fs classes (Protocol.class_setness (VirtualClasses.abstract body)) reserve (RenameMemoCallers.predicate_growth s a+10) final next index.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hna Hready Hbudget.
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Htwo : word 2) by (unfold word,maximum; lia).
  destruct (RenameMemoClassMember.record s fs classes a (VirtualClasses.abstract body) Hclasses Hwellformed Ha ltac:(intros i Hbad; discriminate))
    as (value & Hbound & Hrecord).
  destruct (RenameMemoCallers.generated_predicate s (fun _=>false) (RenameMemoClassSetnessRaw.predicate_arguments (Z.of_nat a) 2)
    fs classes (VirtualClasses.abstract body) a 2 0 observations Hmeta Hsip (arena_positive _ _ Harena) Herror Harena Htopology Hfalse
    Hclasses Hwellformed Ha eq_refl eq_refl eq_refl Htwo Hzero Hready)
    as (first & fs_a & left & Hfirst & Harena_a & Hleft & Hleftword & Hmeaning & Hprefix & Hflag & Hgrowth & Hframe & Hclasses_a & Hwellformed_a & Htopology_a).
  assert (Hfalse_a : nth_error fs_a 0=Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hinitial : FormulaCircuit.represents fs_a [0;Z.of_nat left]
    [SetTheory.falsity;VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0]).
  { constructor; [split; assumption|]. constructor; [split; [exact Hleftword|now rewrite Nat2Z.id]|constructor]. }
  assert (Hbudget_a : Z.of_nat (length fs_a+10+reserve)<=9223372036854775807).
  { repeat rewrite Nat2Z.inj_add in *. unfold RenameMemoResourceBounds.doubling_limit in *. lia. }
  destruct (FormulaCircuitProperties.complete RenameMemoClassSetnessRaw.plan first fs_a [0;Z.of_nat left]
    [SetTheory.falsity;VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0]
    (RenameMemoClassSetnessRaw.values (VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0)) reserve observations
    Harena_a Htopology_a Hflag Hinitial RenameMemoClassSetnessRaw.fits (RenameMemoClassSetnessRaw.infer _) Hbudget_a)
    as (built & next & ids & Htrace & Hbuiltframe & Harena_next & Hflag_next & Hrep & Hprefix_next & Hremaining & Htopology_next & Hgrowth_next).
  pose proof (RenameMemoClassSetnessRaw.result_semantics observations first (Z.of_nat left) built ids next _ Htrace Hrep) as [Hword Hresult].
  pose proof (proj1 (proj1 Harena_a)) as [Hmeta_a Hrest].
  exists (store_meta built 0 (meta_value built 0)),next,(Z.to_nat (meta_value built 0)). split.
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
Theorem generated_set s bs ns fs classes a variable reserve observations :
  (8<length (memory s arraydef_0__meta))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some (VirtualClasses.set variable) -> ns vardef_0__setness_cls=Z.of_nat a ->
  word (Z.of_nat (S variable)) ->
  Z.of_nat (length fs+4+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,observations)) /\
    post s fs classes (Protocol.class_setness (VirtualClasses.set variable)) reserve 4 final next index.
Proof.
  intros Hmetadata Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hna Hsuccessor Hbudget.
  destruct (ClassEqualSets.set_lookup s fs classes a variable Hclasses Hwellformed Ha) as [Hbound [Hvariable Hrecord]].
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Hinitial : FormulaCircuit.represents fs [0] [SetTheory.falsity]) by
    (constructor; [split; assumption|constructor]).
  destruct (FormulaCircuitProperties.complete (RenameMemoClassSetnessRaw.set_plan variable) s fs [0] [SetTheory.falsity]
    (RenameMemoClassSetnessRaw.set_values variable) reserve observations Harena Htopology Herror Hinitial
    (RenameMemoClassSetnessRaw.set_fits variable Hsuccessor) (RenameMemoClassSetnessRaw.set_infer variable) Hbudget)
    as (built & next & ids & Htrace & Hbuiltframe & Harena_next & Hflag_next & Hrep & Hprefix & Hremaining & Htopology_next & Hgrowth).
  pose proof (RenameMemoClassSetnessRaw.set_result_semantics observations s built ids next variable Htrace Hrep) as [Hword Hresult].
  pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest].
  exists (store_meta built 0 (meta_value built 0)),next,(Z.to_nat (meta_value built 0)). split.
  - eapply eq_trans; [exact (eliminate_correct funcdef_0__setness_body bs ns s observations)|].
    eapply eq_trans; [exact (unit_projection (execLocalObserved funcdef_0__setness_body ({|machine:=s;bools:=bs;nums:=ns|},observations)) (fun after=>(machine (fst after),snd after)))|].
    exact (RenameMemoClassSetnessRaw.generated_set {|machine:=s;bools:=bs;nums:=ns|} built ids a variable observations
      Hna Hbound Hrecord Hmetadata Herror Hsuccessor Htrace).
  - eapply finish; try eassumption.
    + exact (ClassEqualSets.intern_frame _ _ Hbuiltframe).
Qed.
Definition work s index cls := match cls with
  | VirtualClasses.set _ => 4%nat
  | VirtualClasses.abstract _ => (RenameMemoCallers.predicate_growth s index+10)%nat end.
Definition ready s fs index cls := match cls with
  | VirtualClasses.set variable => word (Z.of_nat (S variable))
  | VirtualClasses.abstract _ => RenameMemoCallers.predicate_ready s fs index 2 0 end.
Theorem generated_refines s bs ns fs classes a cls reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some cls -> ns vardef_0__setness_cls=Z.of_nat a -> ready s fs a cls ->
  Z.of_nat (length fs+work s a cls+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,observations)) /\
    post s fs classes (Protocol.class_setness cls) reserve (work s a cls) final next index.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hna Hready Hbudget.
  destruct cls as [variable|body]; cbn [work ready] in Hready,Hbudget |- *.
  - eapply generated_set; try eassumption; lia.
  - eapply generated_abstract; try eassumption.
    replace (length fs+RenameMemoCallers.predicate_growth s a+10+reserve)%nat with
      (length fs+(RenameMemoCallers.predicate_growth s a+10)+reserve)%nat by lia. exact Hbudget.
Qed.
End RenameMemoClassSetness.
