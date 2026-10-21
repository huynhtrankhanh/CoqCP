From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash ObservedLocal InternReserve ClassStorage ClassLookup ClassPredicate ClassEqualSets ClassEqualCircuit PredicateRefinement RenameInvariant RenameStorage FormulaCircuit FormulaEncoding Representation ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassEqualRefinement.
Import IndexExecution SipHashExecution ObservedLocal.
Lemma unit_projection {A B} (result : option (unit * A)) (project : A -> B) :
  optionBind result (fun r=>Some (fst r,project (snd r))) = optionBind result (fun r=>Some (tt,project (snd r))).
Proof. destruct result as [[[] after]|]; reflexivity. Qed.
Definition nonsets a b := ~ exists i j, a = VirtualClasses.set i /\ b = VirtualClasses.set j.
Lemma frame_trans s t u : RenameStorage.logical_frame s t -> RenameStorage.logical_frame t u -> RenameStorage.logical_frame s u.
Proof.
  intros [Ha [Hc [Hi Ho]]] [Ha' [Hc' [Hi' Ho']]]. split; [intros; now rewrite Ha',Ha by assumption|].
  split; [intros; now rewrite Hc',Hc by assumption|]. split; congruence.
Qed.
Lemma result_frame s : RenameStorage.logical_frame s (store_meta s 0 (meta_value s 0)).
Proof.
  split.
  - intros name [Hm Hrest]. now apply store_meta_other.
  - split; [intros cell Hcell; apply meta_store_other; unfold RenameStorage.Cells.protected in Hcell; tauto|]. split; reflexivity.
Qed.
Lemma predicate_successor cls : VirtualClasses.predicate cls (fun n=>(n+1)%nat) 0 = VirtualClasses.predicate cls S 0.
Proof.
  destruct cls as [i|body]; cbn [VirtualClasses.predicate]; [now rewrite Nat.add_1_r|].
  apply PredicateRefinement.rename_extensional. intros [|i]; cbn [VirtualClasses.cons]; [reflexivity|now rewrite Nat.add_1_r].
Qed.
Lemma equality_formula a b : nonsets a b -> VirtualClasses.erase (VirtualClasses.class_equal a b) =
  SetTheory.all (SetTheory.iff (VirtualClasses.predicate a S 0) (VirtualClasses.predicate b S 0)).
Proof. destruct a,b; try reflexivity. intros Hnonsets. exfalso. apply Hnonsets. repeat eexists; reflexivity. Qed.
Lemma records s fs classes a b cls_a cls_b : ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some cls_a -> nth_error classes b = Some cls_b -> nonsets cls_a cls_b ->
  exists tag_a value_a tag_b value_b,
    (a < length (memory s arraydef_0__classes))%nat /\ (b < length (memory s arraydef_0__classes))%nat /\
    nth_error (memory s arraydef_0__classes) a = Some (tag_a,value_a) /\
    nth_error (memory s arraydef_0__classes) b = Some (tag_b,value_b) /\ (tag_a<>0 \/ tag_b<>0).
Proof.
  intros Hclasses Hwellformed Ha Hb Hnonsets.
  destruct (ClassLookup.lookup s fs classes a cls_a Hclasses Hwellformed Ha) as [Habound Hraw_a].
  destruct (ClassLookup.lookup s fs classes b cls_b Hclasses Hwellformed Hb) as [Hbbound Hraw_b].
  destruct Hraw_a as [[i [-> [Hi Hrecord_a]]]|[root_a [p [-> [Hp Hrecord_a]]]]];
    destruct Hraw_b as [[j [-> [Hj Hrecord_b]]]|[root_b [q [-> [Hq Hrecord_b]]]]].
  - exfalso. apply Hnonsets. repeat eexists; reflexivity.
  - exists 0,(Z.of_nat i),1,(Z.of_nat root_b). repeat split; try assumption; auto; discriminate.
  - exists 1,(Z.of_nat root_a),0,(Z.of_nat j). repeat split; try assumption; auto; discriminate.
  - exists 1,(Z.of_nat root_a),1,(Z.of_nat root_b). repeat split; try assumption; auto; discriminate.
Qed.
Theorem generated_general s bs ns fs classes a b cls_a cls_b reserve observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some cls_a -> nth_error classes b = Some cls_b -> nonsets cls_a cls_b ->
  ns vardef_0__classEqual_a = Z.of_nat a -> ns vardef_0__classEqual_b = Z.of_nat b ->
  ClassPredicate.fits cls_a 1 0 -> ClassPredicate.fits cls_b 1 0 ->
  Z.of_nat (length fs + ClassPredicate.work cls_a + ClassPredicate.work cls_b + 6 + reserve) <= RenameInvariant.resource_limit ->
  exists final next index, execObserved (funcdef_0__classEqual bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.erase (VirtualClasses.class_equal cls_a cls_b)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8 = 0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
    Z.of_nat (length next + reserve) <= RenameInvariant.resource_limit.
Proof.
  intros Harena Hfalse Herror Hclasses Hwellformed Ha Hb Hnonsets Hna Hnb Hfits_a Hfits_b Hbudget.
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Hone : word 1) by (unfold word,maximum; lia).
  destruct (records s fs classes a b cls_a cls_b Hclasses Hwellformed Ha Hb Hnonsets)
    as [tag_a [value_a [tag_b [value_b [Habound [Hbbound [Hrecord_a [Hrecord_b Hnotzero]]]]]]]].
  assert (Hbudget_a : Z.of_nat (length fs + ClassPredicate.work cls_a) <= RenameInvariant.resource_limit).
  { repeat rewrite Nat2Z.inj_add in *. lia. }
  destruct (ClassPredicate.generated_refines s (fun _=>false) (ClassEqualCircuit.predicate_arguments (Z.of_nat a)) fs classes cls_a a 1 0 observations
    Harena Hfalse Herror Hclasses Hwellformed Ha eq_refl eq_refl eq_refl Hfits_a Hone Hzero Hbudget_a)
    as [first [fs_a [left [Hfirst [Harena_a [Hleft [Hleftword [Hmeaning_a [Hprefix_a [Hflag_a [Hgrowth_a [Hframe_a [Hclasses_a Hwellformed_a]]]]]]]]]]]]].
  assert (Hfalse_a : nth_error fs_a 0 = Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hbudget_b : Z.of_nat (length fs_a + ClassPredicate.work cls_b) <= RenameInvariant.resource_limit).
  { apply Nat2Z.inj_le in Hgrowth_a. repeat rewrite Nat2Z.inj_add in *. lia. }
  destruct (ClassPredicate.generated_refines first (fun _=>false) (ClassEqualCircuit.predicate_arguments (Z.of_nat b)) fs_a classes cls_b b 1 0 observations
    Harena_a Hfalse_a Hflag_a Hclasses_a Hwellformed_a Hb eq_refl eq_refl eq_refl Hfits_b Hone Hzero Hbudget_b)
    as [second [fs_b [right [Hsecond [Harena_b [Hright [Hrightword [Hmeaning_b [Hprefix_b [Hflag_b [Hgrowth_b [Hframe_b [Hclasses_b Hwellformed_b]]]]]]]]]]]]].
  assert (Hfalse_b : nth_error fs_b 0 = Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hmeaning_left : nth_error fs_b (Z.to_nat (Z.of_nat left)) = Some (VirtualClasses.predicate cls_a (fun n=>(n+1)%nat) 0)).
  { rewrite Nat2Z.id. eapply InternReserve.lookup_preserved; eassumption. }
  assert (Hmeaning_right : nth_error fs_b (Z.to_nat (Z.of_nat right)) = Some (VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0)) by now rewrite Nat2Z.id.
  assert (Hcircuit_budget : Z.of_nat (length fs_b + 6 + reserve) <= 9223372036854775807).
  { apply Nat2Z.inj_le in Hgrowth_b. repeat rewrite Nat2Z.inj_add in *. unfold RenameInvariant.resource_limit in *. lia. }
  destruct (ClassEqualCircuit.construct second fs_b (Z.of_nat left) (Z.of_nat right) _ _ reserve observations Harena_b Hflag_b Hfalse_b Hleftword Hrightword Hmeaning_left Hmeaning_right Hcircuit_budget)
    as [built [next [ids [Htrace [Hbuilt_frame [Harena_next [Hflag_next [Hrep [Hprefix_next Hremaining]]]]]]]]].
  pose proof (ClassEqualCircuit.result_semantics observations second (Z.of_nat left) (Z.of_nat right) built ids next _ _ Htrace Hrep) as [Hresultword Hmeaning].
  pose proof (proj1 (proj1 Harena_a)) as [Hmeta_a Hrest_a].
  pose proof (proj1 (proj1 Harena_b)) as [Hmeta_b Hrest_b].
  pose proof (proj1 (proj1 Harena_next)) as [Hmeta_next Hrest_next].
  set (final := store_meta built 0 (meta_value built 0)).
  assert (Hrun : execObserved (funcdef_0__classEqual bs ns) (s,observations) = Some (tt,(final,observations))).
  { eapply eq_trans; [exact (eliminate_correct funcdef_0__classEqual_body bs ns s observations)|].
    eapply eq_trans; [exact (unit_projection (execLocalObserved funcdef_0__classEqual_body ({|machine:=s;bools:=bs;nums:=ns|},observations)) (fun after=>(machine (fst after),snd after)))|].
    exact (ClassEqualCircuit.generated_general {|machine:=s;bools:=bs;nums:=ns|} first second built ids a b tag_a tag_b value_a value_b (Z.of_nat left) (Z.of_nat right) observations
      Hna Hnb Habound Hbbound Hrecord_a Hrecord_b Hnotzero Hfirst ltac:(lia) Hleft Hsecond ltac:(lia) Hright Htrace). }
  assert (Hfinalarena : NativeRepresentation.canonical_arena final next)
    by (apply (ArenaFrame.storage_arena built); [apply ArenaFrame.storage_meta; lia|exact Harena_next]).
  assert (Hfinalframe : RenameStorage.logical_frame s final).
  { eapply frame_trans; [exact Hframe_a|]. eapply frame_trans; [exact Hframe_b|].
    eapply frame_trans; [exact (ClassEqualSets.intern_frame _ _ Hbuilt_frame)|apply result_frame]. }
  assert (Hfinalprefix : exists extra,next=fs++extra).
  { eapply InternReserve.extends_trans; [exact Hprefix_a|]. eapply InternReserve.extends_trans; eassumption. }
  assert (Hfinalvalue : meta_value final 0 = meta_value built 0) by (unfold final; apply meta_store_same; lia).
  exists final,next,(Z.to_nat (meta_value built 0)). split; [exact Hrun|]. split; [exact Hfinalarena|]. split.
  - rewrite Hfinalvalue,Z2Nat.id by exact (proj1 Hresultword). reflexivity.
  - split; [now rewrite Z2Nat.id by exact (proj1 Hresultword)|]. split.
    + rewrite equality_formula by exact Hnonsets. now rewrite !predicate_successor in Hmeaning.
    + split; [exact Hfinalprefix|]. split.
      * unfold final. now rewrite meta_store_other by discriminate.
      * split; [exact Hfinalframe|]. split.
        -- destruct Hfinalprefix as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hfinalframe Hclasses).
        -- split; [now apply (ClassLookup.frame_wellformed s final)|exact Hremaining].
Qed.
Definition ready cls_a cls_b := match cls_a,cls_b with
| VirtualClasses.set _,VirtualClasses.set _ => True
| _,_ => ClassPredicate.fits cls_a 1 0 /\ ClassPredicate.fits cls_b 1 0 end.
Definition work cls_a cls_b := match cls_a,cls_b with
| VirtualClasses.set _,VirtualClasses.set _ => 1%nat
| _,_ => (ClassPredicate.work cls_a + ClassPredicate.work cls_b + 6)%nat end.
Definition success s bs ns fs classes cls_a cls_b observations :=
  exists final next index, execObserved (funcdef_0__classEqual bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.erase (VirtualClasses.class_equal cls_a cls_b)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8 = 0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final.
Theorem general_without_reserve s bs ns fs classes a b cls_a cls_b observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some cls_a -> nth_error classes b = Some cls_b -> nonsets cls_a cls_b ->
  ns vardef_0__classEqual_a = Z.of_nat a -> ns vardef_0__classEqual_b = Z.of_nat b ->
  ClassPredicate.fits cls_a 1 0 -> ClassPredicate.fits cls_b 1 0 ->
  Z.of_nat (length fs + ClassPredicate.work cls_a + ClassPredicate.work cls_b + 6) <= RenameInvariant.resource_limit ->
  success s bs ns fs classes cls_a cls_b observations.
Proof.
  intros Harena Hfalse Herror Hclasses Hwellformed Ha Hb Hnonsets Hna Hnb Hfits_a Hfits_b Hbudget.
  assert (Hreserve : Z.of_nat (length fs + ClassPredicate.work cls_a + ClassPredicate.work cls_b + 6 + 0) <= RenameInvariant.resource_limit) by now rewrite Nat.add_0_r.
  destruct (generated_general s bs ns fs classes a b cls_a cls_b 0 observations Harena Hfalse Herror Hclasses Hwellformed Ha Hb Hnonsets Hna Hnb Hfits_a Hfits_b Hreserve)
    as [final [next [index Hpost]]]. exists final,next,index. tauto.
Qed.
Theorem generated_refines s bs ns fs classes a b cls_a cls_b observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some cls_a -> nth_error classes b = Some cls_b ->
  ns vardef_0__classEqual_a = Z.of_nat a -> ns vardef_0__classEqual_b = Z.of_nat b ->
  ready cls_a cls_b -> Z.of_nat (length fs + work cls_a cls_b) <= RenameInvariant.resource_limit ->
  success s bs ns fs classes cls_a cls_b observations.
Proof.
  intros Harena Hfalse Herror Hclasses Hwellformed Ha Hb Hna Hnb Hready Hbudget.
  destruct cls_a as [i|p]; destruct cls_b as [j|q]; cbn [ready work] in Hready,Hbudget.
  - apply (ClassEqualSets.generated_refines s bs ns fs classes a b i j observations Harena Herror); try assumption.
    repeat rewrite Nat2Z.inj_add in Hbudget. unfold RenameInvariant.resource_limit in *. lia.
  - eapply general_without_reserve; try eassumption.
    + unfold nonsets. intros [i0 [j0 [Hi Hj]]]. discriminate.
    + exact (proj1 Hready).
    + exact (proj2 Hready).
    + repeat rewrite Nat2Z.inj_add in *. lia.
  - eapply general_without_reserve; try eassumption.
    + unfold nonsets. intros [i0 [j0 [Hi Hj]]]. discriminate.
    + exact (proj1 Hready).
    + exact (proj2 Hready).
    + repeat rewrite Nat2Z.inj_add in *. lia.
  - eapply general_without_reserve; try eassumption.
    + unfold nonsets. intros [i0 [j0 [Hi Hj]]]. discriminate.
    + exact (proj1 Hready).
    + exact (proj2 Hready).
    + repeat rewrite Nat2Z.inj_add in *. lia.
Qed.
End ClassEqualRefinement.
