From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash HashTable ObservedLocal InternReserve ClassStorage ClassLookup ClassEqualSets
  ClassEqualCircuit RenameMemoCallers RenameMemoLengths RenameMemoResourceBounds RenameMemoInput
  RenameStorage FormulaCircuit FormulaCircuitProperties FormulaEncoding Representation ArenaFrame FormulaTopology
  Intern InternGrowth RenameMemoTopology.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoClassEqual.
Import IndexExecution SipHashExecution ObservedLocal.
Lemma arena_positive s fs : NativeRepresentation.canonical_arena s fs -> 0<meta_value s 20.
Proof. intro Harena. destruct (proj1 (proj1 Harena)) as [_ [_ [Hpositive _]]]. exact Hpositive. Qed.
Theorem ready_transport s t fs next classes index cls shift arg :
  NativeRepresentation.canonical_arena s fs -> NativeRepresentation.canonical_arena t next ->
  (exists extra,next=fs++extra) -> RenameStorage.logical_frame s t ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s -> nth_error classes index=Some cls ->
  RenameMemoCallers.predicate_ready s fs index shift arg ->
  Z.of_nat (length next)+Z.of_nat (RenameMemoCallers.predicate_growth s index)<=RenameMemoResourceBounds.doubling_limit ->
  RenameMemoCallers.predicate_ready t next index shift arg.
Proof.
  intros Harena Hnext Hprefix Hframe Hclasses Hwellformed Hlookup Hready Hcapacity.
  destruct (ClassLookup.lookup s fs classes index cls Hclasses Hwellformed Hlookup) as [Hclassbound Hclass].
  destruct Hframe as [Ha _].
  assert (Hraws : memory t arraydef_0__classes=memory s arraydef_0__classes) by (apply Ha; repeat split; discriminate).
  unfold RenameMemoCallers.predicate_ready. rewrite Hraws.
  unfold RenameMemoCallers.predicate_ready in Hready.
  unfold RenameMemoCallers.predicate_growth in Hcapacity.
  destruct Hclass as [[variable [Hcls [Hvariable Hraw]]]|[root [p [Hcls [Hp Hraw]]]]];
    rewrite Hraw,Nat2Z.id in *.
  - destruct Hready as [Hold Hsum]. split; [lia|exact Hsum].
  - destruct Hready as [Hfuel [Hroom [Hshift Harg]]].
    assert (Hroot : (root<length fs)%nat) by (apply nth_error_Some; congruence).
    rewrite (RenameMemoCallers.indices_max_prefix s t fs next (S root) Harena Hnext Hprefix ltac:(lia)).
    split; [exact Hfuel|]. split; [exact Hcapacity|]. now split.
Qed.
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
  apply RenameMemoCallers.rename_extensional. intros [|i]; cbn [VirtualClasses.cons]; [reflexivity|now rewrite Nat.add_1_r].
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
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some cls_a -> nth_error classes b = Some cls_b -> nonsets cls_a cls_b ->
  ns vardef_0__classEqual_a = Z.of_nat a -> ns vardef_0__classEqual_b = Z.of_nat b ->
  RenameMemoCallers.predicate_ready s fs a 1 0 -> RenameMemoCallers.predicate_ready s fs b 1 0 ->
  Z.of_nat (length fs + RenameMemoCallers.predicate_growth s a + RenameMemoCallers.predicate_growth s b + 6 + reserve) <= RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__classEqual bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.erase (VirtualClasses.class_equal cls_a cls_b)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8 = 0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
    Z.of_nat (length next + reserve) <= RenameMemoResourceBounds.doubling_limit /\
    FormulaTopology.ordered final (length next) /\
    (length next<=length fs+(RenameMemoCallers.predicate_growth s a+RenameMemoCallers.predicate_growth s b+6))%nat.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hb Hnonsets Hna Hnb Hfits_a Hfits_b Hbudget.
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Hone : word 1) by (unfold word,maximum; lia).
  destruct (records s fs classes a b cls_a cls_b Hclasses Hwellformed Ha Hb Hnonsets)
    as [tag_a [value_a [tag_b [value_b [Habound [Hbbound [Hrecord_a [Hrecord_b Hnotzero]]]]]]]].
  destruct (RenameMemoCallers.generated_predicate s (fun _=>false) (ClassEqualCircuit.predicate_arguments (Z.of_nat a)) fs classes cls_a a 1 0 observations
    Hmeta Hsip (arena_positive s fs Harena) Herror Harena Htopology Hfalse Hclasses Hwellformed Ha eq_refl eq_refl eq_refl Hone Hzero Hfits_a)
    as (first & fs_a & left & Hfirst & Harena_a & Hleft & Hleftword & Hmeaning_a & Hprefix_a & Hflag_a & Hgrowth_a & Hframe_a & Hclasses_a & Hwellformed_a & Htopology_a).
  assert (Hfalse_a : nth_error fs_a 0 = Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hbudget_b : Z.of_nat (length fs_a)+Z.of_nat (RenameMemoCallers.predicate_growth s b)<=RenameMemoResourceBounds.doubling_limit).
  { repeat rewrite Nat2Z.inj_add in Hbudget. lia. }
  pose proof (ready_transport s first fs fs_a classes b cls_b 1 0 Harena Harena_a Hprefix_a Hframe_a Hclasses Hwellformed Hb Hfits_b Hbudget_b) as Hready_b.
  destruct (RenameMemoLengths.predicate_observed_lengths s (fun _=>false) (ClassEqualCircuit.predicate_arguments (Z.of_nat a)) observations first observations Hfirst)
    as [Hmeta_length_a Hsip_length_a].
  assert (Hmeta_a : (31<length (memory first arraydef_0__meta))%nat) by (rewrite Hmeta_length_a; exact Hmeta).
  assert (Hsip_a : (0<length (memory first arraydef_0__sipState))%nat) by (rewrite Hsip_length_a; exact Hsip).
  destruct (RenameMemoCallers.generated_predicate first (fun _=>false) (ClassEqualCircuit.predicate_arguments (Z.of_nat b)) fs_a classes cls_b b 1 0 observations
    Hmeta_a Hsip_a (arena_positive first fs_a Harena_a) Hflag_a Harena_a Htopology_a Hfalse_a Hclasses_a Hwellformed_a Hb eq_refl eq_refl eq_refl Hone Hzero Hready_b)
    as (second & fs_b & right & Hsecond & Harena_b & Hright & Hrightword & Hmeaning_b & Hprefix_b & Hflag_b & Hgrowth_b & Hframe_b & Hclasses_b & Hwellformed_b & Htopology_b).
  rewrite (RenameMemoCallers.predicate_growth_frame s first b Hframe_a) in Hgrowth_b.
  assert (Hfalse_b : nth_error fs_b 0 = Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hmeaning_left : nth_error fs_b (Z.to_nat (Z.of_nat left)) = Some (VirtualClasses.predicate cls_a (fun n=>(n+1)%nat) 0)).
  { rewrite Nat2Z.id. eapply InternReserve.lookup_preserved; eassumption. }
  assert (Hmeaning_right : nth_error fs_b (Z.to_nat (Z.of_nat right)) = Some (VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0)) by now rewrite Nat2Z.id.
  assert (Hcircuit_budget : Z.of_nat (length fs_b + 6 + reserve) <= 9223372036854775807).
  { apply Nat2Z.inj_le in Hgrowth_b. repeat rewrite Nat2Z.inj_add in *. unfold RenameMemoResourceBounds.doubling_limit in *. lia. }
  assert (Hinitial_rep : FormulaCircuit.represents fs_b [0;Z.of_nat left;Z.of_nat right]
    [SetTheory.falsity;VirtualClasses.predicate cls_a (fun n=>(n+1)%nat) 0;VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0]).
  { constructor; [split; assumption|]. constructor; [split; assumption|]. constructor; [split; assumption|constructor]. }
  destruct (FormulaCircuitProperties.complete ClassEqualCircuit.plan second fs_b [0;Z.of_nat left;Z.of_nat right]
    [SetTheory.falsity;VirtualClasses.predicate cls_a (fun n=>(n+1)%nat) 0;VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0]
    (ClassEqualCircuit.values (VirtualClasses.predicate cls_a (fun n=>(n+1)%nat) 0) (VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0))
    reserve observations Harena_b Htopology_b Hflag_b Hinitial_rep ClassEqualCircuit.fits (ClassEqualCircuit.infer _ _) Hcircuit_budget)
    as (built & next & ids & Htrace & Hbuilt_frame & Harena_next & Hflag_next & Hrep & Hprefix_next & Hremaining & Htopology_next & Hgrowth_next).
  pose proof (ClassEqualCircuit.result_semantics observations second (Z.of_nat left) (Z.of_nat right) built ids next _ _ Htrace Hrep) as [Hresultword Hmeaning].
  pose proof (proj1 (proj1 Harena_a)) as [Hmeta_a_table Hrest_a].
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
        -- split; [now apply (ClassLookup.frame_wellformed s final)|]. split; [exact Hremaining|]. split.
           ++ intros parent child Hparent Hchild. apply Htopology_next; [exact Hparent|].
              unfold final,HashTableInvariant.tuple_at in Hchild. now rewrite store_meta_other in Hchild by discriminate.
           ++ cbn [ClassEqualCircuit.plan length] in Hgrowth_next. lia.
Qed.
Theorem generated_sets s bs ns fs classes a b left right reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some (VirtualClasses.set left) -> nth_error classes b=Some (VirtualClasses.set right) ->
  ns vardef_0__classEqual_a=Z.of_nat a -> ns vardef_0__classEqual_b=Z.of_nat b ->
  Z.of_nat (length fs+1+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__classEqual bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (VirtualClasses.erase (VirtualClasses.class_equal (VirtualClasses.set left) (VirtualClasses.set right))) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
    Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+1)%nat.
Proof.
  intros Harena Htopology Herror Hclasses Hwellformed Hleft Hright Ha Hb Hbudget.
  destruct (ClassEqualSets.set_lookup s fs classes a left Hclasses Hwellformed Hleft) as [Habound [Hleftword Hleftrecord]].
  destruct (ClassEqualSets.set_lookup s fs classes b right Hclasses Hwellformed Hright) as [Hbbound [Hrightword Hrightrecord]].
  set (arguments:=ClassEqualSets.arguments (Z.of_nat left) (Z.of_nat right)).
  assert (Hnormal : FormulaEncoding.normal (arguments vardef_0__intern_tag,arguments vardef_0__intern_a,arguments vardef_0__intern_b)).
  { change (FormulaEncoding.normal (1,Z.of_nat left,Z.of_nat right)). right. left. auto. }
  assert (Hdecode : FormulaEncoding.decode fs (arguments vardef_0__intern_tag,arguments vardef_0__intern_a,arguments vardef_0__intern_b)=Some (SetTheory.equal left right)).
  { change (Some (SetTheory.equal (Z.to_nat (Z.of_nat left)) (Z.to_nat (Z.of_nat right)))=Some (SetTheory.equal left right)). now rewrite !Nat2Z.id. }
  destruct (InternReserve.generated_refines s (fun _=>false) arguments fs (SetTheory.equal left right) reserve observations
    Harena Herror ltac:(replace (length fs+S reserve)%nat with (length fs+1+reserve)%nat by lia; exact Hbudget) Hnormal Hdecode)
    as (final & next & index & Hintern & Hlogical & Hnext & Hflag & Hindex & Hword & Hmeaning & Hextends & Hreserve).
  assert (Hplain : exec (funcdef_0__intern (fun _=>false) arguments) s=Some (tt,final)).
  { pose proof (execObserved_erases (funcdef_0__intern (fun _=>false) arguments) (s,observations)) as Herased.
    rewrite Hintern in Herased. exact (eq_sym Herased). }
  assert (Hcapacity : Z.of_nat (length fs)<=9223372036854775807).
  { unfold RenameMemoResourceBounds.doubling_limit in Hbudget. rewrite Nat2Z.inj_add in Hbudget. lia. }
  pose proof (InternGrowth.at_most_one s final _ _ fs next Harena Herror Hcapacity Hplain Hnext) as Hgrowth.
  pose proof (ClassEqualSets.intern_frame s final Hlogical) as Hframe.
  exists final,next,index. split.
  - eapply ClassEqualSets.generated_helper; eassumption.
  - split; [exact Hnext|]. split; [exact Hindex|]. split; [exact Hword|]. split; [exact Hmeaning|].
    split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hframe|]. split.
    + destruct Hextends as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hframe Hclasses).
    + split; [now apply (ClassLookup.frame_wellformed s final)|]. split; [exact Hreserve|]. split.
      * exact (RenameMemoTopology.preserves s final fs next Harena Hnext Hextends Hgrowth Htopology).
      * lia.
Qed.
Definition work s a b cls_a cls_b := match cls_a,cls_b with
  | VirtualClasses.set _,VirtualClasses.set _=>1%nat
  | _,_ => (RenameMemoCallers.predicate_growth s a+RenameMemoCallers.predicate_growth s b+6)%nat end.
Definition ready s fs a b cls_a cls_b := match cls_a,cls_b with
  | VirtualClasses.set _,VirtualClasses.set _=>True
  | _,_ => RenameMemoCallers.predicate_ready s fs a 1 0 /\ RenameMemoCallers.predicate_ready s fs b 1 0 end.
Theorem generated_refines s bs ns fs classes a b cls_a cls_b reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) ->
  nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s -> nth_error classes a=Some cls_a -> nth_error classes b=Some cls_b ->
  ns vardef_0__classEqual_a=Z.of_nat a -> ns vardef_0__classEqual_b=Z.of_nat b -> ready s fs a b cls_a cls_b ->
  Z.of_nat (length fs+work s a b cls_a cls_b+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__classEqual bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (VirtualClasses.erase (VirtualClasses.class_equal cls_a cls_b)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
    Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
    FormulaTopology.ordered final (length next) /\ (length next<=length fs+work s a b cls_a cls_b)%nat.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hb Hna Hnb Hready Hbudget.
  destruct cls_a as [left|body_a],cls_b as [right|body_b]; cbn [ready work] in Hready,Hbudget |- *.
  all: first [eapply generated_sets with (a:=a) (b:=b); eassumption|
    destruct Hready as [Hready_a Hready_b]; eapply generated_general with (a:=a) (b:=b);
    try eassumption; try lia; intros [i [j [Hbad Hbad']]]; discriminate].
Qed.
End RenameMemoClassEqual.
