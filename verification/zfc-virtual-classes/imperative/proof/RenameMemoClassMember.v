From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash HashTable ObservedLocal InternReserve ClassStorage ClassLookup ClassEqualSets
  ClassMemberCircuit RenameMemoClassMemberRaw RenameMemoClassMemberSet RenameMemoClassEqual RenameMemoCallers RenameMemoLengths
  RenameMemoResourceBounds RenameMemoInput RenameStorage FormulaCircuit FormulaCircuitProperties FormulaEncoding Representation
  ArenaFrame FormulaTopology Intern InternGrowth RenameMemoTopology.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoClassMember.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoClassEqual.
Definition nonset cls := forall i,cls<>VirtualClasses.set i.
Lemma record s fs classes a cls : ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some cls -> nonset cls ->
  exists value,(a<length (memory s arraydef_0__classes))%nat /\ nth_error (memory s arraydef_0__classes) a=Some (1,value).
Proof.
  intros Hclasses Hwellformed Hlookup Hnonset.
  destruct (ClassLookup.lookup s fs classes a cls Hclasses Hwellformed Hlookup) as [Hbound Hclass].
  destruct Hclass as [[i [Hcls [Hword Hraw]]]|[root [p [Hcls [Hformula Hraw]]]]].
  - exfalso. exact (Hnonset i Hcls).
  - exists (Z.of_nat root). auto.
Qed.
Lemma predicate_double cls : VirtualClasses.predicate cls (fun n=>(n+2)%nat) 0=
  VirtualClasses.predicate cls (fun n=>S (S n)) 0.
Proof.
  destruct cls as [i|body]; cbn [VirtualClasses.predicate].
  - replace (i+2)%nat with (S (S i)) by lia. reflexivity.
  - apply RenameMemoCallers.rename_extensional. intros [|i]; cbn [VirtualClasses.cons]; [reflexivity|]. f_equal. lia.
Qed.
Lemma membership_formula a b : nonset a -> VirtualClasses.erase (VirtualClasses.class_member a b)=
  ClassMemberCircuit.result (VirtualClasses.predicate a (fun n=>(n+2)%nat) 0)
    (VirtualClasses.predicate b (fun n=>(n+1)%nat) 0).
Proof.
  intro Hnonset. destruct a as [i|body]; [exfalso; exact (Hnonset i eq_refl)|].
  change (SetTheory.ex (SetTheory.conj
    (SetTheory.all (SetTheory.iff (SetTheory.member 0 1) (VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>S (S n)) 0)))
    (VirtualClasses.predicate b S 0))=
    ClassMemberCircuit.result (VirtualClasses.predicate (VirtualClasses.abstract body) (fun n=>(n+2)%nat) 0)
      (VirtualClasses.predicate b (fun n=>(n+1)%nat) 0)).
  unfold ClassMemberCircuit.result. now rewrite predicate_double,predicate_successor.
Qed.
Theorem generated_general s bs ns fs classes a b cls_a cls_b reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a=Some cls_a -> nth_error classes b=Some cls_b -> nonset cls_a ->
  ns vardef_0__classMember_a=Z.of_nat a -> ns vardef_0__classMember_b=Z.of_nat b ->
  RenameMemoCallers.predicate_ready s fs a 2 0 -> RenameMemoCallers.predicate_ready s fs b 1 0 ->
  Z.of_nat (length fs+RenameMemoCallers.predicate_growth s a+RenameMemoCallers.predicate_growth s b+13+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__classMember bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (VirtualClasses.erase (VirtualClasses.class_member cls_a cls_b)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
    Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next) /\
    (length next<=length fs+(RenameMemoCallers.predicate_growth s a+RenameMemoCallers.predicate_growth s b+13))%nat.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hb Hnonset Hna Hnb Hfits_a Hfits_b Hbudget.
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  assert (Hone : word 1) by (unfold word,maximum; lia).
  assert (Htwo : word 2) by (unfold word,maximum; lia).
  destruct (record s fs classes a cls_a Hclasses Hwellformed Ha Hnonset)
    as (value_a & Habound & Hrecord_a).
  destruct (RenameMemoCallers.generated_predicate s (fun _=>false) (RenameMemoClassMemberRaw.predicate_arguments (Z.of_nat a) 2) fs classes cls_a a 2 0 observations
    Hmeta Hsip (arena_positive s fs Harena) Herror Harena Htopology Hfalse Hclasses Hwellformed Ha eq_refl eq_refl eq_refl Htwo Hzero Hfits_a)
    as (first & fs_a & left & Hfirst & Harena_a & Hleft & Hleftword & Hmeaning_a & Hprefix_a & Hflag_a & Hgrowth_a & Hframe_a & Hclasses_a & Hwellformed_a & Htopology_a).
  assert (Hfalse_a : nth_error fs_a 0 = Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hbudget_b : Z.of_nat (length fs_a)+Z.of_nat (RenameMemoCallers.predicate_growth s b)<=RenameMemoResourceBounds.doubling_limit).
  { repeat rewrite Nat2Z.inj_add in Hbudget. lia. }
  pose proof (ready_transport s first fs fs_a classes b cls_b 1 0 Harena Harena_a Hprefix_a Hframe_a Hclasses Hwellformed Hb Hfits_b Hbudget_b) as Hready_b.
  destruct (RenameMemoLengths.predicate_observed_lengths s (fun _=>false) (RenameMemoClassMemberRaw.predicate_arguments (Z.of_nat a) 2) observations first observations Hfirst)
    as [Hmeta_length_a Hsip_length_a].
  assert (Hmeta_a : (31<length (memory first arraydef_0__meta))%nat) by (rewrite Hmeta_length_a; exact Hmeta).
  assert (Hsip_a : (0<length (memory first arraydef_0__sipState))%nat) by (rewrite Hsip_length_a; exact Hsip).
  destruct (RenameMemoCallers.generated_predicate first (fun _=>false) (RenameMemoClassMemberRaw.predicate_arguments (Z.of_nat b) 1) fs_a classes cls_b b 1 0 observations
    Hmeta_a Hsip_a (arena_positive first fs_a Harena_a) Hflag_a Harena_a Htopology_a Hfalse_a Hclasses_a Hwellformed_a Hb eq_refl eq_refl eq_refl Hone Hzero Hready_b)
    as (second & fs_b & right & Hsecond & Harena_b & Hright & Hrightword & Hmeaning_b & Hprefix_b & Hflag_b & Hgrowth_b & Hframe_b & Hclasses_b & Hwellformed_b & Htopology_b).
  rewrite (RenameMemoCallers.predicate_growth_frame s first b Hframe_a) in Hgrowth_b.
  assert (Hfalse_b : nth_error fs_b 0 = Some SetTheory.falsity) by (eapply InternReserve.lookup_preserved; eassumption).
  assert (Hmeaning_left : nth_error fs_b (Z.to_nat (Z.of_nat left)) = Some (VirtualClasses.predicate cls_a (fun n=>(n+2)%nat) 0)).
  { rewrite Nat2Z.id. eapply InternReserve.lookup_preserved; eassumption. }
  assert (Hmeaning_right : nth_error fs_b (Z.to_nat (Z.of_nat right)) = Some (VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0)) by now rewrite Nat2Z.id.
  assert (Hcircuit_budget : Z.of_nat (length fs_b + 13 + reserve) <= 9223372036854775807).
  { apply Nat2Z.inj_le in Hgrowth_b. repeat rewrite Nat2Z.inj_add in *. unfold RenameMemoResourceBounds.doubling_limit in *. lia. }
  assert (Hinitial_rep : FormulaCircuit.represents fs_b [0;Z.of_nat left;Z.of_nat right]
    [SetTheory.falsity;VirtualClasses.predicate cls_a (fun n=>(n+2)%nat) 0;VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0]).
  { constructor; [split; assumption|]. constructor; [split; assumption|]. constructor; [split; assumption|constructor]. }
  destruct (FormulaCircuitProperties.complete ClassMemberCircuit.plan second fs_b [0;Z.of_nat left;Z.of_nat right]
    [SetTheory.falsity;VirtualClasses.predicate cls_a (fun n=>(n+2)%nat) 0;VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0]
    (ClassMemberCircuit.values (VirtualClasses.predicate cls_a (fun n=>(n+2)%nat) 0) (VirtualClasses.predicate cls_b (fun n=>(n+1)%nat) 0))
    reserve observations Harena_b Htopology_b Hflag_b Hinitial_rep ClassMemberCircuit.fits (ClassMemberCircuit.infer _ _) Hcircuit_budget)
    as (built & next & ids & Htrace & Hbuilt_frame & Harena_next & Hflag_next & Hrep & Hprefix_next & Hremaining & Htopology_next & Hgrowth_next).
  pose proof (RenameMemoClassMemberRaw.result_semantics observations second (Z.of_nat left) (Z.of_nat right) built ids next _ _ Htrace Hrep) as [Hresultword Hmeaning].
  pose proof (proj1 (proj1 Harena_a)) as [Hmeta_a_table Hrest_a].
  pose proof (proj1 (proj1 Harena_b)) as [Hmeta_b Hrest_b].
  pose proof (proj1 (proj1 Harena_next)) as [Hmeta_next Hrest_next].
  set (final := store_meta built 0 (meta_value built 0)).
  assert (Hrun : execObserved (funcdef_0__classMember bs ns) (s,observations) = Some (tt,(final,observations))).
  { eapply eq_trans; [exact (eliminate_correct funcdef_0__classMember_body bs ns s observations)|].
    eapply eq_trans; [exact (unit_projection (execLocalObserved funcdef_0__classMember_body ({|machine:=s;bools:=bs;nums:=ns|},observations)) (fun after=>(machine (fst after),snd after)))|].
    exact (RenameMemoClassMemberRaw.generated_general {|machine:=s;bools:=bs;nums:=ns|} first second built ids a b 1 value_a (Z.of_nat left) (Z.of_nat right) observations
      Hna Hnb Habound Hrecord_a ltac:(discriminate) Hfirst ltac:(lia) Hleft Hsecond ltac:(lia) Hright Htrace). }
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
    + rewrite membership_formula by exact Hnonset. exact Hmeaning.
    + split; [exact Hfinalprefix|]. split.
      * unfold final. now rewrite meta_store_other by discriminate.
      * split; [exact Hfinalframe|]. split.
        -- destruct Hfinalprefix as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hfinalframe Hclasses).
        -- split; [now apply (ClassLookup.frame_wellformed s final)|]. split; [exact Hremaining|]. split.
           ++ intros parent child Hparent Hchild. apply Htopology_next; [exact Hparent|].
              unfold final,HashTableInvariant.tuple_at in Hchild. now rewrite store_meta_other in Hchild by discriminate.
           ++ cbn [ClassMemberCircuit.plan length] in Hgrowth_next. lia.
Qed.
Definition work s a b cls_a (cls_b : VirtualClasses.class) := match cls_a with
  | VirtualClasses.set _=>RenameMemoCallers.predicate_growth s b
  | _=>(RenameMemoCallers.predicate_growth s a+RenameMemoCallers.predicate_growth s b+13)%nat end.
Definition ready s fs a b cls_a (cls_b : VirtualClasses.class) := match cls_a with
  | VirtualClasses.set i=>RenameMemoCallers.predicate_ready s fs b 0 i
  | _=>RenameMemoCallers.predicate_ready s fs a 2 0 /\ RenameMemoCallers.predicate_ready s fs b 1 0 end.
Theorem generated_refines s bs ns fs classes a b cls_a cls_b reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> nth_error fs 0=Some SetTheory.falsity -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s -> nth_error classes a=Some cls_a -> nth_error classes b=Some cls_b ->
  ns vardef_0__classMember_a=Z.of_nat a -> ns vardef_0__classMember_b=Z.of_nat b -> ready s fs a b cls_a cls_b ->
  Z.of_nat (length fs+work s a b cls_a cls_b+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  exists final next index, execObserved (funcdef_0__classMember bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (VirtualClasses.erase (VirtualClasses.class_member cls_a cls_b)) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
    Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next) /\
    (length next<=length fs+work s a b cls_a cls_b)%nat.
Proof.
  intros Hmeta Hsip Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hb Hna Hnb Hready Hbudget.
  destruct cls_a as [i|body]; cbn [ready work] in Hready,Hbudget |- *.
  - destruct (RenameMemoClassMemberSet.generated_refines s bs ns fs classes a b i cls_b observations
      Hmeta Hsip (arena_positive s fs Harena) Harena Htopology Hfalse Herror Hclasses Hwellformed Ha Hb Hna Hnb Hready)
      as (final & next & index & Hrun & Hnext & Hindex & Hword & Hmeaning & Hprefix & Hflag & Hgrowth & Hframe & Hclasses_final & Hwellformed_final & Hordered).
    exists final,next,index. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hindex|]. split; [exact Hword|].
    split; [exact Hmeaning|]. split; [exact Hprefix|]. split; [exact Hflag|]. split; [exact Hframe|].
    split; [exact Hclasses_final|]. split; [exact Hwellformed_final|]. split; [lia|]. now split.
  - destruct Hready as [Hready_a Hready_b]. eapply generated_general with (a:=a) (b:=b); try eassumption; try lia.
    intros i Hbad. discriminate.
Qed.
End RenameMemoClassMember.
