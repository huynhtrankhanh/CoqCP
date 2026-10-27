From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash Representation FormulaTopology ClassStorage ClassLookup
 RenameMemoCallers RenameMemoClassEqual RenameMemoClassMember RenameMemoBounds RenameMemoInput
 RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition AxiomTaggedInvariant
 SchemaEvaluationResources SchemaEvaluationBoundedCell SchemaEvaluationIndexBounds.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexBudget.
Import IndexExecution SipHashExecution.
Lemma classes_lookup bound entries index cls : SchemaEvaluationIndexBounds.classes bound entries ->
 nth_error entries index=Some cls -> SchemaEvaluationIndexBounds.class_bound bound cls.
Proof.
 intros H. induction H as [|head entries Hhead Htail IH] in index|-*.
 - destruct index;discriminate.
 - destruct index as [|index];cbn [nth_error];intro Hlookup;[injection Hlookup as <-;exact Hhead|exact (IH index Hlookup)].
Qed.
Lemma source_bounds native fs root p bound :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> nth_error fs root=Some p ->
 RenameMemoIndexBounds.formula_bound bound p /\ (RenameMemoTransition.height p<=root)%nat.
Proof.
 intros Harena Htop Hraw Hlookup. eapply RenameMemoInput.canonical_source_bounds;try eassumption.
 intros node Hnode. apply Hraw. assert (Hroot:(root<length fs)%nat) by (apply nth_error_Some;congruence). lia.
Qed.
Lemma growth_bound native fs entries index cls capacity :
 ClassStorage.represents native fs entries -> ClassLookup.wellformed native -> nth_error entries index=Some cls ->
 (0<length fs)%nat -> (length fs<=capacity)%nat ->
 (RenameMemoCallers.predicate_growth native index<=capacity*capacity)%nat.
Proof.
 intros Hclasses Hgood Hlookup Hpositive Hcapacity.
 destruct (ClassLookup.lookup native fs entries index cls Hclasses Hgood Hlookup) as [_ Hclass].
 unfold RenameMemoCallers.predicate_growth.
 destruct Hclass as [[variable [-> [Hword Hrecord]]]|[root [p [-> [Hp Hrecord]]]]];rewrite Hrecord.
 - nia.
 - rewrite Nat2Z.id. assert (Hroot:(root<length fs)%nat) by (apply nth_error_Some;congruence). nia.
Qed.
Lemma predicate_ready native fs entries index cls shift arg bound capacity :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 ClassStorage.represents native fs entries -> ClassLookup.wellformed native -> nth_error entries index=Some cls ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> SchemaEvaluationIndexBounds.class_bound bound cls ->
 (length fs<=capacity)%nat ->
 Z.of_nat (5*(capacity*capacity)+1)<=maximum ->
 Z.of_nat (length fs+capacity*capacity)<=RenameMemoResourceBounds.doubling_limit ->
 Z.of_nat bound+Z.of_nat shift<=maximum -> Z.of_nat bound+Z.of_nat arg<=maximum ->
 RenameMemoCallers.predicate_ready native fs index shift arg.
Proof.
 intros Harena Htop Hclasses Hgood Hlookup Hraw Hbound Hcapacity Hfuel Hroom Hshift Harg.
 destruct (ClassLookup.lookup native fs entries index cls Hclasses Hgood Hlookup) as [_ Hclass].
 unfold RenameMemoCallers.predicate_ready.
 destruct Hclass as [[variable [-> [Hword Hrecord]]]|[root [p [-> [Hp Hrecord]]]]];rewrite Hrecord,Nat2Z.id.
 - cbn [SchemaEvaluationIndexBounds.class_bound] in Hbound. split.
   + repeat rewrite Nat2Z.inj_add in Hroom. lia.
   + unfold word. rewrite Nat2Z.inj_add. lia.
 - assert (Hroot:(root<length fs)%nat) by (apply nth_error_Some;congruence).
   assert (Hsquare:(S root*S root<=capacity*capacity)%nat) by nia.
   assert (Hcomputed:(RenameMemoInput.indices_max native (S root)<=bound)%nat).
   { apply SchemaEvaluationIndexBounds.indices_max_bound.
     exact (SchemaEvaluationIndexBounds.raw_arena_prefix native (S root) (length fs) bound ltac:(lia) Hraw). }
   split.
   + unfold RenameMemoBounds.fuel. repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
   + split.
     * repeat rewrite Nat2Z.inj_add in *. lia.
     * split;lia.
Qed.
Lemma equal_ready native fs entries bound capacity reserve :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 ClassStorage.represents native fs entries -> ClassLookup.wellformed native ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> SchemaEvaluationIndexBounds.classes bound entries ->
 (0<length fs)%nat -> (length fs<=capacity)%nat ->
 Z.of_nat (5*(capacity*capacity)+1)<=maximum -> Z.of_nat bound+2<=maximum ->
 Z.of_nat (length fs+(2*(capacity*capacity)+6)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationBoundedCell.equal native fs entries reserve.
Proof.
 intros Harena Htop Hclasses Hgood Hraw Hbounds Hpositive Hcapacity Hfuel Hindices Hroom ia ib ca cb Ha Hb.
 pose proof (classes_lookup bound entries ia ca Hbounds Ha) as Hca.
 pose proof (classes_lookup bound entries ib cb Hbounds Hb) as Hcb.
 pose proof (growth_bound native fs entries ia ca capacity Hclasses Hgood Ha Hpositive Hcapacity) as HgrowthA.
 pose proof (growth_bound native fs entries ib cb capacity Hclasses Hgood Hb Hpositive Hcapacity) as HgrowthB.
 assert (HpredicateRoom:Z.of_nat (length fs+capacity*capacity)<=RenameMemoResourceBounds.doubling_limit).
 { repeat rewrite Nat2Z.inj_add in *. lia. }
 assert (HreadyA:RenameMemoCallers.predicate_ready native fs ia 1 0).
 { eapply predicate_ready;try eassumption;lia. }
 assert (HreadyB:RenameMemoCallers.predicate_ready native fs ib 1 0).
 { eapply predicate_ready;try eassumption;lia. }
 split.
 - destruct ca,cb;cbn [RenameMemoClassEqual.ready];auto.
 - destruct ca,cb;cbn [RenameMemoClassEqual.work];repeat rewrite Nat2Z.inj_add in *;lia.
Qed.
Lemma member_ready native fs entries bound capacity reserve :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 ClassStorage.represents native fs entries -> ClassLookup.wellformed native ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> SchemaEvaluationIndexBounds.classes bound entries ->
 (0<length fs)%nat -> (length fs<=capacity)%nat ->
 Z.of_nat (5*(capacity*capacity)+1)<=maximum -> 2*Z.of_nat bound+3<=maximum ->
 Z.of_nat (length fs+(2*(capacity*capacity)+13)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationBoundedCell.member native fs entries reserve.
Proof.
 intros Harena Htop Hclasses Hgood Hraw Hbounds Hpositive Hcapacity Hfuel Hindices Hroom ia ib ca cb Ha Hb.
 pose proof (classes_lookup bound entries ia ca Hbounds Ha) as Hca.
 pose proof (classes_lookup bound entries ib cb Hbounds Hb) as Hcb.
 pose proof (growth_bound native fs entries ia ca capacity Hclasses Hgood Ha Hpositive Hcapacity) as HgrowthA.
 pose proof (growth_bound native fs entries ib cb capacity Hclasses Hgood Hb Hpositive Hcapacity) as HgrowthB.
 assert (HpredicateRoom:Z.of_nat (length fs+capacity*capacity)<=RenameMemoResourceBounds.doubling_limit).
 { repeat rewrite Nat2Z.inj_add in *. lia. }
 split.
 - destruct ca as [variable|p];cbn [RenameMemoClassMember.ready].
   + cbn [SchemaEvaluationIndexBounds.class_bound] in Hca. eapply predicate_ready;try eassumption;lia.
   + split; eapply predicate_ready;try eassumption;lia.
 - destruct ca;cbn [RenameMemoClassMember.work];repeat rewrite Nat2Z.inj_add in *;lia.
Qed.
Definition axiom_cost capacity tag := AxiomTaggedInvariant.cost tag (capacity-1).
Lemma cost_bound capacity tag root : (0<capacity)%nat ->
 (AxiomTaggedInvariant.uses_rename tag=true -> (root<capacity)%nat) ->
 (AxiomTaggedInvariant.cost tag root<=axiom_cost capacity tag)%nat.
Proof.
 intros Hpositive Hroot. unfold axiom_cost.
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 all: cbn [AxiomTaggedInvariant.cost];try lia.
 all: assert (Hlt:(root<capacity)%nat) by (apply Hroot;reflexivity);nia.
Qed.
Lemma rename_needs_p tag : AxiomTaggedInvariant.uses_rename tag=true -> AxiomTaggedInvariant.needs_p tag=true.
Proof.
 unfold AxiomTaggedInvariant.uses_rename,AxiomTaggedInvariant.needs_p.
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 18%nat tag.
 all: cbn [existsb Nat.eqb orb];congruence.
Qed.
Lemma shifted_ready native fs entries rho depth a bound capacity reserve :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> SchemaEvaluationIndexBounds.classes bound entries ->
 SchemaEvaluationResources.argument native entries rho a -> (length fs<=capacity)%nat ->
 SchemaEvaluationResources.class_room entries ->
 Z.of_nat (5*(capacity*capacity)+1)<=maximum -> Z.of_nat bound+Z.of_nat depth<=maximum ->
 Z.of_nat (length fs+capacity*capacity+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationBoundedCell.shifted native fs entries rho depth a reserve.
Proof.
 intros Harena Htop Hraw Hclasses Hargument Hcapacity Hclassroom Hfuel Hindices Hroom.
 split;[exact Hargument|]. intro Hpositive. split;[exact Hclassroom|]. split.
 - intros variable Heq. destruct Hargument as (id & Hargument & Hword & Hlookup).
   rewrite Heq in Hlookup. pose proof (classes_lookup bound entries id (VirtualClasses.set variable) Hclasses Hlookup) as Hbound.
   cbn [SchemaEvaluationIndexBounds.class_bound] in Hbound. lia.
 - intros cls root p Hrecord Hlookup.
   destruct (source_bounds native fs root p bound Harena Htop Hraw Hlookup) as [Hbound Hheight].
   assert (Hroot:(root<length fs)%nat) by (apply nth_error_Some;congruence).
   assert (Hsquare:(S root*S root<=capacity*capacity)%nat) by nia.
   exists bound. split.
   + unfold RenameMemoBounds.fuel. repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
   + split;[exact Hbound|]. split;[exact Hindices|]. split.
     * unfold maximum in *. repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
     * unfold RenameMemoResourceBounds.doubling_limit in Hroom. repeat rewrite Nat2Z.inj_add in *. lia.
Qed.
Lemma axiom_ready native fs tag rawJ bound capacity reserve :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound ->
 (0<length fs)%nat -> (length fs<=capacity)%nat ->
 (AxiomTaggedInvariant.uses_rename tag=true -> Z.of_nat (5*(capacity*capacity)+1)<=maximum) ->
 Z.of_nat bound+Z.of_nat rawJ+2<=maximum ->
 Z.of_nat (length fs+axiom_cost capacity tag+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationBoundedCell.axiom fs tag rawJ reserve.
Proof.
 intros Harena Htop Hraw Hpositive Hcapacity Hfuel Hindices Hroom root p Hword Hlookup.
 assert (Hroot:AxiomTaggedInvariant.uses_rename tag=true -> (root<length fs)%nat).
 { intro Hrename. specialize (Hlookup (rename_needs_p tag Hrename)). apply nth_error_Some;congruence. }
 pose proof (cost_bound capacity tag root ltac:(lia) ltac:(intro H;specialize (Hroot H);lia)) as Hcost.
 exists bound. split;[|unfold RenameMemoResourceBounds.doubling_limit in Hroom;repeat rewrite Nat2Z.inj_add in *;lia].
 unfold AxiomTaggedInvariant.renaming_ready. destruct (AxiomTaggedInvariant.uses_rename tag) eqn:Huses;[|exact I].
 specialize (Hfuel eq_refl). specialize (Hlookup (rename_needs_p tag Huses)). specialize (Hroot eq_refl).
 destruct (source_bounds native fs root p bound Harena Htop Hraw Hlookup) as [Hbound Hheight].
 assert (Hsquare:(S root*S root<=capacity*capacity)%nat) by nia.
 split.
 - unfold RenameMemoBounds.fuel. repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
 - split;[exact Hbound|]. split.
   + assert (Hinc:(AxiomTaggedInvariant.increment tag rawJ<=rawJ+2)%nat).
     { unfold AxiomTaggedInvariant.increment. destruct tag as [|[|[|[|[|tag]]]]];cbn;lia. }
     apply Nat2Z.inj_le in Hinc. rewrite Nat2Z.inj_add in Hinc. lia.
   + unfold maximum in *. repeat rewrite Nat2Z.inj_add in *. repeat rewrite Nat2Z.inj_mul in *. nia.
Qed.
Definition cost capacity kind tag depth := match kind with
 | 0%nat=>if Nat.eqb depth 0 then 0%nat else (capacity*capacity)%nat
 | 4%nat=>(2*(capacity*capacity)+6)%nat
 | 5%nat=>(2*(capacity*capacity)+13)%nat
 | 6%nat | 7%nat | 10%nat=>1%nat
 | 8%nat=>axiom_cost capacity tag
 | _=>0%nat end.
Definition renames kind tag depth := match kind with
 | 0%nat=>negb (Nat.eqb depth 0) | 4%nat | 5%nat=>true
 | 8%nat=>AxiomTaggedInvariant.uses_rename tag | _=>false end.
Definition needs_class kind depth := match kind with
 | 0%nat=>negb (Nat.eqb depth 0) | 3%nat=>true | _=>false end.
Definition index_step kind bound depth b c d := match kind with
 | 0%nat=>(bound+depth)%nat | 4%nat=>(bound+2)%nat | 5%nat=>(2*bound+3)%nat
 | 8%nat=>(bound+b+c+d+4)%nat | _=>bound end.
Definition numeric capacity bound class_count reserve depth kind a b c d :=
 Z.of_nat (capacity+cost capacity kind a depth+reserve)<=RenameMemoResourceBounds.doubling_limit /\
 (renames kind a depth=true -> Z.of_nat (5*(capacity*capacity)+1)<=maximum) /\
 (needs_class kind depth=true -> Z.of_nat (class_count+1)<=maximum) /\
 Z.of_nat (index_step kind bound depth b c d)<=maximum.
Theorem ready native fs entries rho bound capacity class_count reserve depth kind a b c d :
 NativeRepresentation.canonical_arena native fs -> FormulaTopology.ordered native (length fs) ->
 ClassStorage.represents native fs entries -> ClassLookup.wellformed native ->
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound -> SchemaEvaluationIndexBounds.classes bound entries ->
 (0<length fs)%nat -> (length fs<=capacity)%nat -> (length entries<=class_count)%nat ->
 (kind=0%nat -> SchemaEvaluationResources.argument native entries rho a) ->
 numeric capacity bound class_count reserve depth kind a b c d ->
 SchemaEvaluationBoundedCell.ready native fs entries rho depth kind a b c d reserve.
Proof.
 intros Harena Htop Hclasses Hgood Hraw Hbounds Hpositive Hcapacity HclassCount Hargument
   (Hroom & Hfuel & Hclassroom & Hindices).
 assert (Hbase:Z.of_nat (length fs+reserve)<=SchemaEvaluationBoundedCell.bound).
 { unfold RenameMemoResourceBounds.doubling_limit,SchemaEvaluationBoundedCell.bound in *. repeat rewrite Nat2Z.inj_add in *. lia. }
 split;[exact Hbase|].
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[idtac|cases rest index] end in cases 12%nat kind.
 all: cbn [SchemaEvaluationBoundedCell.ready] ;try exact I.
 - split;[exact (Hargument eq_refl)|]. intro Hdepth.
   assert (Hnonzero:Nat.eqb depth 0=false) by (apply Nat.eqb_neq;exact Hdepth).
   cbn [renames needs_class] in Hfuel,Hclassroom. rewrite Hnonzero in Hfuel,Hclassroom.
   cbn [cost] in Hroom. rewrite Hnonzero in Hroom.
   destruct (shifted_ready native fs entries rho depth a bound capacity reserve Harena Htop Hraw Hbounds
     (Hargument eq_refl) Hcapacity ltac:(unfold SchemaEvaluationResources.class_room;specialize (Hclassroom eq_refl);lia)
     (Hfuel eq_refl) ltac:(cbn [index_step] in Hindices;rewrite Nat2Z.inj_add in Hindices;exact Hindices)
     ltac:(repeat rewrite Nat2Z.inj_add in *;lia)) as [_ Hshifted]. exact (Hshifted Hdepth).
 - unfold SchemaEvaluationResources.class_room. specialize (Hclassroom eq_refl). lia.
 - eapply equal_ready;try eassumption.
   + exact (Hfuel eq_refl).
   + cbn [index_step] in Hindices. rewrite Nat2Z.inj_add in Hindices. exact Hindices.
   + cbn [cost] in Hroom. repeat rewrite Nat2Z.inj_add in *. lia.
 - eapply member_ready;try eassumption.
   + exact (Hfuel eq_refl).
   + cbn [index_step] in Hindices. rewrite Nat2Z.inj_add,Nat2Z.inj_mul in Hindices. exact Hindices.
   + cbn [cost] in Hroom. repeat rewrite Nat2Z.inj_add in *. lia.
 - cbn [cost] in Hroom. unfold RenameMemoResourceBounds.doubling_limit,SchemaEvaluationBoundedCell.bound in *. repeat rewrite Nat2Z.inj_add in *. lia.
 - cbn [cost] in Hroom. unfold RenameMemoResourceBounds.doubling_limit,SchemaEvaluationBoundedCell.bound in *. repeat rewrite Nat2Z.inj_add in *. lia.
 - eapply axiom_ready;try eassumption.
   + cbn [index_step] in Hindices. repeat rewrite Nat2Z.inj_add in Hindices. lia.
   + cbn [cost] in Hroom. repeat rewrite Nat2Z.inj_add in *. lia.
 - cbn [cost] in Hroom. unfold RenameMemoResourceBounds.doubling_limit,SchemaEvaluationBoundedCell.bound in *. repeat rewrite Nat2Z.inj_add in *. lia.
Qed.
End SchemaEvaluationIndexBudget.
