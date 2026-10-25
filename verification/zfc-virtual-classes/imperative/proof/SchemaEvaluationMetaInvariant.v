From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash Lift ObservedLocal NativePrimitives ArenaFrame FormulaProjection
  SchemaEvaluationMeta SchemaPairSemantic SchemaEvaluation SchemaPair SchemaPairStep SchemaShiftClass Representation FormulaTopology ClassStorage ClassLookup SchemaClass RenameMemoControl RenameMemoRun RenameMemoBounds
  RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths
  RenameMemoClassEqual RenameStack RenameStorage InternReserve HashTable.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationMetaInvariant.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics SchemaShiftClass SchemaEvaluationMeta SchemaPair SchemaPairStep SchemaPairSemantic.
Theorem shift_abstract_refines s bs ns fs classes cls root p depth bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error (memory s arraydef_0__classes) cls=Some (1,Z.of_nat root) -> nth_error fs root=Some p ->
  nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__schemaShiftClass_cls=Z.of_nat cls -> ns vardef_0__schemaShiftClass_depth=Z.of_nat depth -> (0<depth)%nat ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
  Z.of_nat bound+Z.of_nat depth<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
  Z.of_nat (length fs+S root*S root)<=9223372036854775807 ->
  Z.of_nat (length classes+S reserve)<=maximum ->
  exists final next,
    execObserved (funcdef_0__schemaShiftClass bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\
    ClassStorage.represents final next (classes++[Schemata.shifted_class depth (VirtualClasses.abstract (VirtualClasses.core p))]) /\
    meta_value final 0=Z.of_nat (length classes) /\ meta_value final 8=0 /\
    (exists extra,next=fs++extra) /\ FormulaTopology.ordered final (length next) /\
    (length next<=length fs+S root*S root)%nat /\
    Z.of_nat (length (classes++[Schemata.shifted_class depth (VirtualClasses.abstract (VirtualClasses.core p))])+reserve)<=maximum /\
    stdin final=stdin s /\ stdout final=stdout s /\ ClassLookup.wellformed final /\ meta_value final 18=meta_value s 18.
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hclasses Hgood Hraw Hlookup Hfalse Hcls Hdepth Hpositive Hfuel Hbound Hindices Hheight Hbudget Hclassbudget.
  pose proof (ArenaFrame.storage_arena s (started s cls) fs (started_storage s cls) Harena) as Hstartarena.
  assert (Hstarttopology:FormulaTopology.ordered (started s cls) (length fs)).
  { intros parent child Hparent Hchild. apply Htopology;[exact Hparent|]. exact Hchild. }
  assert (Hstartmeta:(31<length (memory (started s cls) arraydef_0__meta))%nat)
    by (unfold started;rewrite store_meta_length;exact Hmeta).
  assert (Hstartsip:(0<length (memory (started s cls) arraydef_0__sipState))%nat)
    by (unfold started;rewrite store_meta_other by discriminate;exact Hsip).
  assert (Hstarterror:meta_value (started s cls) 8=0)
    by (unfold started;rewrite meta_store_other by lia;exact Herror).
  destruct (RenameMemoCallers.shift_checks bound depth Hindices) as (Hshiftword & Hargword & Hindexroom).
  assert (Hroom:Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit).
  { unfold RenameMemoResourceBounds.doubling_limit. now rewrite <-Nat2Z.inj_add. }
  destruct (RenameMemoRun.generated (started s cls) (fun _=>false) (rename_arguments (Z.of_nat root) (Z.of_nat depth))
    fs p root 1 shift_mode depth 0 bound Hstartmeta Hstartsip (RenameMemoClassEqual.arena_positive _ _ Hstartarena)
    Hstarterror Hstartarena Hstarttopology Hlookup Hfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom
    Hshiftword Hargword Hbound Hindexroom Hheight observations)
    as (rframe & next & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology).
  rewrite shifted_abstract in Hrmeaning.
  pose proof (RenameMemoOutput.source_extension fs next Hrsource) as Hrprefix.
  pose proof (RenameStorage.rename_frame _ _ _ _ _ _ Hrename) as Hrframe.
  assert (Hrclasses:ClassStorage.represents (machine rframe) next classes).
  { destruct Hrprefix as [extra Hextra]. rewrite Hextra. eapply (RenameStorage.classes_transport (started s cls));[exact Hrframe|now apply started_classes]. }
  pose proof (proj1 (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename)) as Hrmeta.
  assert (Hrmeta8:(8<length (memory (machine rframe) arraydef_0__meta))%nat) by (rewrite Hrmeta;unfold started;rewrite store_meta_length;lia).
  set (final:=SchemaClass.result (machine rframe) (length classes) (1,meta_value (machine rframe) 0)).
  assert (Hdecode:ClassStorage.decode next (1,meta_value (machine rframe) 0)=
    Some (Schemata.shifted_class depth (VirtualClasses.abstract (VirtualClasses.core p)))).
  { unfold ClassStorage.decode. rewrite Hrmeaning. reflexivity. }
  assert (Hfinalmeta0:meta_value final 0=Z.of_nat (length classes)).
  { apply (proj1 (SchemaClass.result_values (machine rframe) (length classes) (1,meta_value (machine rframe) 0) ltac:(lia))). }
  assert (Hrgood:ClassLookup.wellformed (machine rframe)).
  { unfold ClassLookup.wellformed in *. rewrite (proj1 Hrframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate).
    unfold started. now rewrite store_meta_other by discriminate. }
  assert (Hfinalgood:ClassLookup.wellformed final).
  { apply SchemaClass.append_wellformed with (fs:=next);[exact Hrclasses|exact Hrgood|exact Hrword]. }
  assert (Hvalid:meta_value final 18=meta_value s 18).
  { unfold final. rewrite SchemaClass.result_meta_other by lia.
    rewrite (proj1 (proj2 Hrframe)) by (unfold RenameStorage.Cells.protected;repeat split;discriminate).
    unfold started. now rewrite meta_store_other by lia. }
  exists final,next. split.
  - apply (generated_abstract_helper s bs ns cls root depth (machine rframe) (length classes) observations);try assumption;
      [lia|exact (proj1 Hrclasses)|lia].
  - split;[now apply SchemaClass.result_arena|].
    split;[apply SchemaClass.append_represents;[lia|exact Hrclasses|exact Hdecode]|].
    split;[exact Hfinalmeta0|]. split;[unfold final;rewrite SchemaClass.result_meta_other by lia;exact Hrerror|].
    split;[exact Hrprefix|]. split;[now apply SchemaClass.result_topology|]. split;[exact Hrgrowth|].
    split;[rewrite length_app;cbn [length];lia|].
    destruct (proj2 (proj2 Hrframe)) as [Hinput Houtput]. split;[exact Hinput|]. split;[exact Houtput|]. split;assumption.
Qed.

Theorem generated_abstract (f:SchemaEvaluation.Frame) width remaining outer_remaining a cls root p d bound fs classes rho formula_reserve class_reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=Z.of_nat d -> (0<d)%nat ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error (memory (machine f) arraydef_0__classes) cls=Some (1,Z.of_nat root) -> nth_error fs root=Some p ->
 rho a=VirtualClasses.abstract (VirtualClasses.core p) -> nth_error fs 0=Some SetTheory.falsity ->
 Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
 Z.of_nat bound+Z.of_nat d<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
 Z.of_nat (length fs+S root*S root+formula_reserve)<=9223372036854775807 ->
 Z.of_nat (length classes+S class_reserve)<=maximum ->
 exists final next,execLocalObserved (SchemaEvaluation.meta_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\ NativeRepresentation.canonical_arena final next /\
 ClassStorage.represents final next (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) /\
 SchemaEvaluation.meaning next (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) rho d
   (Protocol.CE (Schemata.metavariable a)) (meta_value final 0) /\ meta_value final 8=0 /\
 (exists extra,next=fs++extra) /\ FormulaTopology.ordered final (length next) /\
 Z.of_nat (length next+formula_reserve)<=9223372036854775807 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)])+class_reserve)<=maximum /\ ClassLookup.wellformed final /\ meta_value final 18=meta_value (machine f) 18.
Proof.
 intros Ha Hlookup Hd Hpositive Hmeta Hsip Harena Htop Herror Hclasses Hgood Hraw Hp Hrho Hfalse Hfuel Hbound Hindices Hheight Hbudget Hclassbudget.
 destruct (shift_abstract_refines (machine f) (fun _=>false)
   (arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)) fs classes cls root p d bound class_reserve observations
   Hmeta Hsip Harena Htop Herror Hclasses Hgood Hraw Hp Hfalse
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same)
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_same;exact Hd) Hpositive Hfuel Hbound Hindices Hheight ltac:(lia) Hclassbudget)
 as [final [next [Hrun [Hnext [Hnextclasses [Hindex [Hflag [Hprefix [Hnexttop [Hgrowth [Hclassroom [Hinput [Houtput [Hnextgood Hvalid]]]]]]]]]]]]]].
 exists final,next. split;[eapply generated_helper;eassumption|]. split;[exact Hnext|].
 assert (Hmeaning:Schemata.instantiate_class rho d (Schemata.metavariable a)=Schemata.shifted_class d (VirtualClasses.abstract (VirtualClasses.core p))).
 { cbn [Schemata.instantiate_class]. now rewrite Hrho. }
 rewrite Hmeaning. split;[exact Hnextclasses|]. split.
 - unfold SchemaEvaluation.meaning,SchemaEvaluation.class_value. rewrite Hmeaning,Hindex. split;[unfold word;lia|].
   rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag.
 - split;[exact Hflag|]. split;[exact Hprefix|]. split;[exact Hnexttop|]. split;[lia|]. split;[exact Hclassroom|]. split;assumption.
Qed.

Theorem generated_meta_abstract (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar key cls root p depth bound fs classes rho formula_reserve class_reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (0,Z.of_nat a,b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=Z.of_nat depth -> (0<depth)%nat ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error (memory (machine f) arraydef_0__classes) cls=Some (1,Z.of_nat root) -> nth_error fs root=Some p ->
 rho a=VirtualClasses.abstract (VirtualClasses.core p) -> nth_error fs 0=Some SetTheory.falsity ->
 Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> RenameMemoIndexBounds.formula_bound bound p ->
 Z.of_nat bound+Z.of_nat depth<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
 Z.of_nat (length fs+S root*S root+formula_reserve)<=9223372036854775807 ->
 Z.of_nat (length classes+S class_reserve)<=maximum ->
 exists final next,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final next (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) rho depth (Protocol.CE (Schemata.metavariable a)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\
 ClassStorage.represents (machine final) next (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) /\
 meta_value (machine final) 8=0 /\ (exists extra,next=fs++extra) /\ FormulaTopology.ordered (machine final) (length next) /\
 Z.of_nat (length next+formula_reserve)<=9223372036854775807 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)])+class_reserve)<=maximum /\ ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hkey Hbound Harg Hdepth Hpositive Hmeta Hsip Harena Htop Herror Hclasses Hgood Hclass Hp Hrho Hfalse Hfuel Hindices Hindexroom Hheight Hbudget Hclassbudget.
 set (parsed:=descriptor_frame f (0,Z.of_nat a,b,c,rawd,ty,ar)).
 destruct (generated_abstract parsed width remaining outer_remaining a cls root p depth bound fs classes rho formula_reserve class_reserve observations
   (descriptor_a _ _ _ _ _ _ _ _) Harg Hdepth Hpositive Hmeta Hsip Harena Htop Herror Hclasses Hgood Hclass Hp Hrho Hfalse Hfuel Hindices Hindexroom Hheight Hbudget Hclassbudget)
 as (built & next & Hrun & Hnext & Hnextclasses & Hmeaning & Hflag & Hprefix & Hnexttop & Hroom & Hclassroom & Hnextgood & Hvalid).
 set (middle:=setMachine parsed built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\
   post f (output middle key) next (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) rho depth (Protocol.CE (Schemata.metavariable a)) key).
 { eapply (finish meta);try eassumption.
   - unfold middle. exact (descriptor_kind f 0 (Z.of_nat a) b c rawd ty ar).
   - reflexivity.
   - lia.
 }
 exists (output middle key),next. destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[now apply written_topology|]. split;[exact Hroom|]. split;[exact Hclassroom|]. split;[unfold ClassLookup.wellformed;now rewrite written_other by discriminate|now rewrite written_meta].
Qed.

Theorem generated_meta_zero (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar key cls fs classes rho observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (0,Z.of_nat a,b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=0 ->
 (8<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes cls=Some (rho a) -> word (Z.of_nat cls) ->
 exists final,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final fs classes rho 0 (Protocol.CE (Schemata.metavariable a)) key /\
 ClassStorage.represents (machine final) fs classes /\
 NativeRepresentation.canonical_arena (machine final) fs /\ FormulaTopology.ordered (machine final) (length fs) /\
 meta_value (machine final) 8=0 /\ meta_value (machine final) 18=meta_value (machine f) 18 /\ ClassLookup.wellformed (machine final).
Proof.
 intros Hnode Hraw Hkey Hbound Harg Hdepth Hmeta Harena Htop Herror Hclasses Hgood Hcls Hword.
 set (parsed:=descriptor_frame f (0,Z.of_nat a,b,c,rawd,ty,ar)).
 destruct (SchemaEvaluationMeta.generated_zero parsed width remaining outer_remaining a cls fs classes rho observations
   (descriptor_a _ _ _ _ _ _ _ _) Harg Hdepth Hmeta Hclasses Hgood Hcls Hword)
 as (built & Hrun & Hnextclasses & Hmeaning).
 assert (Hshift:execObserved (funcdef_0__schemaShiftClass (fun _=>false)
   (SchemaEvaluationMeta.arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)))
   (machine parsed,observations)=Some (tt,(SchemaShiftClass.started (machine f) cls,observations))).
 { apply (SchemaShiftClass.generated_zero (machine f) _ _ cls observations Hmeta).
   - unfold SchemaEvaluationMeta.arguments. rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same.
   - unfold SchemaEvaluationMeta.arguments. rewrite RenameMemoControl.updated_same. exact Hdepth. }
 pose proof (SchemaEvaluationMeta.generated_helper parsed width remaining outer_remaining a (Z.of_nat cls)
   (SchemaShiftClass.started (machine f) cls) observations (descriptor_a _ _ _ _ _ _ _ _) Harg Hshift) as Hspecified.
 rewrite Hrun in Hspecified. injection Hspecified as Hspecified.
 assert (Hbuilt:built=SchemaShiftClass.started (machine f) cls) by exact Hspecified.
 set (middle:=setMachine parsed built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) fs classes rho 0 (Protocol.CE (Schemata.metavariable a)) key).
 { eapply (finish meta);try eassumption.
   - unfold middle. exact (descriptor_kind f 0 (Z.of_nat a) b c rawd ty ar).
   - reflexivity.
   - lia.
 }
 exists (output middle key). destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. rewrite Hbuilt in Hnextclasses|-*. split;[now apply written_classes|].
 split.
 - apply written_arena. apply (ArenaFrame.storage_arena (machine f));[apply SchemaShiftClass.started_storage|exact Harena].
 - split.
   + apply written_topology. apply (FormulaTopology.same (machine f));[exact Htop|].
     intros parent Hparent. unfold HashTableInvariant.tuple_at,SchemaShiftClass.started. now rewrite store_meta_other by discriminate.
   + rewrite !written_meta. unfold SchemaShiftClass.started. rewrite !meta_store_other by lia. split;[exact Herror|]. split;[reflexivity|].
     unfold ClassLookup.wellformed. rewrite written_other by discriminate.
     unfold SchemaShiftClass.started. now rewrite store_meta_other by discriminate.
Qed.

Theorem generated_meta_set (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar key cls variable depth fs classes rho reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (0,Z.of_nat a,b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=Z.of_nat depth -> (0<depth)%nat ->
 (8<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error (memory (machine f) arraydef_0__classes) cls=Some (0,Z.of_nat variable) -> rho a=VirtualClasses.set variable ->
 Z.of_nat variable+Z.of_nat depth<=maximum -> Z.of_nat (length classes+S reserve)<=maximum ->
 exists final,execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final fs (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) rho depth (Protocol.CE (Schemata.metavariable a)) key /\
 ClassStorage.represents (machine final) fs (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) /\
 NativeRepresentation.canonical_arena (machine final) fs /\ FormulaTopology.ordered (machine final) (length fs) /\
 meta_value (machine final) 18=meta_value (machine f) 18 /\ meta_value (machine final) 8=meta_value (machine f) 8 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)])+reserve)<=maximum /\ ClassLookup.wellformed (machine final).
Proof.
 intros Hnode Hraw Hkey Hbound Harg Hdepth Hpositive Hmeta Harena Htop Hclasses Hgood Hclass Hrho Hsum Hbudget.
 set (parsed:=descriptor_frame f (0,Z.of_nat a,b,c,rawd,ty,ar)).
 destruct (SchemaEvaluationMeta.generated_set parsed width remaining outer_remaining a cls variable depth fs classes rho reserve observations
   (descriptor_a _ _ _ _ _ _ _ _) Harg Hdepth Hpositive Hmeta Hclasses Hclass Hrho Hsum Hbudget)
 as (built & Hrun & Hnextclasses & Hmeaning & Hflag & Hroom).
 assert (Hshift:execObserved (funcdef_0__schemaShiftClass (fun _=>false)
   (SchemaEvaluationMeta.arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)))
   (machine parsed,observations)=Some (tt,(SchemaClass.result (SchemaShiftClass.started (machine f) cls)
     (length classes) (0,Z.of_nat (variable+depth)),observations))).
 { apply (SchemaShiftClass.generated_set (machine f) _ _ cls variable depth (length classes) observations Hmeta Hclass).
   - unfold SchemaEvaluationMeta.arguments. rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same.
   - unfold SchemaEvaluationMeta.arguments. rewrite RenameMemoControl.updated_same. exact Hdepth.
   - exact Hpositive.
   - exact Hsum.
   - exact (proj1 Hclasses).
   - lia. }
 pose proof (SchemaEvaluationMeta.generated_helper parsed width remaining outer_remaining a (Z.of_nat cls)
   (SchemaClass.result (SchemaShiftClass.started (machine f) cls) (length classes) (0,Z.of_nat (variable+depth)))
   observations (descriptor_a _ _ _ _ _ _ _ _) Harg Hshift) as Hspecified.
 rewrite Hrun in Hspecified. injection Hspecified as Hspecified.
 assert (Hbuilt:built=SchemaClass.result (SchemaShiftClass.started (machine f) cls) (length classes) (0,Z.of_nat (variable+depth)))
   by exact Hspecified.
 set (middle:=setMachine parsed built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\
   post f (output middle key) fs (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) rho depth (Protocol.CE (Schemata.metavariable a)) key).
 { eapply (finish meta);try eassumption.
   - unfold middle. exact (descriptor_kind f 0 (Z.of_nat a) b c rawd ty ar).
   - reflexivity.
   - lia.
 }
 exists (output middle key). destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. rewrite Hbuilt in Hnextclasses,Hflag|-*. split;[now apply written_classes|].
 split.
 - apply written_arena. apply SchemaClass.result_arena.
   apply (ArenaFrame.storage_arena (machine f));[apply SchemaShiftClass.started_storage|exact Harena].
 - split.
   + apply written_topology. apply SchemaClass.result_topology.
     apply (FormulaTopology.same (machine f));[exact Htop|]. intros parent Hparent.
     unfold HashTableInvariant.tuple_at,SchemaShiftClass.started. now rewrite store_meta_other by discriminate.
   + split.
     * rewrite written_meta,SchemaClass.result_meta_other by lia. unfold SchemaShiftClass.started. now rewrite meta_store_other by lia.
     * split;[now rewrite written_meta|]. split;[exact Hroom|].
       unfold ClassLookup.wellformed. rewrite written_other by discriminate. fold (ClassLookup.wellformed (SchemaClass.result (SchemaShiftClass.started (machine f) cls) (length classes) (0,Z.of_nat (variable+depth)))).
       apply (SchemaClass.append_wellformed _ fs classes).
       -- now apply SchemaShiftClass.started_classes.
       -- unfold ClassLookup.wellformed,SchemaShiftClass.started. now rewrite store_meta_other by discriminate.
       -- cbn [snd]. unfold word. rewrite Nat2Z.inj_add. lia.
Qed.

Theorem generated_abstraction (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key childKey id fs classes rho p reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (3,Z.of_nat a,b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 childKey=(a*stride+depth+1)%nat -> Z.of_nat childKey<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) childKey=Some id ->
 (8<length (memory (machine f) arraydef_0__meta))%nat -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 meta_value (machine f) 8=0 -> FormulaTopology.ordered (machine f) (length fs) ->
 SchemaEvaluation.formula_value fs id (Schemata.instantiate_formula rho (S depth) p) ->
 Z.of_nat (length classes+S reserve)<=maximum ->
 exists final,
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,observations)) /\
 post f final fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth (Protocol.CE (Schemata.template_abstract p)) key /\
 NativeRepresentation.canonical_arena (machine final) fs /\
 ClassStorage.represents (machine final) fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) /\
 meta_value (machine final) 8=0 /\ FormulaTopology.ordered (machine final) (length fs) /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)])+reserve)<=maximum /\ ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hchildkey Hchildword Hchild Hmeta Hbound Harena Hclasses Hgood Herror Htop Hmeaning Hbudget.
 set (parsed:=descriptor_frame f (3,Z.of_nat a,b,c,rawd,ty,ar)).
 set (built:=SchemaClass.result (machine f) (length classes) (1,id)).
 set (middle:=setMachine parsed built).
 assert (Hdecode:ClassStorage.decode fs (1,id)=Some (Schemata.instantiate_class rho depth (Schemata.template_abstract p))).
 { cbn [ClassStorage.decode Schemata.instantiate_class]. now rewrite (proj2 Hmeaning). }
 destruct (SchemaClass.generated_refines (machine f) (fun _=>false) (SchemaClass.arguments 1 id) fs classes 1 id
   (Schemata.instantiate_class rho depth (Schemata.template_abstract p)) reserve observations Hmeta Hclasses eq_refl eq_refl Hdecode Hbudget)
 as [Hhelper [Hnext [Hindex Hroom]]].
 assert (Hrun:execLocalObserved (dropWithinLoop (selected abstraction width remaining outer_remaining)) (parsed,observations)=Some (KeepGoing,(middle,observations))).
 { change (execLocalObserved (SchemaEvaluation.abstract_handler width remaining outer_remaining) (parsed,observations)=Some (KeepGoing,(middle,observations))).
   apply (SchemaEvaluation.generated_abstract_helper parsed width remaining outer_remaining a stride depth childKey id built observations
     (descriptor_a _ _ _ _ _ _ _ _) ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hchildkey Hchildword Hchild Hhelper). }
 assert (Hresult:SchemaEvaluation.meaning fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth
   (Protocol.CE (Schemata.template_abstract p)) (meta_value (machine middle) 0)).
 { change (SchemaEvaluation.class_value (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) (meta_value built 0)
     (Schemata.instantiate_class rho depth (Schemata.template_abstract p))).
   unfold SchemaEvaluation.class_value.
   change (meta_value built 0=Z.of_nat (length classes)) in Hindex. rewrite Hindex. split;[unfold word;lia|].
   rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag. }
 destruct (finish abstraction f middle width remaining outer_remaining node 3 (Z.of_nat a) b c rawd ty ar key fs
   (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth (Protocol.CE (Schemata.template_abstract p)) observations
   Hnode Hraw ltac:(unfold middle;cbn [nums setMachine];apply descriptor_kind) eq_refl Hrun ltac:(lia)
   ltac:(unfold middle;cbn [nums setMachine];unfold parsed;now rewrite descriptor_key) Hbound Hresult) as [Hexec Hpost].
 exists (output middle key). split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split.
 - apply written_arena. now apply SchemaClass.result_arena.
 - split;[exact (written_classes _ _ _ _ _ Hnext)|]. split.
   + rewrite written_meta. unfold built. now rewrite SchemaClass.result_meta_other by lia.
   + split;[apply written_topology;now apply SchemaClass.result_topology|]. split;[exact Hroom|]. split.
     * unfold ClassLookup.wellformed. rewrite written_other by discriminate. fold (ClassLookup.wellformed built).
       unfold built. apply (SchemaClass.append_wellformed _ fs classes);[exact Hclasses|exact Hgood|exact (proj1 Hmeaning)].
     * rewrite written_meta. unfold built. now rewrite SchemaClass.result_meta_other by lia.
Qed.

End SchemaEvaluationMetaInvariant.
