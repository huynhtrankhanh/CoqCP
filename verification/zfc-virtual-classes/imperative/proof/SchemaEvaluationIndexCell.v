From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaEvaluationDependencies SchemaEvaluationResources
 SchemaEvaluationInvariant SchemaPair SchemaPairStep SchemaPairSemantic SchemaEvaluationAbstractSemantic SchemaGraph SchemaRepresentation SchemaMetadata
 Representation ClassStorage ClassLookup FormulaTopology ArenaFrame RenameMemoControl RenameMemoLengths HashTable AxiomTaggedInvariant InternInvariant SchemaEvaluationMetaInvariant SchemaEvaluationFamilyInvariant SchemaEvaluationPreservation SchemaEvaluationCell RenameMemoBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoClassEqual RenameMemoClassMember RenameMemoResourceBounds.
From NativeProof Require Import SchemaEvaluationBoundedCell SchemaEvaluationIndexBounds SchemaEvaluationIndexHelpers SchemaEvaluationIndexClassEqual SchemaEvaluationIndexClassMember SchemaEvaluationIndexShiftClass SchemaEvaluationControl SchemaEvaluationFrames RenameMemoInput SchemaEvaluationIndexAxiomTagged SchemaEvaluationAxiom SchemaEvaluationAxiomSemantic AxiomStorage SchemaShiftClass SchemaEvaluationMetaInvariant SchemaEvaluationBinaryMP SchemaEvaluationMeta SchemaShiftClass SchemaClass RenameStorage InternReserve FormulaCircuit FormulaEncoding SemanticFrames.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexCell.
Import IndexExecution SipHashExecution ObservedLocal SchemaEvaluationDependencies SchemaEvaluationCell SchemaEvaluation.
Definition bounded native (fs:list SetTheory.formula) classes bound :=
 SchemaEvaluationIndexBounds.raw_arena native (length fs) bound /\ SchemaEvaluationIndexBounds.classes bound classes.
Definition successor kind bound depth b c d := (match kind with
 | 0=>bound+depth | 4=>bound+2 | 5=>2*bound+3 | 8=>bound+b+c+d+4 | _=>bound end)%nat.
Definition ready := SchemaEvaluationBoundedCell.ready.
Lemma bounded_mono native fs classes lower upper : (lower<=upper)%nat ->
 bounded native fs classes lower -> bounded native fs classes upper.
Proof.
 intros Hle [Hraw Hclasses]. split.
 - exact (SchemaEvaluationIndexBounds.raw_arena_mono native (length fs) lower upper Hle Hraw).
 - exact (SchemaEvaluationIndexShiftClass.classes_mono lower upper classes Hle Hclasses).
Qed.
Lemma class_lookup bound classes index cls : SchemaEvaluationIndexBounds.classes bound classes ->
 nth_error classes index=Some cls -> SchemaEvaluationIndexBounds.class_bound bound cls.
Proof.
 intros Hclasses. induction Hclasses as [|head tail Hhead Htail IH] in index|-*;[destruct index;discriminate|].
 destruct index as [|index];[intro H;injection H as <-;exact Hhead|apply IH].
Qed.
Lemma written_raw native key value count bound : SchemaEvaluationIndexBounds.raw_arena native count bound ->
 SchemaEvaluationIndexBounds.raw_arena (SchemaPairStep.written native key value) count bound.
Proof. intro H. eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply SchemaPairStep.written_other;discriminate|exact H]. Qed.
Theorem binary_equal (f:Frame) width remaining outer_remaining a b stride d ka kb ia ib fs classes rho ta tb reserve bound observations :
 nums f vardef_0__schemaInstance_kind=4 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho d ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho d tb) ->
 RenameMemoClassEqual.ready (machine f) fs ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) ->
 Z.of_nat (length fs+RenameMemoClassEqual.work (machine f) ia ib
   (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho d ta) ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho d tb) ->
 Z.of_nat bound+2<=maximum ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+2) /\
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f (Z.of_nat ia) (Z.of_nat ib)) final,observations)) /\
 NativeRepresentation.canonical_arena final next /\
 meaning next classes rho d (Protocol.FE (Schemata.template_equal ta tb)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame (machine f) final /\
 ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
 Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget Hraw HclassA HclassB Hindices.
 destruct (SchemaEvaluationIndexClassEqual.generated_refines (machine f) (fun _=>false)
   (update (update (fun _=>0) vardef_0__classEqual_a (Z.of_nat ia)) vardef_0__classEqual_b (Z.of_nat ib))
   fs classes ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) reserve bound observations
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib ltac:(rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same) ltac:(apply RenameMemoControl.updated_same) Hready Hbudget Hraw HclassA HclassB Hindices)
 as (final & next & index & HrawNext & Hrun & Hnext & Hindex & Hindexword & Hmeaning & Hprefix & Hflag & Hframe & Hnextclasses & Hnextgood & Hroom & Hnexttop & Hgrowth).
 exists final,next. split;[exact HrawNext|]. split.
 - eapply generated_binary_equal_helper;eassumption.
 - split;[exact Hnext|]. split.
   + change (formula_value next (meta_value final 0)
       (VirtualClasses.erase (VirtualClasses.class_equal (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)))).
     rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + exact (conj Hprefix (conj Hflag (conj Hframe (conj Hnextclasses (conj Hnextgood (conj Hroom Hnexttop)))))).
Qed.
Theorem binary_member (f:Frame) width remaining outer_remaining a b stride d ka kb ia ib fs classes rho ta tb reserve bound observations :
 nums f vardef_0__schemaInstance_kind=5 ->
 nums f vardef_0__schemaInstance_a=Z.of_nat a -> nums f vardef_0__schemaInstance_b=Z.of_nat b ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> depth width remaining=Z.of_nat d ->
 ka=(a*stride+d)%nat -> kb=(b*stride+d)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho d ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho d tb) ->
 RenameMemoClassMember.ready (machine f) fs ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) ->
 Z.of_nat (length fs+RenameMemoClassMember.work (machine f) ia ib
   (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho d ta) ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho d tb) ->
 2*Z.of_nat bound+3<=maximum ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena final (length next) (2*bound+3) /\
 execLocalObserved (binary_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (binary_frame f (Z.of_nat ia) (Z.of_nat ib)) final,observations)) /\
 NativeRepresentation.canonical_arena final next /\
 meaning next classes rho d (Protocol.FE (Schemata.template_member ta tb)) (meta_value final 0) /\
 (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ RenameStorage.logical_frame (machine f) final /\
 ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\
 Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\ FormulaTopology.ordered final (length next).
Proof.
 intros Hkind Ha Hb Hstride Hd Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget Hraw HclassA HclassB Hindices.
 destruct (SchemaEvaluationIndexClassMember.generated_refines (machine f) (fun _=>false)
   (update (update (fun _=>0) vardef_0__classMember_a (Z.of_nat ia)) vardef_0__classMember_b (Z.of_nat ib))
   fs classes ia ib (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb) reserve bound observations
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib ltac:(rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same) ltac:(apply RenameMemoControl.updated_same) Hready Hbudget Hraw HclassA HclassB Hindices)
 as (final & next & index & HrawNext & Hrun & Hnext & Hindex & Hindexword & Hmeaning & Hprefix & Hflag & Hframe & Hnextclasses & Hnextgood & Hroom & Hnexttop & Hgrowth).
 exists final,next. split;[exact HrawNext|]. split.
 - eapply generated_binary_member_helper;eassumption.
 - split;[exact Hnext|]. split.
   + change (formula_value next (meta_value final 0)
       (VirtualClasses.erase (VirtualClasses.class_member (Schemata.instantiate_class rho d ta) (Schemata.instantiate_class rho d tb)))).
     rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + exact (conj Hprefix (conj Hflag (conj Hframe (conj Hnextclasses (conj Hnextgood (conj Hroom Hnexttop)))))).
Qed.
Import SchemaPair SchemaPairStep SchemaPairSemantic SchemaEvaluationMeta SchemaShiftClass.
Theorem cell_equal (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb ia ib fs classes rho ta tb reserve bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (4,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho depth ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho depth tb) ->
 RenameMemoClassEqual.ready (machine f) fs ia ib (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb) ->
 Z.of_nat (length fs+RenameMemoClassEqual.work (machine f) ia ib
   (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho depth ta) ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho depth tb) ->
 Z.of_nat bound+2<=maximum ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) (bound+2) /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ post f final next classes rho depth (Protocol.FE (Schemata.template_equal ta tb)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ meta_value (machine final) 8=0 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget HrawInitial HclassA HclassB Hindices.
 set (parsed:=descriptor_frame f (4,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 destruct (binary_equal parsed width remaining outer_remaining a b stride depth ka kb ia ib fs classes rho ta tb reserve bound observations
   (descriptor_kind _ _ _ _ _ _ _ _) Ha Hb ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hka Hkb Hworda Hwordb Hlookupa Hlookupb
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget HrawInitial HclassA HclassB Hindices)
 as (built & next & HrawNext & Hrun & Hnext & Hmeaning & Hprefix & Hflag & Hframe & Hnextclasses & Hnextgood & Hroom & Hnexttop).
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed (Z.of_nat ia) (Z.of_nat ib)) built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) next classes rho depth (Protocol.FE (Schemata.template_equal ta tb)) key).
 { eapply (finish binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 4 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
   - lia.
 }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate). exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));unfold RenameStorage.Cells.protected;repeat split;discriminate. }
 exists (output middle key),next. split.
 { unfold output,middle. cbn [machine setMachine]. exact (written_raw built key (meta_value built 0) (length next) _ HrawNext). }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now apply written_topology|]. split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[exact Hroom|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem cell_member (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb ia ib fs classes rho ta tb reserve bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (5,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat ia) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some (Z.of_nat ib) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes ia=Some (Schemata.instantiate_class rho depth ta) ->
 nth_error classes ib=Some (Schemata.instantiate_class rho depth tb) ->
 RenameMemoClassMember.ready (machine f) fs ia ib (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb) ->
 Z.of_nat (length fs+RenameMemoClassMember.work (machine f) ia ib
   (Schemata.instantiate_class rho depth ta) (Schemata.instantiate_class rho depth tb)+reserve)<=RenameMemoResourceBounds.doubling_limit ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho depth ta) ->
 SchemaEvaluationIndexBounds.class_bound bound (Schemata.instantiate_class rho depth tb) ->
 2*Z.of_nat bound+3<=maximum ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) (2*bound+3) /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ post f final next classes rho depth (Protocol.FE (Schemata.template_member ta tb)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ meta_value (machine final) 8=0 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=RenameMemoResourceBounds.doubling_limit /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget HrawInitial HclassA HclassB Hindices.
 set (parsed:=descriptor_frame f (5,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 destruct (binary_member parsed width remaining outer_remaining a b stride depth ka kb ia ib fs classes rho ta tb reserve bound observations
   (descriptor_kind _ _ _ _ _ _ _ _) Ha Hb ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hka Hkb Hworda Hwordb Hlookupa Hlookupb
   Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hgood Hia Hib Hready Hbudget HrawInitial HclassA HclassB Hindices)
 as (built & next & HrawNext & Hrun & Hnext & Hmeaning & Hprefix & Hflag & Hframe & Hnextclasses & Hnextgood & Hroom & Hnexttop).
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed (Z.of_nat ia) (Z.of_nat ib)) built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) next classes rho depth (Protocol.FE (Schemata.template_member ta tb)) key).
 { eapply (finish binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 5 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
   - lia.
 }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate). exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));unfold RenameStorage.Cells.protected;repeat split;discriminate. }
 exists (output middle key),next. split.
 { unfold output,middle. cbn [machine setMachine]. exact (written_raw built key (meta_value built 0) (length next) _ HrawNext). }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now apply written_topology|]. split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[exact Hroom|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem cell_imp (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb va vb fs classes rho p q reserve bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (6,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some va ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 (0<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 meta_value (machine f) 8=0 -> ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 SchemaEvaluation.formula_value fs va (Schemata.instantiate_formula rho depth p) ->
 SchemaEvaluation.formula_value fs vb (Schemata.instantiate_formula rho depth q) ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ post f final next classes rho depth (Protocol.FE (Schemata.template_imp p q)) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ meta_value (machine final) 8=0 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807 /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena Htop Herror Hclasses Hgood [Hleft Hpleft] [Hright Hpright] Hbudget HrawInitial.
 set (parsed:=descriptor_frame f (6,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hnormal:FormulaEncoding.normal (3,va,vb)) by (right;left;auto).
 assert (Hdecode:FormulaEncoding.decode fs (3,va,vb)=Some (SetTheory.implies (Schemata.instantiate_formula rho depth p) (Schemata.instantiate_formula rho depth q))).
 { cbn [FormulaEncoding.decode]. now rewrite Hpleft,Hpright. }
 destruct (SchemaEvaluationIndexBounds.generated_intern (machine f) (fun _=>false) (FormulaCircuit.arguments 3 va vb) fs _ reserve bound observations Harena Herror Hbudget HrawInitial
   ltac:(change (RenameMemoInput.raw_bound bound (3,va,vb));intros [H|H];discriminate) Hnormal Hdecode)
 as (built & next & index & Hnative & Hframe & Hnext & Hflag & Hindex & Hindexword & Hresult & Hprefix & Hroom & HrawNext).
 assert (Hrun:execLocalObserved (SchemaEvaluation.binary_handler width remaining outer_remaining) (parsed,observations)=
   Some (KeepGoing,(setMachine (SchemaEvaluation.binary_frame parsed va vb) built,observations))).
 { eapply SchemaEvaluation.generated_binary_imp_helper;try eassumption;first [apply descriptor_kind|unfold parsed;now rewrite descriptor_width]. }
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed va vb) built).
 assert (Hmeaning:SchemaEvaluation.meaning next classes rho depth (Protocol.FE (Schemata.template_imp p q)) (meta_value (machine middle) 0)).
 { change (SchemaEvaluation.formula_value next (meta_value built 0) (SetTheory.implies (Schemata.instantiate_formula rho depth p) (Schemata.instantiate_formula rho depth q))).
   rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id. }
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\ post f (output middle key) next classes rho depth (Protocol.FE (Schemata.template_imp p q)) key).
 { eapply (finish binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 6 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
 }
 assert (Hnextclasses:ClassStorage.represents built next classes).
 { destruct Hprefix as [extra Hprefix]. rewrite Hprefix. destruct Hframe as [Harrays [Hcells Hio]].
   eapply SemanticFrames.classes_extend;[apply Hcells;lia|apply Harrays;discriminate|exact Hclasses]. }
 assert (Hnexttop:FormulaTopology.ordered built (length next)).
 { destruct (FormulaTopology.generated_intern_preserves (machine f) (fun _=>false) (FormulaCircuit.arguments 3 va vb) fs _ Harena Htop Herror ltac:(lia) Hdecode)
   as (other & Hplain & Hotherflag & Hothertop).
   pose proof (f_equal (fun run=>option_map (fun response=>(fst response,fst (snd response))) run) Hnative) as Herase.
   rewrite execObserved_erases in Herase. cbn [option_map fst snd] in Herase. rewrite Herase in Hplain. injection Hplain as <-.
   destruct Hnext as [[Hready [Hcount Hrest]] Hnextmeaning]. now rewrite Hcount,Nat2Z.id in Hothertop. }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by discriminate. exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));lia. }
 exists (output middle key),next. split.
 { unfold SchemaPairSemantic.output,middle. cbn [machine setMachine]. exact (written_raw built key (meta_value built 0) (length next) bound HrawNext). }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now apply written_topology|]. split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[exact Hroom|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Theorem cell_universal (f:Frame) width remaining outer_remaining node kind a b c rawd ty ar stride depth key childKey id
 fs classes rho p expression reserve bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (kind,Z.of_nat a,b,c,rawd,ty,ar) ->
 (kind=7 \/ kind=10) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 childKey=(a*stride+depth+1)%nat -> Z.of_nat childKey<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) childKey=Some id ->
 (0<length (memory (machine f) arraydef_0__meta))%nat -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 SchemaEvaluation.formula_value fs id p ->
 (forall next value,SchemaEvaluation.formula_value next value (SetTheory.all p) ->
   SchemaEvaluation.meaning next classes rho depth expression value) ->
 Z.of_nat (length fs+S reserve)<=9223372036854775807 ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ SchemaPairSemantic.post f final next classes rho depth expression key /\
 NativeRepresentation.canonical_arena (machine final) next /\ ClassStorage.represents (machine final) next classes /\
 FormulaTopology.ordered (machine final) (length next) /\ ClassLookup.wellformed (machine final) /\
 meta_value (machine final) 8=0 /\ meta_value (machine final) 18=meta_value (machine f) 18 /\
 (exists extra,next=fs++extra) /\ Z.of_nat (length next+reserve)<=9223372036854775807.
Proof.
 intros Hnode Hraw Hkind Hstride Hdepth Hkey Hchildkey Hchildword Hchild Hmeta Hbound Harena Htop Herror Hclasses Hgood [Hid Hp] Htarget Hbudget HrawInitial.
 set (parsed:=SchemaPairStep.descriptor_frame f (kind,Z.of_nat a,b,c,rawd,ty,ar)).
 assert (Hnormal:FormulaEncoding.normal (4,id,0)) by (right;right;auto).
 assert (Hdecode:FormulaEncoding.decode fs (4,id,0)=Some (SetTheory.all p)).
 { cbn [FormulaEncoding.decode]. now rewrite Hp. }
 destruct (SchemaEvaluationIndexBounds.generated_intern (machine f) (fun _=>false) (FormulaCircuit.arguments 4 id 0) fs _ reserve bound observations
   Harena Herror Hbudget HrawInitial ltac:(change (RenameMemoInput.raw_bound bound (4,id,0));intros [H|H];discriminate) Hnormal Hdecode)
 as (built & next & index & Hnative & Hframe & Hnext & Hflag & Hindex & Hindexword & Hresult & Hprefix & Hroom & HrawNext).
 assert (Hrun:execLocalObserved (SchemaEvaluation.all_handler width remaining outer_remaining) (parsed,observations)=
   Some (KeepGoing,(setMachine parsed built,observations))).
 { eapply SchemaEvaluation.generated_all_helper;try eassumption.
   - apply SchemaPairSemantic.descriptor_a. }
 set (middle:=setMachine parsed built).
 assert (Hmeaning:SchemaEvaluation.meaning next classes rho depth expression (meta_value built 0)).
 { apply Htarget. unfold SchemaEvaluation.formula_value. rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id. }
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(SchemaPairSemantic.output middle key,observations)) /\
   SchemaPairSemantic.post f (SchemaPairSemantic.output middle key) next classes rho depth expression key).
 { eapply (SchemaPairSemantic.finish SchemaPair.universal);try eassumption.
   - unfold middle. exact (SchemaPairStep.descriptor_kind f kind (Z.of_nat a) b c rawd ty ar).
 }
 assert (Hnextclasses:ClassStorage.represents built next classes).
 { destruct Hprefix as [extra Hprefix]. rewrite Hprefix. destruct Hframe as [Harrays [Hcells Hio]].
   eapply SemanticFrames.classes_extend;[apply Hcells;lia|apply Harrays;discriminate|exact Hclasses]. }
 assert (Hnexttop:FormulaTopology.ordered built (length next)).
 { destruct (FormulaTopology.generated_intern_preserves (machine f) (fun _=>false) (FormulaCircuit.arguments 4 id 0) fs _
     Harena Htop Herror ltac:(lia) Hdecode) as (other & Hplain & Hotherflag & Hothertop).
   pose proof (f_equal (fun run=>option_map (fun response=>(fst response,fst (snd response))) run) Hnative) as Herase.
   rewrite execObserved_erases in Herase. cbn [option_map fst snd] in Herase. rewrite Herase in Hplain. injection Hplain as <-.
   destruct Hnext as [[Hready [Hcount Hrest]] Hnextmeaning]. now rewrite Hcount,Nat2Z.id in Hothertop. }
 assert (Hnextgood:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by discriminate. exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18) by (apply (proj1 (proj2 Hframe));lia).
 exists (SchemaPairSemantic.output middle key),next. split.
 { unfold SchemaPairSemantic.output,middle. cbn [machine setMachine]. exact (written_raw built key (meta_value built 0) (length next) bound HrawNext). }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold SchemaPairSemantic.output,middle. cbn [machine setMachine]. split;[now apply SchemaPairStep.written_arena|].
 split;[now apply SchemaPairStep.written_classes|]. split;[now apply SchemaPairStep.written_topology|].
 split;[unfold ClassLookup.wellformed;now rewrite SchemaPairStep.written_other by discriminate|].
 split;[now rewrite SchemaPairStep.written_meta|]. split;[now rewrite SchemaPairStep.written_meta|]. split;assumption.
Qed.
Theorem cell_literal (f:SchemaEvaluation.Frame) width remaining outer_remaining node kind a b c d ty ar key fs classes rho depth expression bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (kind,a,b,c,d,ty,ar) ->
 (kind=1 \/ kind=2 \/ kind=11) ->
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> ClassStorage.represents (machine f) fs classes ->
 FormulaTopology.ordered (machine f) (length fs) -> ClassLookup.wellformed (machine f) ->
 meta_value (machine f) 8=0 -> SchemaEvaluation.meaning fs classes rho depth expression a ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final,SchemaEvaluationIndexBounds.raw_arena (machine final) (length fs) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\ SchemaPairSemantic.post f final fs classes rho depth expression key /\
 NativeRepresentation.canonical_arena (machine final) fs /\ ClassStorage.represents (machine final) fs classes /\
 FormulaTopology.ordered (machine final) (length fs) /\ ClassLookup.wellformed (machine final) /\
 meta_value (machine final) 8=0 /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hkind Hmeta Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning HrawInitial.
 set (parsed:=SchemaPairStep.descriptor_frame f (kind,a,b,c,d,ty,ar)).
 set (middle:=setMachine parsed (store_meta (machine f) 0 a)).
 set (final:=SchemaPairSemantic.output middle key).
 assert (Hrun:execLocalObserved (dropWithinLoop (SchemaPair.selected SchemaPair.literal width remaining outer_remaining))
   (parsed,observations)=Some (KeepGoing,(middle,observations))).
 { unfold middle. change (execLocalObserved (SchemaEvaluation.literal_handler width remaining outer_remaining)
     (parsed,observations)=Some (KeepGoing,(setMachine parsed (store_meta (machine f) 0 a),observations))).
   assert (Ha:nums parsed vardef_0__schemaInstance_a=a) by apply SchemaPairSemantic.descriptor_a.
   rewrite <-(SchemaPairStep.descriptor_machine f (kind,a,b,c,d,ty,ar)),<-Ha.
   apply SchemaEvaluation.generated_literal. unfold parsed. rewrite SchemaPairStep.descriptor_machine. lia. }
 assert (Hresult:SchemaEvaluation.meaning fs classes rho depth expression (meta_value (machine middle) 0)).
 { unfold middle. cbn [machine setMachine]. rewrite meta_store_same by lia. exact Hmeaning. }
 destruct (SchemaPairSemantic.finish SchemaPair.literal f middle width remaining outer_remaining node kind a b c d ty ar key fs classes rho depth expression observations
   Hnode Hraw ltac:(unfold middle;cbn [nums setMachine];apply SchemaPairStep.descriptor_kind) Hkind Hrun ltac:(lia)
   ltac:(unfold middle;cbn [nums setMachine];unfold parsed;now rewrite SchemaPairStep.descriptor_key) Hbound Hresult)
   as [Hexec Hpost].
 exists final. split.
 { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
   unfold final,SchemaPairSemantic.output,middle. cbn [machine setMachine]. rewrite written_other,store_meta_other by discriminate. reflexivity. }
 split;[exact Hexec|]. split;[exact Hpost|]. unfold final,SchemaPairSemantic.output,middle. cbn [machine setMachine].
 split;[apply SchemaPairStep.written_arena;now apply zero_store_arena|].
 split;[apply SchemaPairStep.written_classes;now apply zero_store_classes|].
 split;[apply SchemaPairStep.written_topology;now apply zero_store_topology|].
 split.
 - eapply ClassLookup.transport;[apply SchemaPairStep.written_other;discriminate|now apply zero_store_wellformed].
 - rewrite !SchemaPairStep.written_meta,!meta_store_other by lia. split;[exact Herror|reflexivity].
Qed.
Theorem cell_mp (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key ka kb implication vb fs classes rho ci ca bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (9,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ka=(a*stride+depth)%nat -> kb=(b*stride+depth)%nat -> Z.of_nat ka<=maximum -> Z.of_nat kb<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) ka=Some (Z.of_nat implication) ->
 nth_error (memory (machine f) arraydef_0__schemaValues) kb=Some vb ->
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 meta_value (machine f) 8=0 -> ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 SchemaEvaluation.meaning fs classes rho depth (Protocol.PE ci) (Z.of_nat implication) ->
 SchemaEvaluation.meaning fs classes rho depth (Protocol.PE ca) vb ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final,SchemaEvaluationIndexBounds.raw_arena (machine final) (length fs) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 NativeRepresentation.canonical_arena (machine final) fs /\ ClassStorage.represents (machine final) fs classes /\
 FormulaTopology.ordered (machine final) (length fs) /\ meta_value (machine final) 8=0 /\
 (forall index,index<>key -> SchemaEvaluation.value (machine final) index=SchemaEvaluation.value (machine f) index) /\
 (forall watched,length (memory (machine final) watched)=length (memory (machine f) watched)) /\
 match Schemata.infer rho depth (Schemata.template_mp ci ca) with
 | Some result=>post f final fs classes rho depth (Protocol.PE (Schemata.template_mp ci ca)) key /\
    meta_value (machine final) 18=meta_value (machine f) 18
 | None=>meta_value (machine final) 18=0
 end /\ ClassLookup.wellformed (machine final).
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hbound Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena Htop Herror Hclasses Hgood Hci Hca HrawInitial.
 set (parsed:=descriptor_frame f (9,Z.of_nat a,Z.of_nat b,c,rawd,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat a) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat b).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 destruct (SchemaEvaluationBinaryMP.generated_binary_mp parsed width remaining outer_remaining a b stride depth ka kb implication vb fs classes rho ci ca observations
   (descriptor_kind _ _ _ _ _ _ _ _) Ha Hb ltac:(unfold parsed;now rewrite descriptor_width) Hdepth Hka Hkb Hworda Hwordb Hlookupa Hlookupb Hmeta Harena Hci Hca)
 as (raw & Hrun & Hmeaning).
 set (middle:=setMachine (SchemaEvaluation.binary_frame parsed (Z.of_nat implication) vb)
   (SchemaEvaluation.mp_result (machine f) raw vb)).
 assert (Hmarked:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations))).
 { unfold output. eapply (generated_marked binary);try eassumption.
   - unfold middle. exact (descriptor_kind f 9 (Z.of_nat a) (Z.of_nat b) c rawd ty ar).
   - unfold applies. intuition.
   - unfold middle. cbn [machine setMachine]. rewrite SchemaEvaluationBinaryMP.mp_lengths. lia.
   - unfold middle. cbn [machine setMachine]. now rewrite SchemaEvaluationBinaryMP.mp_arrays by discriminate.
 }
 assert (Hvalues:forall index,index<>key -> SchemaEvaluation.value (machine (output middle key)) index=SchemaEvaluation.value (machine f) index).
 { intros index Hindex. unfold output,middle. cbn [machine setMachine]. rewrite written_preserves by exact Hindex.
   unfold SchemaEvaluation.value. now rewrite SchemaEvaluationBinaryMP.mp_arrays by discriminate. }
 assert (Hlengths:forall watched,length (memory (machine (output middle key)) watched)=length (memory (machine f) watched)).
 { intro watched. unfold output,middle. cbn [machine setMachine]. rewrite written_all_lengths. apply SchemaEvaluationBinaryMP.mp_lengths. }
 exists (output middle key). split.
 { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
   unfold output,middle. cbn [machine setMachine]. rewrite written_other,SchemaEvaluationBinaryMP.mp_arrays by discriminate. reflexivity. }
 split;[exact Hmarked|].
 split;[unfold output,middle;cbn [machine setMachine];apply written_arena;now apply SchemaEvaluationBinaryMP.mp_arena|].
 split;[unfold output,middle;cbn [machine setMachine];apply written_classes;now apply SchemaEvaluationBinaryMP.mp_classes|].
 split;[unfold output,middle;cbn [machine setMachine];apply written_topology;now apply SchemaEvaluationBinaryMP.mp_topology|].
 split;[unfold output,middle;cbn [machine setMachine];rewrite written_meta,SchemaEvaluationBinaryMP.mp_cell by discriminate;exact Herror|].
 split;[exact Hvalues|]. split;[exact Hlengths|].
 assert (Hnextgood:ClassLookup.wellformed (machine (output middle key))).
 { unfold output,middle,ClassLookup.wellformed. cbn [machine setMachine].
   rewrite written_other,SchemaEvaluationBinaryMP.mp_arrays by discriminate. exact Hgood. }
 split;[|exact Hnextgood].
 destruct (Schemata.infer rho depth (Schemata.template_mp ci ca)) as [result|] eqn:Hinfer.
 - destruct Hmeaning as [Hmeaning Hvalid]. split.
   + unfold post. split.
     * exists result. split;[exact Hinfer|]. unfold output,middle. cbn [machine setMachine]. rewrite written_same.
       -- exact Hmeaning.
       -- now rewrite SchemaEvaluationBinaryMP.mp_arrays by discriminate.
     * split;[exact Hvalues|]. intros watched Hprotected. apply Hlengths.
   + unfold output,middle. cbn [machine setMachine]. now rewrite written_meta.
 - unfold output,middle. cbn [machine setMachine]. now rewrite written_meta.
Qed.
Theorem cell_abstraction (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar stride depth key childKey id fs classes rho p reserve bound observations :
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
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final,SchemaEvaluationIndexBounds.raw_arena (machine final) (length fs) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,observations)) /\
 post f final fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) rho depth (Protocol.CE (Schemata.template_abstract p)) key /\
 NativeRepresentation.canonical_arena (machine final) fs /\
 ClassStorage.represents (machine final) fs (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)]) /\
 meta_value (machine final) 8=0 /\ FormulaTopology.ordered (machine final) (length fs) /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)])+reserve)<=maximum /\ ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hstride Hdepth Hkey Hchildkey Hchildword Hchild Hmeta Hbound Harena Hclasses Hgood Herror Htop Hmeaning Hbudget HrawInitial.
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
 exists (output middle key). split.
 { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
   unfold output,middle. cbn [machine setMachine]. unfold built. rewrite written_other,SchemaClass.result_other by discriminate. reflexivity. }
 split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split.
 - apply written_arena. now apply SchemaClass.result_arena.
 - split;[exact (written_classes _ _ _ _ _ Hnext)|]. split.
   + rewrite written_meta. unfold built. now rewrite SchemaClass.result_meta_other by lia.
   + split;[apply written_topology;now apply SchemaClass.result_topology|]. split;[exact Hroom|]. split.
     * unfold ClassLookup.wellformed. rewrite written_other by discriminate. fold (ClassLookup.wellformed built).
       unfold built. apply (SchemaClass.append_wellformed _ fs classes);[exact Hclasses|exact Hgood|exact (proj1 Hmeaning)].
     * rewrite written_meta. unfold built. now rewrite SchemaClass.result_meta_other by lia.
Qed.
Theorem cell_meta_zero (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar key cls fs classes rho bound observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (0,Z.of_nat a,b,c,rawd,ty,ar) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=0 ->
 (8<length (memory (machine f) arraydef_0__meta))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error classes cls=Some (rho a) -> word (Z.of_nat cls) ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final,SchemaEvaluationIndexBounds.raw_arena (machine final) (length fs) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final fs classes rho 0 (Protocol.CE (Schemata.metavariable a)) key /\
 ClassStorage.represents (machine final) fs classes /\
 NativeRepresentation.canonical_arena (machine final) fs /\ FormulaTopology.ordered (machine final) (length fs) /\
 meta_value (machine final) 8=0 /\ meta_value (machine final) 18=meta_value (machine f) 18 /\ ClassLookup.wellformed (machine final).
Proof.
 intros Hnode Hraw Hkey Hbound Harg Hdepth Hmeta Harena Htop Herror Hclasses Hgood Hcls Hword HrawInitial.
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
 exists (output middle key). split.
 { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
   unfold output,middle. cbn [machine setMachine]. rewrite Hbuilt. rewrite written_other by discriminate. unfold SchemaShiftClass.started. apply store_meta_other;discriminate. }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
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
Theorem cell_meta_set (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar key cls variable depth fs classes rho reserve bound observations :
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
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final,SchemaEvaluationIndexBounds.raw_arena (machine final) (length fs) bound /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final fs (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) rho depth (Protocol.CE (Schemata.metavariable a)) key /\
 ClassStorage.represents (machine final) fs (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) /\
 NativeRepresentation.canonical_arena (machine final) fs /\ FormulaTopology.ordered (machine final) (length fs) /\
 meta_value (machine final) 18=meta_value (machine f) 18 /\ meta_value (machine final) 8=meta_value (machine f) 8 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)])+reserve)<=maximum /\ ClassLookup.wellformed (machine final).
Proof.
 intros Hnode Hraw Hkey Hbound Harg Hdepth Hpositive Hmeta Harena Htop Hclasses Hgood Hclass Hrho Hsum Hbudget HrawInitial.
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
 exists (output middle key). split.
 { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawInitial].
   unfold output,middle. cbn [machine setMachine]. rewrite Hbuilt. rewrite written_other,SchemaClass.result_other by discriminate. unfold SchemaShiftClass.started. apply store_meta_other;discriminate. }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
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
Theorem shift_abstract s bs ns fs classes cls root p depth bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error (memory s arraydef_0__classes) cls=Some (1,Z.of_nat root) -> nth_error fs root=Some p ->
  nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__schemaShiftClass_cls=Z.of_nat cls -> ns vardef_0__schemaShiftClass_depth=Z.of_nat depth -> (0<depth)%nat ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  Z.of_nat bound+Z.of_nat depth<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
  Z.of_nat (length fs+S root*S root)<=9223372036854775807 ->
  Z.of_nat (length classes+S reserve)<=maximum ->
  exists final next, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+depth) /\
    execObserved (funcdef_0__schemaShiftClass bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\
    ClassStorage.represents final next (classes++[Schemata.shifted_class depth (VirtualClasses.abstract (VirtualClasses.core p))]) /\
    meta_value final 0=Z.of_nat (length classes) /\ meta_value final 8=0 /\
    (exists extra,next=fs++extra) /\ FormulaTopology.ordered final (length next) /\
    (length next<=length fs+S root*S root)%nat /\
    Z.of_nat (length (classes++[Schemata.shifted_class depth (VirtualClasses.abstract (VirtualClasses.core p))])+reserve)<=maximum /\
    stdin final=stdin s /\ stdout final=stdout s /\ ClassLookup.wellformed final /\ meta_value final 18=meta_value s 18.
Proof.
 intros Hmeta Hsip Harena Htop Herror Hclasses Hgood Hraw Hp Hfalse Hcls Hdepth Hpositive Hfuel HrawInitial Hindices Hheight Hbudget Hclassbudget.
 assert (Hformula:RenameMemoIndexBounds.formula_bound bound p).
 { exact (SchemaEvaluationIndexBounds.formula_lookup bound fs root p
     (SchemaEvaluationIndexBounds.canonical_raw_formulas s fs bound Harena Htop HrawInitial) Hp). }
 destruct (SchemaEvaluationMetaInvariant.shift_abstract_refines s bs ns fs classes cls root p depth bound reserve observations
   Hmeta Hsip Harena Htop Herror Hclasses Hgood Hraw Hp Hfalse Hcls Hdepth Hpositive Hfuel Hformula Hindices Hheight Hbudget Hclassbudget)
   as (final & next & Hrun & Hpost).
 destruct (SchemaEvaluationIndexShiftClass.generated_abstract_refines s bs ns fs classes cls root p depth bound reserve observations
   Hmeta Hsip Harena Htop Herror Hclasses Hraw Hp Hfalse Hcls Hdepth Hpositive Hfuel HrawInitial Hindices Hheight Hbudget Hclassbudget)
   as (actual & nextActual & HrawNext & Hactual & HarenaActual & Hrest).
 assert (Heq:final=actual) by congruence. subst actual.
 assert (Hlen:length next=length nextActual).
 { pose proof (proj1 (proj2 (proj1 (proj1 Hpost)))) as Hcount.
   pose proof (proj1 (proj2 (proj1 HarenaActual))) as HcountActual. lia. }
 exists final,next. split;[rewrite Hlen;exact HrawNext|]. split;assumption.
Qed.
Theorem meta_abstract (f:SchemaEvaluation.Frame) width remaining outer_remaining a cls root p d bound fs classes rho formula_reserve class_reserve observations :
 nums f vardef_0__schemaInstance_a=Z.of_nat a ->
 nth_error (memory (machine f) arraydef_0__schemaArguments) a=Some (Z.of_nat cls) ->
 SchemaEvaluation.depth width remaining=Z.of_nat d -> (0<d)%nat ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error (memory (machine f) arraydef_0__classes) cls=Some (1,Z.of_nat root) -> nth_error fs root=Some p ->
 rho a=VirtualClasses.abstract (VirtualClasses.core p) -> nth_error fs 0=Some SetTheory.falsity ->
 Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 Z.of_nat bound+Z.of_nat d<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
 Z.of_nat (length fs+S root*S root+formula_reserve)<=9223372036854775807 ->
 Z.of_nat (length classes+S class_reserve)<=maximum ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+d) /\
 execLocalObserved (SchemaEvaluation.meta_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine f final,observations)) /\ NativeRepresentation.canonical_arena final next /\
 ClassStorage.represents final next (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) /\
 SchemaEvaluation.meaning next (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)]) rho d
   (Protocol.CE (Schemata.metavariable a)) (meta_value final 0) /\ meta_value final 8=0 /\
 (exists extra,next=fs++extra) /\ FormulaTopology.ordered final (length next) /\
 Z.of_nat (length next+formula_reserve)<=9223372036854775807 /\
 Z.of_nat (length (classes++[Schemata.instantiate_class rho d (Schemata.metavariable a)])+class_reserve)<=maximum /\ ClassLookup.wellformed final /\ meta_value final 18=meta_value (machine f) 18.
Proof.
 intros Ha Hlookup Hd Hpositive Hmeta Hsip Harena Htop Herror Hclasses Hgood Hraw Hp Hrho Hfalse Hfuel Hbound Hindices Hheight Hbudget Hclassbudget.
 destruct (shift_abstract (machine f) (fun _=>false)
   (arguments (Z.of_nat cls) (SchemaEvaluation.depth width remaining)) fs classes cls root p d bound class_reserve observations
   Hmeta Hsip Harena Htop Herror Hclasses Hgood Hraw Hp Hfalse
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_other by discriminate;apply RenameMemoControl.updated_same)
   ltac:(unfold arguments;rewrite RenameMemoControl.updated_same;exact Hd) Hpositive Hfuel Hbound Hindices Hheight ltac:(lia) Hclassbudget)
 as (final & next & HrawNext & Hrun & Hnext & Hnextclasses & Hindex & Hflag & Hprefix & Hnexttop & Hgrowth & Hclassroom & Hinput & Houtput & Hnextgood & Hvalid).
 exists final,next. split;[exact HrawNext|]. split;[eapply generated_helper;eassumption|]. split;[exact Hnext|].
 assert (Hmeaning:Schemata.instantiate_class rho d (Schemata.metavariable a)=Schemata.shifted_class d (VirtualClasses.abstract (VirtualClasses.core p))).
 { cbn [Schemata.instantiate_class]. now rewrite Hrho. }
 rewrite Hmeaning. split;[exact Hnextclasses|]. split.
 - unfold SchemaEvaluation.meaning,SchemaEvaluation.class_value. rewrite Hmeaning,Hindex. split;[unfold word;lia|].
   rewrite Nat2Z.id,nth_error_app2 by lia. now rewrite Nat.sub_diag.
 - split;[exact Hflag|]. split;[exact Hprefix|]. split;[exact Hnexttop|]. split;[lia|]. split;[exact Hclassroom|]. split;assumption.
Qed.
Theorem cell_meta_abstract (f:SchemaEvaluation.Frame) width remaining outer_remaining node a b c rawd ty ar key cls root p depth bound fs classes rho formula_reserve class_reserve observations :
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
 Z.of_nat (RenameMemoBounds.fuel root)<=maximum -> SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 Z.of_nat bound+Z.of_nat depth<=maximum -> Z.of_nat (S (RenameMemoTransition.height p))<=maximum ->
 Z.of_nat (length fs+S root*S root+formula_reserve)<=9223372036854775807 ->
 Z.of_nat (length classes+S class_reserve)<=maximum ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) (bound+depth) /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
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
 destruct (meta_abstract parsed width remaining outer_remaining a cls root p depth bound fs classes rho formula_reserve class_reserve observations
   (descriptor_a _ _ _ _ _ _ _ _) Harg Hdepth Hpositive Hmeta Hsip Harena Htop Herror Hclasses Hgood Hclass Hp Hrho Hfalse Hfuel Hindices Hindexroom Hheight Hbudget Hclassbudget)
 as (built & next & HrawNext & Hrun & Hnext & Hnextclasses & Hmeaning & Hflag & Hprefix & Hnexttop & Hroom & Hclassroom & Hnextgood & Hvalid).
 set (middle:=setMachine parsed built).
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\
   post f (output middle key) next (classes++[Schemata.instantiate_class rho depth (Schemata.metavariable a)]) rho depth (Protocol.CE (Schemata.metavariable a)) key).
 { eapply (finish meta);try eassumption.
   - unfold middle. exact (descriptor_kind f 0 (Z.of_nat a) b c rawd ty ar).
   - reflexivity.
   - lia.
 }
 exists (output middle key),next. split.
 { unfold output,middle. cbn [machine setMachine]. exact (written_raw built key (meta_value built 0) (length next) _ HrawNext). }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_classes|].
 split;[now rewrite written_meta|]. split;[exact Hprefix|]. split;[now apply written_topology|]. split;[exact Hroom|]. split;[exact Hclassroom|]. split;[unfold ClassLookup.wellformed;now rewrite written_other by discriminate|now rewrite written_meta].
Qed.
Import SchemaEvaluationAxiom.
Theorem axiom_semantic (f:SchemaEvaluation.Frame) width remaining outer_remaining tag rawI rawJ rawK stride d idA idB idC
 fs classes rho tp tq tr bound reserve observations :
 (tag<=17)%nat -> nums f vardef_0__schemaInstance_a=Z.of_nat tag ->
 nums f vardef_0__schemaInstance_b=Z.of_nat rawI -> nums f vardef_0__schemaInstance_c=Z.of_nat rawJ ->
 nums f vardef_0__schemaInstance_d=Z.of_nat rawK -> nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 SchemaEvaluation.depth width remaining=Z.of_nat d ->
 readable (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI ->
 readable (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ ->
 readable (machine f) stride d (Nat.eqb tag 1) rawK ->
 selected_id (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI=Z.of_nat idA ->
 selected_id (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ=Z.of_nat idB ->
 selected_id (machine f) stride d (Nat.eqb tag 1) rawK=Z.of_nat idC ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 nth_error fs 0=Some SetTheory.falsity -> word (Z.of_nat idA) -> word (Z.of_nat idB) -> word (Z.of_nat idC) ->
 AxiomTaggedInvariant.ready fs tag idA idB idC rawI rawJ rawK
   (Schemata.instantiate_formula rho d tp) (Schemata.instantiate_formula rho d tq) (Schemata.instantiate_formula rho d tr) ->
 AxiomTaggedInvariant.renaming_ready tag idA rawJ (Schemata.instantiate_formula rho d tp) bound ->
 Z.of_nat (length fs+AxiomTaggedInvariant.cost tag idA+reserve)<=9223372036854775807 ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena final (length next) (SchemaEvaluationIndexAxiomTagged.ceiling bound rawI rawJ rawK) /\
 execLocalObserved (SchemaEvaluation.axiom_handler width remaining outer_remaining) (f,observations)=
 Some (KeepGoing,(setMachine (native_frame f stride d tag rawI rawJ rawK) final,observations)) /\
 SchemaEvaluation.meaning next classes rho d (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag tp tq tr rawI rawJ rawK)))
   (meta_value final 0) /\
 NativeRepresentation.canonical_arena final next /\ FormulaTopology.ordered final (length next) /\
 (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 13=1 /\
 Z.of_nat (length next+reserve)<=9223372036854775807 /\
 (length next<=length fs+AxiomTaggedInvariant.cost tag idA)%nat /\
 AxiomStorage.logical_frame (machine f) final /\
 (forall watched,RenameMemoLengths.protected watched -> length (memory final watched)=length (memory (machine f) watched)).
Proof.
 intros Htag Ha Hb Hc Hd Hstride Hdepth HreadA HreadB HreadC HA HB HC Hmeta Hsip Harena Htop Herror Hfalse
   HwordA HwordB HwordC Hready Hrename Hbudget HrawInitial.
 destruct (SchemaEvaluationIndexAxiomTagged.construct (machine f) fs tag idA idB idC rawI rawJ rawK
   (Schemata.instantiate_formula rho d tp) (Schemata.instantiate_formula rho d tq) (Schemata.instantiate_formula rho d tr)
   bound reserve observations Htag Hmeta Hsip Harena Htop Herror Hfalse HwordA HwordB HwordC Hready Hrename Hbudget HrawInitial)
 as (witness & Hwitness & final & next & index & HrawNext & Hrun & Hnext & Hindex & Hindexword & Hmeaning & Hderives & Hprefix & Hflag & Hsuccess & Hnexttop & Hroom & Hgrowth & Hframe & Hlengths).
 exists final,next. split;[exact HrawNext|]. split.
 - eapply generated_helper;try eassumption.
   + rewrite Hlengths by (unfold RenameMemoLengths.protected;repeat split;discriminate). lia.
   + now rewrite HA,HB,HC.
 - split.
   + exists (SetTheory.axiom_formula witness). split.
     * cbn [Schemata.infer]. rewrite <-AxiomTaggedInvariant.literal_instantiated,Hwitness. reflexivity.
     * unfold SchemaEvaluation.formula_value. rewrite Hindex. split;[exact Hindexword|]. now rewrite Nat2Z.id.
   + exact (conj Hnext (conj Hnexttop (conj Hprefix (conj Hflag (conj Hsuccess (conj Hroom (conj Hgrowth (conj Hframe Hlengths)))))))).
Qed.
Theorem cell_axiom (f:SchemaEvaluation.Frame) width remaining outer_remaining node ty ar key tag rawI rawJ rawK stride d idA idB idC
 fs classes rho tp tq tr bound reserve observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (8,Z.of_nat tag,Z.of_nat rawI,Z.of_nat rawJ,Z.of_nat rawK,ty,ar) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key -> (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 (tag<=17)%nat -> nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 SchemaEvaluation.depth width remaining=Z.of_nat d ->
 SchemaEvaluationAxiom.readable (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI ->
 SchemaEvaluationAxiom.readable (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ ->
 SchemaEvaluationAxiom.readable (machine f) stride d (Nat.eqb tag 1) rawK ->
 SchemaEvaluationAxiom.selected_id (machine f) stride d (AxiomTaggedInvariant.needs_p tag) rawI=Z.of_nat idA ->
 SchemaEvaluationAxiom.selected_id (machine f) stride d (AxiomTaggedInvariant.needs_q tag) rawJ=Z.of_nat idB ->
 SchemaEvaluationAxiom.selected_id (machine f) stride d (Nat.eqb tag 1) rawK=Z.of_nat idC ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) -> meta_value (machine f) 8=0 ->
 nth_error fs 0=Some SetTheory.falsity -> word (Z.of_nat idA) -> word (Z.of_nat idB) -> word (Z.of_nat idC) ->
 AxiomTaggedInvariant.ready fs tag idA idB idC rawI rawJ rawK
   (Schemata.instantiate_formula rho d tp) (Schemata.instantiate_formula rho d tq) (Schemata.instantiate_formula rho d tr) ->
 AxiomTaggedInvariant.renaming_ready tag idA rawJ (Schemata.instantiate_formula rho d tp) bound ->
 Z.of_nat (length fs+AxiomTaggedInvariant.cost tag idA+reserve)<=9223372036854775807 ->
 SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) bound ->
 exists final next,SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) (SchemaEvaluationIndexAxiomTagged.ceiling bound rawI rawJ rawK) /\
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(final,observations)) /\
 post f final next classes rho d (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag tp tq tr rawI rawJ rawK))) key /\
 NativeRepresentation.canonical_arena (machine final) next /\ FormulaTopology.ordered (machine final) (length next) /\
 ClassStorage.represents (machine final) next classes /\
 (exists extra,next=fs++extra) /\ meta_value (machine final) 8=0 /\ meta_value (machine final) 13=1 /\
 Z.of_nat (length next+reserve)<=9223372036854775807 /\ (length next<=length fs+AxiomTaggedInvariant.cost tag idA)%nat /\
 ClassLookup.wellformed (machine final) /\ meta_value (machine final) 18=meta_value (machine f) 18.
Proof.
 intros Hnode Hraw Hkey Hbound Hclasses Hgood Htag Hstride Hdepth HreadA HreadB HreadC HA HB HC Hmeta Hsip Harena Htop Herror Hfalse
   HwordA HwordB HwordC Hready Hrename Hbudget HrawInitial.
 set (parsed:=descriptor_frame f (8,Z.of_nat tag,Z.of_nat rawI,Z.of_nat rawJ,Z.of_nat rawK,ty,ar)).
 assert (Ha:nums parsed vardef_0__schemaInstance_a=Z.of_nat tag) by apply descriptor_a.
 assert (Hb:nums parsed vardef_0__schemaInstance_b=Z.of_nat rawI).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hc:nums parsed vardef_0__schemaInstance_c=Z.of_nat rawJ).
 { unfold parsed. cbn [descriptor_frame nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
 assert (Hd:nums parsed vardef_0__schemaInstance_d=Z.of_nat rawK).
 { unfold parsed. cbn [descriptor_frame nums setNum]. apply RenameMemoControl.updated_same. }
 destruct (axiom_semantic parsed width remaining outer_remaining tag rawI rawJ rawK stride d idA idB idC
   fs classes rho tp tq tr bound reserve observations Htag Ha Hb Hc Hd ltac:(unfold parsed;now rewrite descriptor_width) Hdepth
   HreadA HreadB HreadC HA HB HC Hmeta Hsip Harena Htop Herror Hfalse HwordA HwordB HwordC Hready Hrename Hbudget HrawInitial)
 as (built & next & HrawNext & Hrun & Hmeaning & Hnext & Hnexttop & Hprefix & Hflag & Hsuccess & Hroom & Hgrowth & Hframe & Hlengths).
 set (middle:=setMachine (SchemaEvaluationAxiom.native_frame parsed stride d tag rawI rawJ rawK) built).
 assert (Hkind:nums middle vardef_0__schemaInstance_kind=8).
 { unfold middle,SchemaEvaluationAxiom.native_frame,SchemaEvaluationAxiom.arguments_frame.
   repeat match goal with |- context [if ?test then _ else _]=>destruct test end;exact (descriptor_kind f 8 (Z.of_nat tag) (Z.of_nat rawI) (Z.of_nat rawJ) (Z.of_nat rawK) ty ar). }
 assert (Hmiddlekey:nums middle vardef_0__schemaInstance_key=Z.of_nat key).
 { unfold middle,SchemaEvaluationAxiom.native_frame,SchemaEvaluationAxiom.arguments_frame.
   repeat match goal with |- context [if ?test then _ else _]=>destruct test end;exact Hkey. }
 assert (Hfinish:execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
   Some (KeepGoing,(output middle key,observations)) /\
   post f (output middle key) next classes rho d (Protocol.PE (Schemata.template_ax (Schemata.template_axiom tag tp tq tr rawI rawJ rawK))) key).
 { eapply (finish axiom);try eassumption;first [reflexivity|lia]. }
 assert (Hwellformed:ClassLookup.wellformed built).
 { unfold ClassLookup.wellformed in *. rewrite (proj1 Hframe) by (unfold RenameStorage.Arrays.persistent_array;repeat split;discriminate). exact Hgood. }
 assert (Hvalid:meta_value built 18=meta_value (machine f) 18).
 { apply (proj1 (proj2 Hframe));unfold RenameStorage.Cells.protected;repeat split;discriminate. }
 exists (output middle key),next. split.
 { unfold output,middle. cbn [machine setMachine]. exact (written_raw built key (meta_value built 0) (length next) _ HrawNext). }
 destruct Hfinish as [Hexec Hpost]. split;[exact Hexec|]. split;[exact Hpost|].
 assert (Hnextclasses:ClassStorage.represents built next classes).
 { destruct Hprefix as [extra Hprefix]. rewrite Hprefix. eapply AxiomStorage.classes_transport;[exact Hframe|exact Hclasses]. }
 unfold output,middle. cbn [machine setMachine]. split;[now apply written_arena|]. split;[now apply written_topology|].
 split;[now apply written_classes|]. split;[exact Hprefix|]. split;[now rewrite written_meta|]. split;[now rewrite written_meta|]. split;[exact Hroom|]. split;[exact Hgrowth|]. split.
 - unfold ClassLookup.wellformed. now rewrite written_other by discriminate.
 - now rewrite written_meta.
Qed.
Definition core (f:SchemaEvaluation.Frame) width remaining outer_remaining fs classes rho depth expression key reserve index_bound observations :=
  exists final next_fs next_classes,
    bounded (machine final) next_fs next_classes index_bound /\
    execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
      Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) next_fs /\ meta_value (machine final) 8=0 /\
    prefix fs next_fs /\ prefix classes next_classes /\
    ClassStorage.represents (machine final) next_fs next_classes /\
    FormulaTopology.ordered (machine final) (length next_fs) /\ ClassLookup.wellformed (machine final) /\
    (length next_classes<=S (length classes))%nat /\ word (Z.of_nat (length next_fs)) /\
    Z.of_nat (length next_fs+reserve)<=SchemaEvaluationBoundedCell.bound /\
    semantic_result f final next_fs next_classes rho depth expression key.
Lemma core_success (f final:SchemaEvaluation.Frame) width remaining outer_remaining fs classes next_fs next_classes rho depth expression key reserve index_bound observations :
  execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=
    Some (KeepGoing,(final,observations)) ->
  NativeRepresentation.canonical_arena (machine final) next_fs -> meta_value (machine final) 8=0 ->
  prefix fs next_fs -> prefix classes next_classes ->
  ClassStorage.represents (machine final) next_fs next_classes ->
  FormulaTopology.ordered (machine final) (length next_fs) -> ClassLookup.wellformed (machine final) ->
  (length next_classes<=S (length classes))%nat ->
  SchemaPairSemantic.post f final next_fs next_classes rho depth expression key ->
  meta_value (machine final) 18=meta_value (machine f) 18 ->
  Z.of_nat (length next_fs+reserve)<=SchemaEvaluationBoundedCell.bound ->
  SchemaEvaluationIndexBounds.raw_arena (machine final) (length next_fs) index_bound ->
 SchemaEvaluationIndexBounds.classes index_bound next_classes ->
 core f width remaining outer_remaining fs classes rho depth expression key reserve index_bound observations.
Proof.
  intros Hrun Harena Herror Hfs Hclasses Hclassrep Htop Hgood Hgrowth Hpost Hvalid Hreserve Hraw HclassBounds.
  exists final,next_fs,next_classes. split;[exact (conj Hraw HclassBounds)|].
  split;[exact Hrun|]. split;[exact Harena|]. split;[exact Herror|].
  split;[exact Hfs|]. split;[exact Hclasses|]. split;[exact Hclassrep|].
  split;[exact Htop|]. split;[exact Hgood|]. split;[exact Hgrowth|].
  split;[exact (arena_count_word _ _ Harena)|]. split;[exact Hreserve|]. left. split;assumption.
Qed.
Ltac finish_indices := first
 [solve [eassumption]
 |lazymatch goal with |-SchemaEvaluationIndexBounds.raw_arena ?native ?count ?upper =>
    match goal with Hraw:SchemaEvaluationIndexBounds.raw_arena native count ?lower |- _ =>
      eapply (SchemaEvaluationIndexBounds.raw_arena_mono native count lower upper);[cbn [successor SchemaEvaluationIndexAxiomTagged.ceiling];lia|exact Hraw] end end
 |lazymatch goal with |-SchemaEvaluationIndexBounds.classes ?upper ?entries =>
    match goal with Hclasses:SchemaEvaluationIndexBounds.classes ?lower entries |- _ =>
      eapply (SchemaEvaluationIndexShiftClass.classes_mono lower upper entries);[cbn [successor SchemaEvaluationIndexAxiomTagged.ceiling];lia|exact Hclasses] end end].
Lemma renaming_needs_p tag : AxiomTaggedInvariant.uses_rename tag=true -> AxiomTaggedInvariant.needs_p tag=true.
Proof.
 unfold AxiomTaggedInvariant.uses_rename,AxiomTaggedInvariant.needs_p.
 let rec cases fuel := lazymatch fuel with O=>cbn;discriminate |S ?rest=>destruct tag as [|tag];[cbn;auto|cases rest] end in cases 17%nat.
Qed.
Theorem generated_view source (f:SchemaEvaluation.Frame) root fs classes expressions rho node depth kind a b c d expression
 width remaining outer_remaining reserve index_bound observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 SchemaGraph.reachable source root node depth ->
 view fs classes expressions kind a b c d expression ->
 SchemaRepresentation.fields_fit kind a b c d expression ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 SchemaEvaluationInvariant.completed source root expressions rho fs classes (machine f) (SchemaGraph.key root node depth) ->
 Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
 (SchemaGraph.width root*SchemaGraph.width root<=length (memory (machine f) arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat (SchemaGraph.key root node depth) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) fs -> FormulaTopology.ordered (machine f) (length fs) ->
 ClassStorage.represents (machine f) fs classes -> ClassLookup.wellformed (machine f) ->
 nth_error fs 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 ready (machine f) fs classes rho depth kind a b c d reserve ->
 bounded (machine f) fs classes index_bound ->
 Z.of_nat (successor kind index_bound depth b c d)<=maximum ->
 core f width remaining outer_remaining fs classes rho depth expression (SchemaGraph.key root node depth) reserve (successor kind index_bound depth b c d) observations.
Proof.
 intros Hordered Hroot Hreachable Hview Hfit Hraw Hsource Hcompleted Hword Hallocated Hnode Hdepth Hstride Hkey
   Hmeta Hsip Harena Htop Hclasses Hwellformed Hfalse Herror [HinitialRoom Hready] [HrawInitial HclassBounds] HindexRoom.
 pose proof (SchemaGraph.reachable_grid source root node depth Hordered Hroot Hreachable) as [Hnodegrid [Hdepthgrid Hkeygrid]].
 assert (Hbound:(SchemaGraph.key root node depth<length (memory (machine f) arraydef_0__schemaValues))%nat) by lia.
 destruct Hview as [aa bb cc dd Hsmall|aa bb cc dd cls Hliteral|aa bb cc dd p Hliteral|
   aa bb cc dd p Hchild|aa bb cc dd ca cb Hleft Hright|aa bb cc dd ca cb Hleft Hright|
   aa bb cc dd p q Hleft Hright|aa bb cc dd p Hchild|tag aa bb cc p q r Htag Hp Hq Hr|
   aa bb cc dd ci ca Hleft Hright|aa bb cc dd ci Hchild|aa bb cc dd p checked Hliteral].
 - cbn [ready] in Hready.
   destruct Hready as [[cls [Hargument [Hclsword Hcls]]] Hshift].
   destruct depth as [|depth'].
   + destruct (cell_meta_zero f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ cls fs classes rho index_bound observations
       Hnode Hraw Hkey Hbound Hargument Hdepth ltac:(lia) Harena Htop Herror Hclasses Hwellformed Hcls Hclsword HrawInitial)
       as (final & HrawNext & Hrun & Hpost & Hnextclasses & Hnext & Hnexttop & Hflag & Hvalid & Hnextgood).
     eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
   + destruct (Hshift ltac:(lia)) as [Hclassroom [Hsetroom Habstractroom]].
     pose proof (SchemaEvaluationIndexShiftClass.appended_bound index_bound (S depth') classes (rho aa)
       HclassBounds (class_lookup index_bound classes cls (rho aa) HclassBounds Hcls)) as HclassApp.
     change (SchemaEvaluationIndexBounds.classes (index_bound+S depth')
       (classes++[Schemata.instantiate_class rho (S depth') (Schemata.metavariable aa)])) in HclassApp.
     destruct (ClassLookup.lookup (machine f) fs classes cls (rho aa) Hclasses Hwellformed Hcls)
       as [_ [[variable [Hrho [Hvariable Hclass]]]|[body [p [Hrho [Hp Hclass]]]]]].
     * destruct (cell_meta_set f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ cls variable (S depth') fs classes rho 0 index_bound observations
         Hnode Hraw Hkey Hbound Hargument Hdepth ltac:(lia) ltac:(lia) Harena Htop Hclasses Hwellformed Hclass Hrho (Hsetroom variable Hrho) Hclassroom HrawInitial)
         as (final & HrawNext & Hrun & Hpost & Hnextclasses & Hnext & Hnexttop & Hvalid & Hflag & Hroom & Hnextgood).
       rewrite Herror in Hflag. eapply core_success;try eassumption.
       -- apply prefix_refl.
       -- eexists;reflexivity.
       -- rewrite length_app;cbn;lia.
       -- finish_indices.
     * destruct (Habstractroom cls body p Hclass Hp) as (bound & Hfuel & Hindices & Hindicesroom & Hheight & Hbudget).
       destruct (cell_meta_abstract f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ cls body p (S depth') index_bound fs classes rho reserve 0 observations
         Hnode Hraw Hkey Hbound Hargument Hdepth ltac:(lia) Hmeta Hsip Harena Htop Herror Hclasses Hwellformed Hclass Hp Hrho Hfalse
         Hfuel HrawInitial ltac:(cbn [successor] in HindexRoom;lia) Hheight Hbudget Hclassroom)
         as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hflag & Hprefix & Hnexttop & Hroom & Hclassroom' & Hnextgood & Hvalid).
       eapply core_success;try eassumption;try solve [eexists;reflexivity|rewrite length_app;cbn;lia|lia];finish_indices.

 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.CE (Schemata.literal_class cls)) (Z.of_nat aa)).
   { change (word (Z.of_nat aa) /\ nth_error classes (Z.to_nat (Z.of_nat aa))=Some cls). rewrite Nat2Z.id. split;assumption. }
   destruct (cell_literal f width remaining outer_remaining node 1 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ index_bound observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning HrawInitial)
     as (final & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.FE (Schemata.literal_formula p)) (Z.of_nat aa)).
   { change (word (Z.of_nat aa) /\ nth_error fs (Z.to_nat (Z.of_nat aa))=Some p). rewrite Nat2Z.id. split;assumption. }
   destruct (cell_literal f width remaining outer_remaining node 2 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ index_bound observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning HrawInitial)
     as (final & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct (cell_abstraction f width remaining outer_remaining node aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho p 0 index_bound observations
     Hnode Hraw Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Hclasses Hwellformed Herror Htop HmeanA Hready HrawInitial)
     as (final & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hflag & Hnexttop & Hroom & Hnextgood & Hvalid).
   assert (HclassApp:SchemaEvaluationIndexBounds.classes index_bound
     (classes++[Schemata.instantiate_class rho depth (Schemata.template_abstract p)])).
   { apply Forall_app. split;[exact HclassBounds|]. constructor;[|constructor].
     cbn [Schemata.instantiate_class SchemaEvaluationIndexBounds.class_bound]. cbn [VirtualClasses.erase].
     eapply SchemaEvaluationIndexBounds.formula_lookup with (index:=idA).
     - exact (SchemaEvaluationIndexBounds.canonical_raw_formulas _ fs index_bound Harena Htop HrawInitial).
     - change (word (Z.of_nat idA) /\ nth_error fs (Z.to_nat (Z.of_nat idA))=Some (Schemata.instantiate_formula rho (S depth) p)) in HmeanA.
       rewrite Nat2Z.id in HmeanA. exact (proj2 HmeanA). }
   eapply core_success;try eassumption;try solve [apply prefix_refl|eexists;reflexivity|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.CE ca)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.CE cb)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   change (word (Z.of_nat idA) /\ nth_error classes (Z.to_nat (Z.of_nat idA))=Some (Schemata.instantiate_class rho depth ca)) in HmeanA.
   change (word (Z.of_nat idB) /\ nth_error classes (Z.to_nat (Z.of_nat idB))=Some (Schemata.instantiate_class rho depth cb)) in HmeanB.
   rewrite Nat2Z.id in HmeanA,HmeanB. destruct HmeanA as [_ HclassA]. destruct HmeanB as [_ HclassB].
   destruct (Hready idA idB _ _ HclassA HclassB) as [Hrename Hbudget].
   destruct (cell_equal f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) idA idB fs classes rho ca cb reserve index_bound observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hwellformed
     HclassA HclassB Hrename Hbudget HrawInitial (class_lookup index_bound classes idA _ HclassBounds HclassA) (class_lookup index_bound classes idB _ HclassBounds HclassB) ltac:(cbn [successor] in HindexRoom;lia))
     as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.CE ca)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.CE cb)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   change (word (Z.of_nat idA) /\ nth_error classes (Z.to_nat (Z.of_nat idA))=Some (Schemata.instantiate_class rho depth ca)) in HmeanA.
   change (word (Z.of_nat idB) /\ nth_error classes (Z.to_nat (Z.of_nat idB))=Some (Schemata.instantiate_class rho depth cb)) in HmeanB.
   rewrite Nat2Z.id in HmeanA,HmeanB. destruct HmeanA as [_ HclassA]. destruct HmeanB as [_ HclassB].
   destruct (Hready idA idB _ _ HclassA HclassB) as [Hrename Hbudget].
   destruct (cell_member f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) idA idB fs classes rho ca cb reserve index_bound observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB Hmeta Hsip Harena Htop Hfalse Herror Hclasses Hwellformed
     HclassA HclassB Hrename Hbudget HrawInitial (class_lookup index_bound classes idA _ HclassBounds HclassA) (class_lookup index_bound classes idB _ HclassBounds HclassB) ltac:(cbn [successor] in HindexRoom;lia))
     as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.FE q)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   destruct (cell_imp f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) (Z.of_nat idA) (Z.of_nat idB) fs classes rho p q reserve index_bound observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB ltac:(lia) Harena Htop Herror Hclasses Hwellformed HmeanA HmeanB
     Hready HrawInitial)
     as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hflag & Hprefix & Hroom & Hnextgood & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.FE p)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];first [left;reflexivity|right;left;reflexivity])
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct (cell_universal f width remaining outer_remaining node 7 aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho (Schemata.instantiate_formula rho (S depth) p) (Protocol.FE (Schemata.template_all p)) reserve index_bound observations
     Hnode Hraw ltac:(auto) Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Htop Herror Hclasses Hwellformed HmeanA ltac:(intros;assumption)
     Hready HrawInitial)
     as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid & Hprefix & Hroom).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Htagword [Haword [Hbword Hcword]]]].
   destruct (axiom_ready source (machine f) root expressions rho fs classes node depth tag aa bb cc p q r _
     Hordered Hroot Hreachable Hsource Hp Hq Hr Hcompleted Hword Hallocated Haword Hbword Hcword)
     as (idA & idB & idC & HreadA & HreadB & HreadC & HselectedA & HselectedB & HselectedC & HwordA & HwordB & HwordC & HtypedReady).
   assert (Hneeded:AxiomTaggedInvariant.needs_p tag=true -> nth_error fs idA=Some (Schemata.instantiate_formula rho depth p)).
   { intro Hneed. destruct HtypedReady as [HA _]. unfold AxiomTaggedInvariant.ready in HA.
     rewrite Hneed in HA. exact HA. }
   destruct (Hready idA (Schemata.instantiate_formula rho depth p) HwordA Hneeded) as [bound [Hrename Hbudget]].
   assert (HrenameGlobal:AxiomTaggedInvariant.renaming_ready tag idA bb (Schemata.instantiate_formula rho depth p) index_bound).
   { unfold AxiomTaggedInvariant.renaming_ready in *.
     destruct (AxiomTaggedInvariant.uses_rename tag) eqn:Huses;[|exact I].
     destruct Hrename as (Hfuel & Hformula & Hroom & Hheight). split;[exact Hfuel|]. split.
     - exact (SchemaEvaluationIndexBounds.formula_lookup index_bound fs idA _
         (SchemaEvaluationIndexBounds.canonical_raw_formulas _ fs index_bound Harena Htop HrawInitial)
         (Hneeded (renaming_needs_p tag Huses))).
     - split;[|exact Hheight]. assert (Hinc:(AxiomTaggedInvariant.increment tag bb<=bb+2)%nat).
       { unfold AxiomTaggedInvariant.increment. destruct tag as [|[|[|[|[|tag]]]]];cbn;lia. }
       cbn [successor] in HindexRoom. repeat rewrite Nat2Z.inj_add in HindexRoom. lia. }
   destruct (cell_axiom f width remaining outer_remaining node _ _ _ tag aa bb cc (SchemaGraph.width root) depth idA idB idC
     fs classes rho p q r index_bound reserve observations Hnode Hraw Hkey Hbound Hclasses Hwellformed Htag Hstride Hdepth
     HreadA HreadB HreadC HselectedA HselectedB HselectedC Hmeta Hsip Harena Htop Herror Hfalse HwordA HwordB HwordC HtypedReady HrenameGlobal Hbudget HrawInitial)
     as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnexttop & Hnextclasses & Hprefix & Hflag & Hsuccess & Hroom & Hgrowth & Hnextgood & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 0 (Protocol.PE ci)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];left;reflexivity)
     Hcompleted Hleft Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_0_r in HreadA,HmeanA,HkeyA.
   destruct (completed_value source (machine f) root expressions rho fs classes node depth _ bb 0 (Protocol.PE ca)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];right;left;reflexivity)
     Hcompleted Hright Hword Hallocated) as (idB & HwordB & HreadB & HmeanB & HkeyB).
   rewrite Nat.add_0_r in HreadB,HmeanB,HkeyB.
   destruct (cell_mp f width remaining outer_remaining node aa bb (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa depth) (SchemaGraph.key root bb depth) idA (Z.of_nat idB) fs classes rho ci ca index_bound observations
     Hnode Hraw Hstride Hdepth Hkey Hbound eq_refl eq_refl HkeyA HkeyB HreadA HreadB ltac:(lia) Harena Htop Herror Hclasses Hwellformed HmeanA HmeanB HrawInitial)
     as (final & HrawNext & Hrun & Hnext & Hnextclasses & Hnexttop & Hflag & Hvalues & Hlengths & Hsemantic & Hnextgood).
   destruct (Schemata.infer rho depth (Schemata.template_mp ci ca)) as [result|] eqn:Hinfer.
   + destruct Hsemantic as [Hpost Hvalid]. eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
   + exists final,fs,classes. split;[split;finish_indices|]. split;[exact Hrun|]. split;[exact Hnext|]. split;[exact Hflag|].
     split;[apply prefix_refl|]. split;[apply prefix_refl|]. split;[exact Hnextclasses|].
     split;[exact Hnexttop|]. split;[exact Hnextgood|]. split;[lia|]. split;[exact (arena_count_word _ _ Hnext)|]. split;[exact HinitialRoom|].
     right. exists (Schemata.template_mp ci ca). repeat split;assumption.
 - destruct (completed_value source (machine f) root expressions rho fs classes node depth _ aa 1 (Protocol.PE ci)
     Hordered Hroot Hreachable Hsource ltac:(rewrite SchemaGraph.children_encode;cbn [SchemaGraph.children_fields];left;reflexivity)
     Hcompleted Hchild Hword Hallocated) as (idA & HwordA & HreadA & HmeanA & HkeyA).
   rewrite Nat.add_1_r in HreadA,HmeanA,HkeyA.
   destruct HmeanA as [childResult [HchildInfer HchildMeaning]].
   destruct (cell_universal f width remaining outer_remaining node 10 aa (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ (SchemaGraph.width root) depth _
     (SchemaGraph.key root aa (S depth)) (Z.of_nat idA) fs classes rho childResult (Protocol.PE (Schemata.template_gen ci)) reserve index_bound observations
     Hnode Hraw ltac:(auto) Hstride Hdepth Hkey ltac:(unfold SchemaGraph.key;lia) HkeyA HreadA ltac:(lia) Hbound Harena Htop Herror Hclasses Hwellformed HchildMeaning
     ltac:(intros next value Hvalue;exists (SetTheory.all childResult);split;[cbn [Schemata.infer];rewrite HchildInfer;reflexivity|exact Hvalue])
     Hready HrawInitial)
     as (final & next & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid & Hprefix & Hroom).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
 - destruct (fields_words _ _ _ _ _ _ Hfit) as [Hkword [Haword [Hbword [Hcword Hdword]]]].
   assert (Hmeaning:SchemaEvaluation.meaning fs classes rho depth (Protocol.PE (Schemata.saved_theorem p checked)) (Z.of_nat aa)).
   { exists p. split;[reflexivity|]. change (word (Z.of_nat aa) /\ nth_error fs (Z.to_nat (Z.of_nat aa))=Some p). rewrite Nat2Z.id. split;assumption. }
   destruct (cell_literal f width remaining outer_remaining node 11 (Z.of_nat aa) (Z.of_nat bb) (Z.of_nat cc) (Z.of_nat dd) _ _ _ fs classes rho depth _ index_bound observations
     Hnode Hraw ltac:(auto) ltac:(lia) Hkey Hbound Harena Hclasses Htop Hwellformed Herror Hmeaning HrawInitial)
     as (final & HrawNext & Hrun & Hpost & Hnext & Hnextclasses & Hnexttop & Hnextgood & Hflag & Hvalid).
   eapply core_success;try eassumption;try solve [apply prefix_refl|rewrite length_app;cbn;lia|lia];finish_indices.
Qed.
Lemma bounded_array_frame before after fs classes bound :
 memory after arraydef_0__formulas=memory before arraydef_0__formulas ->
 bounded before fs classes bound -> bounded after fs classes bound.
Proof.
 intros Hformulas [Hraw Hclasses]. split;[|exact Hclasses].
 exact (SchemaEvaluationIndexBounds.raw_array_frame before after (length fs) bound Hformulas Hraw).
Qed.
Lemma core_mono f width remaining outer_remaining fs classes rho depth expression key reserve lower upper observations :
 (lower<=upper)%nat ->
 core f width remaining outer_remaining fs classes rho depth expression key reserve lower observations ->
 core f width remaining outer_remaining fs classes rho depth expression key reserve upper observations.
Proof.
 intros Hle (final & nextfs & nextclasses & Hbounded & Hrest).
 exists final,nextfs,nextclasses. split;[|exact Hrest]. exact (bounded_mono _ _ _ lower upper Hle Hbounded).
Qed.
Theorem generated_represented source (f:SchemaEvaluation.Frame) logical root rho node depth expression
 width remaining outer_remaining reserve index_bound upper observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 SchemaGraph.reachable source root node depth ->
 SchemaRepresentation.represents (machine f) logical ->
 memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 nth_error (Protocol.expressions logical) node=Some expression ->
 SchemaEvaluationInvariant.completed source root (Protocol.expressions logical) rho (Protocol.formulas logical) (Protocol.classes logical)
   (machine f) (SchemaGraph.key root node depth) ->
 Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
 (SchemaGraph.width root*SchemaGraph.width root<=length (memory (machine f) arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node -> SchemaEvaluation.depth width remaining=Z.of_nat depth ->
 nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
 nums f vardef_0__schemaInstance_key=Z.of_nat (SchemaGraph.key root node depth) ->
 (31<length (memory (machine f) arraydef_0__meta))%nat -> (0<length (memory (machine f) arraydef_0__sipState))%nat ->
 NativeRepresentation.canonical_arena (machine f) (Protocol.formulas logical) ->
 FormulaTopology.ordered (machine f) (length (Protocol.formulas logical)) ->
 ClassStorage.represents (machine f) (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed (machine f) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity -> meta_value (machine f) 8=0 ->
 (forall k a b c d,
   nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode k a b c d expression) ->
   ready (machine f) (Protocol.formulas logical) (Protocol.classes logical) rho depth k a b c d reserve /\
   (successor k index_bound depth b c d<=upper)%nat) ->
 bounded (machine f) (Protocol.formulas logical) (Protocol.classes logical) index_bound ->
 Z.of_nat upper<=maximum ->
 core f width remaining outer_remaining (Protocol.formulas logical) (Protocol.classes logical) rho depth expression
   (SchemaGraph.key root node depth) reserve upper observations.
Proof.
 intros Hordered Hroot Hreachable Hrep Hnodes Hlookup Hcompleted Hword Hallocated Hnode Hdepth Hstride Hkey
   Hmeta Hsip Harena Htop Hclasses Hwellformed Hfalse Herror Hready Hbounded Hupperword.
 destruct (represented_view (machine f) logical node expression Hrep Hlookup)
   as (kind & a & b & c & d & Hraw & Hfit & Hview).
 destruct (Hready kind a b c d Hraw) as [Hresources Hsuccessor].
 eapply core_mono;[exact Hsuccessor|].
 eapply (generated_view source f root (Protocol.formulas logical) (Protocol.classes logical) (Protocol.expressions logical)
   rho node depth kind a b c d expression width remaining outer_remaining reserve index_bound observations);try eassumption.
 - now rewrite <-Hnodes.
 - lia.
Qed.
End SchemaEvaluationIndexCell.
