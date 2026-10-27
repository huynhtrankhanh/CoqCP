From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Schemata.
From NativeProof Require Import Index SipHash Lift ObservedLocal NativePrimitives ArenaFrame FormulaProjection
  Representation FormulaTopology ClassStorage ClassLookup SchemaClass RenameMemoControl RenameMemoRun RenameMemoBounds
  RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths
  RenameMemoClassEqual RenameStack RenameStorage InternReserve SchemaShiftClass RenameMemoIndexRun SchemaEvaluationIndexBounds SchemaEvaluationIndexClassEqual.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexShiftClass.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics SchemaShiftClass.
Lemma shifted_bound bound depth cls : SchemaEvaluationIndexBounds.class_bound bound cls ->
 SchemaEvaluationIndexBounds.class_bound (bound+depth) (Schemata.shifted_class depth cls).
Proof.
 destruct cls as [variable|p];cbn [Schemata.shifted_class SchemaEvaluationIndexBounds.class_bound].
 - lia.
 - intro Hbound.
   rewrite <- (SchemaShiftClass.shifted_abstract (VirtualClasses.erase p) depth).
   exact (SchemaEvaluationIndexBounds.renamed_formula bound shift_mode depth 0 1 (VirtualClasses.erase p) Hbound).
Qed.
Lemma classes_mono lower upper entries : (lower<=upper)%nat -> SchemaEvaluationIndexBounds.classes lower entries ->
 SchemaEvaluationIndexBounds.classes upper entries.
Proof. intros Hle H. eapply Forall_impl;[|exact H]. intros cls Hcls. exact (SchemaEvaluationIndexClassEqual.class_mono lower upper cls Hle Hcls). Qed.
Lemma appended_bound bound depth entries cls : SchemaEvaluationIndexBounds.classes bound entries ->
 SchemaEvaluationIndexBounds.class_bound bound cls ->
 SchemaEvaluationIndexBounds.classes (bound+depth) (entries++[Schemata.shifted_class depth cls]).
Proof. intros Hentries Hcls. apply Forall_app. split;[exact (classes_mono bound (bound+depth) entries ltac:(lia) Hentries)|constructor;[exact (shifted_bound bound depth cls Hcls)|constructor]]. Qed.
Lemma started_raw s cls count bound : SchemaEvaluationIndexBounds.raw_arena s count bound ->
 SchemaEvaluationIndexBounds.raw_arena (SchemaShiftClass.started s cls) count bound.
Proof. intro H. eapply SchemaEvaluationIndexBounds.raw_array_frame;[unfold SchemaShiftClass.started;apply store_meta_other;discriminate|exact H]. Qed.
Lemma class_result_raw s n entry count bound : SchemaEvaluationIndexBounds.raw_arena s count bound ->
 SchemaEvaluationIndexBounds.raw_arena (SchemaClass.result s n entry) count bound.
Proof. intro H. eapply SchemaEvaluationIndexBounds.raw_array_frame;[apply SchemaClass.result_other;discriminate|exact H]. Qed.
Theorem generated_abstract_refines s bs ns fs classes cls root p depth bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes ->
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
    stdin final=stdin s /\ stdout final=stdout s.
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hclasses Hraw Hlookup Hfalse Hcls Hdepth Hpositive Hfuel HrawInitial Hindices Hheight Hbudget Hclassbudget.
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
  destruct (RenameMemoIndexRun.generated_bounded (started s cls) (fun _=>false) (rename_arguments (Z.of_nat root) (Z.of_nat depth))
    fs p root 1 shift_mode depth 0 bound Hstartmeta Hstartsip (RenameMemoClassEqual.arena_positive _ _ Hstartarena)
    Hstarterror Hstartarena Hstarttopology Hlookup Hfalse eq_refl eq_refl eq_refl eq_refl eq_refl Hfuel Hroom
    Hshiftword Hargword (started_raw s cls (length fs) bound HrawInitial) Hindexroom Hheight observations)
    as (rframe & next & count & Hrename & Hrarena & Hcache & Hrword & Hrmeaning & Hrsource & Hrerror & Hempty & Hrgrowth & Hrtopology & Hrraw).
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
  exists final,next. split;[exact (class_result_raw _ _ _ _ _ Hrraw)|]. split.
  - apply (generated_abstract_helper s bs ns cls root depth (machine rframe) (length classes) observations);try assumption;
      [lia|exact (proj1 Hrclasses)|lia].
  - split;[now apply SchemaClass.result_arena|].
    split;[apply SchemaClass.append_represents;[lia|exact Hrclasses|exact Hdecode]|].
    split;[exact Hfinalmeta0|]. split;[unfold final;rewrite SchemaClass.result_meta_other by lia;exact Hrerror|].
    split;[exact Hrprefix|]. split;[now apply SchemaClass.result_topology|]. split;[exact Hrgrowth|].
    split;[rewrite length_app;cbn [length];lia|].
    destruct (proj2 (proj2 Hrframe)) as [Hinput Houtput]. split;[exact Hinput|exact Houtput].
Qed.
End SchemaEvaluationIndexShiftClass.
