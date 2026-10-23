From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Schemata.
From NativeProof Require Import Index SipHash Lift ObservedLocal NativePrimitives ArenaFrame FormulaProjection
  Representation FormulaTopology ClassStorage ClassLookup SchemaClass RenameMemoControl RenameMemoRun RenameMemoBounds
  RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoTransition RenameMemoCallers RenameMemoOutput RenameMemoLengths
  RenameMemoClassEqual RenameStack RenameStorage InternReserve.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaShiftClass.
Import IndexExecution SipHashExecution ObservedLocal IndexSemantics.
Definition started s cls := store_meta s 0 (Z.of_nat cls).
Definition rename_arguments root depth : varsfuncdef_0__rename -> Z :=
  update (update (update (update (fun _=>0) vardef_0__rename_node root)
    vardef_0__rename_mode 0) vardef_0__rename_shift depth) vardef_0__rename_initialDepth 1.
Lemma started_classes s cls fs classes : ClassStorage.represents s fs classes -> ClassStorage.represents (started s cls) fs classes.
Proof. intros [Hcount Hclasses]. split;[unfold started;rewrite meta_store_other by lia;exact Hcount|]. exact Hclasses. Qed.
Lemma started_storage s cls : ArenaFrame.storage s (started s cls).
Proof. apply ArenaFrame.storage_meta;lia. Qed.
Local Opaque funcdef_0__schemaClass funcdef_0__rename Imperative.update.
Ltac run_primitives :=
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];unfold started;rewrite ?store_meta_length;
       rewrite ?store_meta_other by discriminate;rewrite ?Nat2Z.id;first [assumption|lia])
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress rewrite meta_store_other by lia
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress rewrite Nat2Z.id
    |match goal with |- context [decide ?P] => first
      [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
Theorem generated_zero s bs ns cls observations :
  (8<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__schemaShiftClass_cls=Z.of_nat cls -> ns vardef_0__schemaShiftClass_depth=0 ->
  execObserved (funcdef_0__schemaShiftClass bs ns) (s,observations)=Some (tt,(started s cls,observations)).
Proof.
  intros Hmeta Hcls Hdepth. unfold funcdef_0__schemaShiftClass. rewrite eliminate_correct. unfold funcdef_0__schemaShiftClass_body.
  repeat first [progress rewrite Hcls|progress rewrite Hdepth
    |match goal with |- context [bool_decide ?P] => progress rewrite (bool_decide_false P) by congruence end
    |run_primitives]. reflexivity.
Qed.
Theorem generated_set s bs ns cls variable depth n observations :
  (8<length (memory s arraydef_0__meta))%nat ->
  nth_error (memory s arraydef_0__classes) cls=Some (0,Z.of_nat variable) ->
  ns vardef_0__schemaShiftClass_cls=Z.of_nat cls -> ns vardef_0__schemaShiftClass_depth=Z.of_nat depth ->
  (0<depth)%nat -> Z.of_nat variable+Z.of_nat depth<=maximum ->
  meta_value s 2=Z.of_nat n -> Z.of_nat n<maximum ->
  execObserved (funcdef_0__schemaShiftClass bs ns) (s,observations)=
    Some (tt,(SchemaClass.result (started s cls) n (0,Z.of_nat (variable+depth)),observations)).
Proof.
  intros Hmeta Hraw Hcls Hdepth Hpositive Hsum Hcount Hroom.
  assert (Hrawbound:(cls<length (memory s arraydef_0__classes))%nat) by (apply nth_error_Some;congruence).
  assert (Hnth : @nth (arrayType arrayIndex1 environment1 arraydef_0__classes) cls (memory s arraydef_0__classes) (0,0) = (0,Z.of_nat variable)) by (eapply List.nth_error_nth; exact Hraw).
  assert (Hsub:coerceInt (maximum-Z.of_nat variable) 64=maximum-Z.of_nat variable)
    by (apply coerce_word;unfold word;lia).
  assert (Hadd:coerceInt (Z.of_nat variable+Z.of_nat depth) 64=Z.of_nat (variable+depth)).
  { rewrite coerce_word by (unfold word;lia). lia. }
  pose proof (SchemaClass.generated_helper (started s cls) (fun _=>false)
    (SchemaClass.arguments 0 (Z.of_nat (variable+depth))) n 0 (Z.of_nat (variable+depth)) observations
    ltac:(unfold started;rewrite store_meta_length;exact Hmeta) ltac:(unfold started;rewrite meta_store_other by lia;exact Hcount)
    Hroom eq_refl eq_refl) as Happend.
  unfold funcdef_0__schemaShiftClass. rewrite eliminate_correct. unfold funcdef_0__schemaShiftClass_body.
  repeat first [progress rewrite Hcls|progress rewrite Hdepth
    |progress unfold addInt at 1|progress unfold subInt at 1
    |progress rewrite Hsub|progress rewrite Hadd
    |progress change (store_meta s 0 (Z.of_nat cls)) with (started s cls)
    |progress change (memory (started s cls) arraydef_0__classes) with (memory s arraydef_0__classes)
    |progress rewrite Hnth
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__schemaClass ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__schemaClass bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(SchemaClass.result (started s cls) n (0,Z.of_nat (variable+depth)),observations)))
         by exact Happend;rewrite Hrun;clear Hrun end
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by (unfold maximum in *;lia)
      |progress rewrite (bool_decide_false P) by (unfold maximum in *;lia)] end
    |run_primitives]. reflexivity.
Qed.
Theorem generated_abstract_helper s bs ns cls root depth renamed n observations :
  (8<length (memory s arraydef_0__meta))%nat ->
  nth_error (memory s arraydef_0__classes) cls=Some (1,Z.of_nat root) ->
  ns vardef_0__schemaShiftClass_cls=Z.of_nat cls -> ns vardef_0__schemaShiftClass_depth=Z.of_nat depth ->
  (0<depth)%nat ->
  execObserved (funcdef_0__rename (fun _=>false) (rename_arguments (Z.of_nat root) (Z.of_nat depth)))
    (started s cls,observations)=Some (tt,(renamed,observations)) ->
  (8<length (memory renamed arraydef_0__meta))%nat -> meta_value renamed 8=0 ->
  meta_value renamed 2=Z.of_nat n -> Z.of_nat n<maximum ->
  execObserved (funcdef_0__schemaShiftClass bs ns) (s,observations)=
    Some (tt,(SchemaClass.result renamed n (1,meta_value renamed 0),observations)).
Proof.
  intros Hmeta Hraw Hcls Hdepth Hpositive Hrename Hrmeta Hrerror Hcount Hroom.
  assert (Hrawbound:(cls<length (memory s arraydef_0__classes))%nat) by (apply nth_error_Some;congruence).
  assert (Hnth : @nth (arrayType arrayIndex1 environment1 arraydef_0__classes) cls (memory s arraydef_0__classes) (0,0) = (1,Z.of_nat root)) by (eapply List.nth_error_nth; exact Hraw).
  pose proof (SchemaClass.generated_helper renamed (fun _=>false) (SchemaClass.arguments 1 (meta_value renamed 0))
    n 1 (meta_value renamed 0) observations Hrmeta Hcount Hroom eq_refl eq_refl) as Happend.
  unfold funcdef_0__schemaShiftClass. rewrite eliminate_correct. unfold funcdef_0__schemaShiftClass_body.
  repeat first [progress rewrite Hcls|progress rewrite Hdepth|progress rewrite Hrerror
    |progress change (store_meta s 0 (Z.of_nat cls)) with (started s cls)
    |progress change (memory (started s cls) arraydef_0__classes) with (memory s arraydef_0__classes)
    |progress rewrite Hnth
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__rename ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__rename bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(renamed,observations))) by exact Hrename;rewrite Hrun;clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__schemaClass ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__schemaClass bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(SchemaClass.result renamed n (1,meta_value renamed 0),observations)))
         by exact Happend;rewrite Hrun;clear Hrun end
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
    |run_primitives]. reflexivity.
Qed.
Lemma shifted_abstract p depth : RenameStack.renamed (renaming shift_mode depth 0) 1 p=
  SetTheory.rename (SetTheory.up (fun i=>(depth+i)%nat)) p.
Proof.
  unfold RenameStack.renamed. apply RenameMemoCallers.rename_extensional.
  intros [|i];cbn [under_binders SetTheory.up renaming];lia.
Qed.
Theorem generated_set_refines s bs ns fs classes cls variable depth reserve observations :
  (8<length (memory s arraydef_0__meta))%nat ->
  ClassStorage.represents s fs classes ->
  nth_error (memory s arraydef_0__classes) cls=Some (0,Z.of_nat variable) ->
  ns vardef_0__schemaShiftClass_cls=Z.of_nat cls -> ns vardef_0__schemaShiftClass_depth=Z.of_nat depth ->
  (0<depth)%nat -> Z.of_nat variable+Z.of_nat depth<=maximum ->
  Z.of_nat (length classes+S reserve)<=maximum ->
  let final:=SchemaClass.result (started s cls) (length classes) (0,Z.of_nat (variable+depth)) in
  execObserved (funcdef_0__schemaShiftClass bs ns) (s,observations)=Some (tt,(final,observations)) /\
  ClassStorage.represents final fs (classes++[Schemata.shifted_class depth (VirtualClasses.set variable)]) /\
  meta_value final 0=Z.of_nat (length classes) /\ meta_value final 8=meta_value s 8 /\
  Z.of_nat (length (classes++[Schemata.shifted_class depth (VirtualClasses.set variable)])+reserve)<=maximum /\
  stdin final=stdin s /\ stdout final=stdout s.
Proof.
  intros Hmeta Hclasses Hraw Hcls Hdepth Hpositive Hsum Hbudget final.
  assert (Hdecode:ClassStorage.decode fs (0,Z.of_nat (variable+depth))=
    Some (Schemata.shifted_class depth (VirtualClasses.set variable))).
  { unfold ClassStorage.decode. rewrite Nat2Z.id. cbn [Schemata.shifted_class]. f_equal. f_equal. lia. }
  split;[apply generated_set;try assumption;[exact (proj1 Hclasses)|lia]|].
  split;[apply SchemaClass.append_represents;[unfold started;rewrite store_meta_length;lia|now apply started_classes|exact Hdecode]|].
  split;[apply (proj1 (SchemaClass.result_values (started s cls) (length classes) (0,Z.of_nat (variable+depth)) ltac:(unfold started;rewrite store_meta_length;lia)))|].
  split;[unfold final;rewrite SchemaClass.result_meta_other by lia;unfold started;rewrite meta_store_other by lia;reflexivity|].
  split;[rewrite length_app;cbn [length];lia|]. split;reflexivity.
Qed.
Theorem generated_abstract_refines s bs ns fs classes cls root p depth bound reserve observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  ClassStorage.represents s fs classes ->
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
    stdin final=stdin s /\ stdout final=stdout s.
Proof.
  intros Hmeta Hsip Harena Htopology Herror Hclasses Hraw Hlookup Hfalse Hcls Hdepth Hpositive Hfuel Hbound Hindices Hheight Hbudget Hclassbudget.
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
  exists final,next. split.
  - apply (generated_abstract_helper s bs ns cls root depth (machine rframe) (length classes) observations);try assumption;
      [lia|exact (proj1 Hrclasses)|lia].
  - split;[now apply SchemaClass.result_arena|].
    split;[apply SchemaClass.append_represents;[lia|exact Hrclasses|exact Hdecode]|].
    split;[exact Hfinalmeta0|]. split;[unfold final;rewrite SchemaClass.result_meta_other by lia;exact Hrerror|].
    split;[exact Hrprefix|]. split;[now apply SchemaClass.result_topology|]. split;[exact Hrgrowth|].
    split;[rewrite length_app;cbn [length];lia|].
    destruct (proj2 (proj2 Hrframe)) as [Hinput Houtput]. split;[exact Hinput|exact Houtput].
Qed.
End SchemaShiftClass.
