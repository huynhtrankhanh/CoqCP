From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives InternTail ClassStorage ClassLookup FormulaProjection
  Representation FormulaTopology HashTable RenameMemoControl.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaClass.
Import IndexExecution SipHashExecution ObservedLocal.
Definition result s n entry := store_meta (store_meta (ClassStorage.written s n entry) 0 (Z.of_nat n)) 2 (Z.of_nat (S n)).
Definition arguments kind value : varsfuncdef_0__schemaClass -> Z :=
  update (update (fun _=>0) vardef_0__schemaClass_kind kind) vardef_0__schemaClass_value value.
Lemma result_meta_length s n entry : length (memory (result s n entry) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof. unfold result. rewrite !store_meta_length,ClassStorage.written_other by discriminate. reflexivity. Qed.
Lemma result_other s n entry name : name<>arraydef_0__meta -> name<>arraydef_0__classes ->
  memory (result s n entry) name=memory s name.
Proof. intros Hm Hc. unfold result. rewrite !store_meta_other by exact Hm. now apply ClassStorage.written_other. Qed.
Lemma result_classes s n entry : memory (result s n entry) arraydef_0__classes=memory (ClassStorage.written s n entry) arraydef_0__classes.
Proof. unfold result. now rewrite !store_meta_other by discriminate. Qed.
Lemma result_meta_other s n entry slot : slot<>0%nat -> slot<>2%nat -> meta_value (result s n entry) slot=meta_value s slot.
Proof. intros H0 H2. unfold result. rewrite !meta_store_other by assumption. apply ClassStorage.written_meta. Qed.
Lemma result_values s n entry : (2<length (memory s arraydef_0__meta))%nat ->
  meta_value (result s n entry) 0=Z.of_nat n /\ meta_value (result s n entry) 2=Z.of_nat (S n).
Proof.
  intro Hmeta. unfold result. split.
  - rewrite meta_store_other by lia. apply meta_store_same. rewrite ClassStorage.written_other by discriminate. lia.
  - apply meta_store_same. rewrite store_meta_length,ClassStorage.written_other by discriminate. exact Hmeta.
Qed.
Lemma result_io s n entry : stdin (result s n entry)=stdin s /\ stdout (result s n entry)=stdout s.
Proof. split;reflexivity. Qed.
Lemma result_projection s n entry : FormulaProjection.storage s (result s n entry).
Proof.
  split;[apply result_meta_length|]. split.
  - intros name Hneeded. unfold FormulaProjection.needed in Hneeded.
    destruct Hneeded as [Heq|[Heq|[Heq|Heq]]];subst name;apply result_other;discriminate.
  - repeat split;apply result_meta_other;lia.
Qed.
Lemma result_arena s n entry fs : NativeRepresentation.canonical_arena s fs -> NativeRepresentation.canonical_arena (result s n entry) fs.
Proof. intro H. eapply FormulaProjection.storage_arena;[apply result_projection|exact H]. Qed.
Lemma result_topology s n entry count : FormulaTopology.ordered s count -> FormulaTopology.ordered (result s n entry) count.
Proof.
  intros Htop parent child Hparent Hchild. apply Htop;[exact Hparent|].
  unfold HashTableInvariant.tuple_at in *. now rewrite result_other in Hchild by discriminate.
Qed.
Lemma append_represents s fs classes entry cls :
  (2<length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s fs classes ->
  ClassStorage.decode fs entry=Some cls -> ClassStorage.represents (result s (length classes) entry) fs (classes++[cls]).
Proof.
  intros Hmeta [Hcount Hclasses] Hdecode. split.
  - rewrite (proj2 (result_values s (length classes) entry Hmeta)),length_app. cbn [length]. f_equal. lia.
  - rewrite result_classes,ClassStorage.written_app by (now apply Forall2_length in Hclasses).
    apply Forall2_app;[exact Hclasses|]. constructor;[exact Hdecode|constructor].
Qed.
Lemma append_wellformed s fs classes entry : ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  word (snd entry) -> ClassLookup.wellformed (result s (length classes) entry).
Proof.
  intros Hrep Hgood Hword. unfold ClassLookup.wellformed. rewrite result_classes,ClassStorage.written_app by
    (now apply ClassStorage.represents_length in Hrep). apply Forall_app. split;[exact Hgood|]. constructor;[exact Hword|constructor].
Qed.
Local Opaque Imperative.update.
Theorem generated_helper s bs ns n kind value observations :
  (8<length (memory s arraydef_0__meta))%nat -> meta_value s 2=Z.of_nat n -> Z.of_nat n<maximum ->
  ns vardef_0__schemaClass_kind=kind -> ns vardef_0__schemaClass_value=value ->
  execObserved (funcdef_0__schemaClass bs ns) (s,observations)=Some (tt,(result s n (kind,value),observations)).
Proof.
  intros Hmeta Hcount Hword Hkind Hvalue.
  assert (Hnext:coerceInt (Z.of_nat n+1) 64=Z.of_nat (S n)).
  { rewrite coerce_word by (unfold word;lia). lia. }
  unfold maximum in Hword. unfold funcdef_0__schemaClass. rewrite eliminate_correct. unfold funcdef_0__schemaClass_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress unfold addInt at 1
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine setNum];
       repeat first [rewrite store_meta_length|rewrite ClassStorage.written_other by discriminate
         |progress unfold ClassStorage.grown|progress cbn [withMemory memory]
         |rewrite growArrays_other by discriminate|rewrite InternTailExecution.modify_other by discriminate
         |rewrite growArrays_same|rewrite growList_length|rewrite Nat2Z.id];lia)
    |progress fold (ClassStorage.grown s n)
    |progress change (withMemory (ClassStorage.grown s n)
        (modifyArray (memory (ClassStorage.grown s n)) arraydef_0__classes n (kind,value)))
      with (ClassStorage.written s n (kind,value))
    |progress rewrite Hkind|progress rewrite Hvalue|progress rewrite Hcount|progress rewrite Hnext|progress rewrite Nat2Z.id
    |progress rewrite ClassStorage.grown_meta|progress rewrite ClassStorage.written_meta
    |progress rewrite meta_store_other by lia
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 2) with 2%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by lia|progress rewrite (bool_decide_false P) by lia] end
    |match goal with |- context [decide ?P] => first
      [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
Theorem generated_overflow s bs ns observations :
  (8<length (memory s arraydef_0__meta))%nat -> meta_value s 2=maximum ->
  execObserved (funcdef_0__schemaClass bs ns) (s,observations)=Some (tt,(store_meta s 8 1,observations)).
Proof.
  intros Hmeta Hcount. unfold maximum in Hcount. unfold funcdef_0__schemaClass.
  rewrite eliminate_correct. unfold funcdef_0__schemaClass_body.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];lia)
    |progress replace (Z.to_nat 2) with 2%nat by reflexivity
    |progress rewrite Hcount
    |match goal with |- context [bool_decide ?P] => progress rewrite (bool_decide_true P) by reflexivity end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
Theorem generated_refines s bs ns fs classes kind value cls reserve observations :
  (8<length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s fs classes ->
  ns vardef_0__schemaClass_kind=kind -> ns vardef_0__schemaClass_value=value ->
  ClassStorage.decode fs (kind,value)=Some cls ->
  Z.of_nat (length classes+S reserve)<=maximum ->
  execObserved (funcdef_0__schemaClass bs ns) (s,observations)=
    Some (tt,(result s (length classes) (kind,value),observations)) /\
  ClassStorage.represents (result s (length classes) (kind,value)) fs (classes++[cls]) /\
  meta_value (result s (length classes) (kind,value)) 0=Z.of_nat (length classes) /\
  Z.of_nat (length (classes++[cls])+reserve)<=maximum.
Proof.
  intros Hmeta Hrep Hkind Hvalue Hdecode Hbudget. split.
  - apply generated_helper;try assumption;[exact (proj1 Hrep)|lia].
  - split;[apply append_represents;try assumption;lia|]. split.
    + apply (proj1 (result_values s (length classes) (kind,value) ltac:(lia))).
    + rewrite length_app. cbn [length]. lia.
Qed.
End SchemaClass.
