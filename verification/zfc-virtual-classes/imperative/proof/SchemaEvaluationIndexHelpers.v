From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash Lift FormulaTopology Representation RenameStack RenameStorage
  RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoInput RenameMemoTransition
  RenameMemoRun RenameMemoOutput RenameMemoControl PredicateExecution ObservedLocal Observation
  InternBounded InternGrowth FormulaEncoding Intern ClassStorage ClassLookup RenameMemoTopology RenameMemoArenaPrefix HashTable RenameMemoCallers RenameMemoIndexRun SchemaEvaluationIndexBounds Intern.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexHelpers.
Import IndexExecution SipHashExecution IndexSemantics RenameMemoControl RenameMemoCallers.
Theorem generated_abstract_predicate s bs ns fs cls root p shift arg bound observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__predicate_cls=Z.of_nat cls -> ns vardef_0__predicate_shift=Z.of_nat shift -> ns vardef_0__predicate_arg=Z.of_nat arg ->
  (cls<length (memory s arraydef_0__classes))%nat -> nth_error (memory s arraydef_0__classes) cls=Some (1,Z.of_nat root) ->
  nth_error fs root=Some p -> RenameMemoInput.input_bound s root bound ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  Z.of_nat bound+Z.of_nat shift<=maximum -> Z.of_nat bound+Z.of_nat arg<=maximum ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+Nat.max shift arg) /\
    execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (VirtualClasses.predicate (VirtualClasses.abstract (VirtualClasses.core p)) (fun n=>(n+shift)%nat) arg) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 10=0 /\
    (length next<=length fs+S root*S root)%nat /\ RenameStorage.logical_frame s final /\ FormulaTopology.ordered final (length next).
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Htopology Hfalse Hcls Hshift Harg Hclassbound Hclass Hlookup Hbound HrawInitial Hfuel Hroom Hshiftroom Hargroom.
  destruct (predicate_checks bound shift arg Hshiftroom Hargroom) as [Hshiftword [Hargword Hindices]].
  destruct (RenameMemoInput.canonical_source_bounds s fs root bound p Harena Htopology Hlookup Hbound) as [Hformula Hheight].
  assert (Hceiling : Z.of_nat (0+RenameMemoTransition.height p)<=maximum).
  { destruct (RenameMemoResourceBounds.grid_word root Hfuel) as [Hwidth [Hwidthword _]].
    change (Z.of_nat (S root)<maximum) in Hwidthword. lia. }
  destruct (predicate_arguments root shift arg) as [Hnode [Hbase [Hmode [Hrename_shift Hrename_arg]]]].
  destruct (RenameMemoIndexRun.generated_bounded s (fun _=>false)
    (PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg)) fs p root 0 predicate_mode shift arg bound
    Hmeta Hsip Hpositive Herror Harena Htopology Hlookup Hfalse Hnode Hbase Hmode Hrename_shift Hrename_arg Hfuel Hroom
    Hshiftword Hargword HrawInitial Hindices Hceiling observations)
    as (finished & next & count & Hrename & Hnext & Hcache & Hword & Hmeaning & Hprefix & Hflag & Hempty & Hgrowth & Htopology_final & Hfinalraw).
  destruct (RenameMemoOutput.exported _ _ _ _ _ _ _ _ Hrename Hprefix) as [Hextends Hframe].
  exists (machine finished),next,(Z.to_nat (meta_value (machine finished) 0)). split; [exact Hfinalraw|]. split.
  - eapply PredicateExecution.generated_abstract with (cls:=Z.of_nat cls) (value:=Z.of_nat root) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + now rewrite Nat2Z.id.
    + rewrite Nat2Z.id. exact (List.nth_error_nth _ _ (0,0) Hclass).
  - split; [exact Hnext|]. split; [now rewrite Z2Nat.id by exact (proj1 Hword)|].
    split; [now rewrite Z2Nat.id by exact (proj1 Hword)|]. split.
    + rewrite <-predicate_renaming. exact Hmeaning.
    + split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hempty|]. split; [exact Hgrowth|]. split; assumption.
Qed.
Theorem generated_set_predicate s bs ns fs cls variable shift arg bound observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8 = 0 ->
  Z.of_nat (length fs) <= RenameMemoResourceBounds.doubling_limit ->
  ns vardef_0__predicate_cls = Z.of_nat cls -> ns vardef_0__predicate_shift = Z.of_nat shift -> ns vardef_0__predicate_arg = Z.of_nat arg ->
  (cls < length (memory s arraydef_0__classes))%nat ->
  nth_error (memory s arraydef_0__classes) cls = Some (0,Z.of_nat variable) ->
  word (Z.of_nat variable) -> word (Z.of_nat shift) -> word (Z.of_nat arg) -> word (Z.of_nat (variable + shift)) ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound -> (variable<=bound)%nat ->
  exists final next index, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+Nat.max shift arg) /\
    execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.predicate (VirtualClasses.set variable) (fun n => (n + shift)%nat) arg) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ (length next <= S (length fs))%nat /\ RenameStorage.logical_frame s final /\ FormulaTopology.ordered final (length next).
Proof.
  intros Harena Htopology Herror Hcapacity Hcls Hshift Harg Hbound Hclass Hvariable Hshiftword Hargword Hsumword HrawInitial HvariableBound.
  set (arguments := PredicateExecution.intern_arguments (Z.of_nat arg) (Z.of_nat variable) (Z.of_nat shift)).
  assert (Hsum : coerceInt (Z.of_nat variable + Z.of_nat shift) 64 = Z.of_nat (variable + shift))
    by (rewrite <-Nat2Z.inj_add; now apply coerce_word).
  assert (Hnormal : FormulaEncoding.normal (arguments vardef_0__intern_tag,arguments vardef_0__intern_a,arguments vardef_0__intern_b)).
  { change (FormulaEncoding.normal (2,Z.of_nat arg,coerceInt (Z.of_nat variable+Z.of_nat shift) 64)).
    rewrite Hsum. right. left. split; [right; left; reflexivity|auto]. }
  assert (Hdecode : FormulaEncoding.decode fs (arguments vardef_0__intern_tag,arguments vardef_0__intern_a,arguments vardef_0__intern_b) = Some (SetTheory.member arg (variable + shift))).
  { change (FormulaEncoding.decode fs (2,Z.of_nat arg,coerceInt (Z.of_nat variable+Z.of_nat shift) 64) = Some (SetTheory.member arg (variable + shift))).
    rewrite Hsum. cbn [FormulaEncoding.decode]. now rewrite !Nat2Z.id. }
  destruct (InternBounded.generated_refines s (fun _ => false) arguments fs (SetTheory.member arg (variable+shift)) Harena Herror Hcapacity Hnormal Hdecode)
    as [final [next [index [Hintern [Hframe [Hflag [Hindex [Hindexword [Hnext [Hmeaning Hextends]]]]]]]]]].
  assert (Hrun : execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations))).
  { eapply PredicateExecution.generated_set with (cls:=Z.of_nat cls) (value:=Z.of_nat variable) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + now rewrite Nat2Z.id.
    + rewrite Nat2Z.id. exact (List.nth_error_nth _ _ (0,0) Hclass).
    + pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest]. lia.
    + rewrite <-Nat2Z.inj_add. exact (proj2 Hsumword).
    + apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern].
  }
  assert (HrawFinal:SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+Nat.max shift arg)).
  { eapply (SchemaEvaluationIndexBounds.observed_intern s final (fun _=>false) arguments fs next (bound+Nat.max shift arg) observations observations);
      try eassumption.
    - exact (SchemaEvaluationIndexBounds.raw_arena_mono s (length fs) bound (bound+Nat.max shift arg) ltac:(lia) HrawInitial).
    - change (RenameMemoInput.raw_bound (bound+Nat.max shift arg) (2,Z.of_nat arg,coerceInt (Z.of_nat variable+Z.of_nat shift) 64)).
      rewrite Hsum. unfold RenameMemoInput.raw_bound. intros _. rewrite !Nat2Z.id. split;lia.
    - apply observed_plain;[apply InternalObservation.intern_nf|exact Hintern]. }
  exists final,next,index. split;[exact HrawFinal|]. split; [exact Hrun|].
  split; [exact Hnext|]. split; [exact Hindex|]. split; [unfold word; lia|]. split; [exact Hmeaning|].
    split; [exact Hextends|]. split; [exact Hflag|].
    split; [exact (InternGrowth.at_most_one s final _ _ fs next Harena Herror Hcapacity Hintern Hnext)|].
    split; [exact (RenameStorage.predicate_frame s bs ns final observations observations Hrun)|].
    eapply RenameMemoTopology.preserves; [exact Harena|exact Hnext|exact Hextends| |exact Htopology].
    exact (InternGrowth.at_most_one s final _ _ fs next Harena Herror Hcapacity Hintern Hnext).
Qed.
Theorem generated_predicate s bs ns fs classes cls index shift arg bound observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs 0=Some SetTheory.falsity ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s -> nth_error classes index=Some cls ->
  ns vardef_0__predicate_cls=Z.of_nat index -> ns vardef_0__predicate_shift=Z.of_nat shift -> ns vardef_0__predicate_arg=Z.of_nat arg ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) -> predicate_ready s fs index shift arg ->
  SchemaEvaluationIndexBounds.raw_arena s (length fs) bound -> SchemaEvaluationIndexBounds.class_bound bound cls ->
  Z.of_nat bound+Z.of_nat (Nat.max shift arg)<=maximum ->
  exists final next result, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+Nat.max shift arg) /\ execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat result /\ word (Z.of_nat result) /\
    nth_error next result=Some (VirtualClasses.predicate cls (fun n=>(n+shift)%nat) arg) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\
    (length next<=length fs+predicate_growth s index)%nat /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\ FormulaTopology.ordered final (length next).
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Htopology Hfalse Hclasses Hwellformed Hlookup Hindex Hshift Harg Hshiftword Hargword Hready HrawInitial HclsBound HglobalRoom.
  destruct (ClassLookup.lookup s fs classes index cls Hclasses Hwellformed Hlookup) as [Hclassbound Hclass].
  assert (Hresult : exists final next result, SchemaEvaluationIndexBounds.raw_arena final (length next) (bound+Nat.max shift arg) /\
    execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat result /\ word (Z.of_nat result) /\
    nth_error next result=Some (VirtualClasses.predicate cls (fun n=>(n+shift)%nat) arg) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\
    (length next<=length fs+predicate_growth s index)%nat /\ RenameStorage.logical_frame s final /\ FormulaTopology.ordered final (length next)).
  { destruct Hclass as [[variable [-> [Hvariable Hraw]]]|[root [p [-> [Hp Hraw]]]]].
    - unfold predicate_ready in Hready. rewrite Hraw,Nat2Z.id in Hready. destruct Hready as [Hcapacity Hsumword].
      destruct (generated_set_predicate s bs ns fs index variable shift arg bound observations Harena Htopology Herror Hcapacity Hindex Hshift Harg Hclassbound Hraw
        Hvariable Hshiftword Hargword Hsumword HrawInitial HclsBound) as (final & next & result & Hfinalraw & Hrun & Hnext & Hvalue & Hword & Hmeaning & Hextends & Hflag & Hgrowth & Hframe & Htopology_final).
      exists final,next,result. split;[exact Hfinalraw|]. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hword|].
      split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [|exact (conj Hframe Htopology_final)].
      unfold predicate_growth. rewrite Hraw. lia.
    - unfold predicate_ready in Hready. rewrite Hraw,Nat2Z.id in Hready. destruct Hready as [Hfuel [Hroom [Hshiftroom Hargroom]]].
      destruct (generated_abstract_predicate s bs ns fs index root p shift arg bound observations
        Hmeta Hsip Hpositive Herror Harena Htopology Hfalse Hindex Hshift Harg Hclassbound Hraw Hp
        ltac:(intros node Hnode;apply HrawInitial;assert (Hroot:(root<length fs)%nat) by (apply nth_error_Some;congruence);lia)
        HrawInitial Hfuel Hroom ltac:(pose proof (Nat.le_max_l shift arg);lia) ltac:(pose proof (Nat.le_max_r shift arg);lia))
        as (final & next & result & Hfinalraw & Hrun & Hnext & Hvalue & Hword & Hmeaning & Hextends & Hflag & Hempty & Hgrowth & Hframe & Htopology_final).
      exists final,next,result. split;[exact Hfinalraw|]. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hword|].
      split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [|exact (conj Hframe Htopology_final)].
      unfold predicate_growth. now rewrite Hraw,Nat2Z.id.
  }
  destruct Hresult as (final & next & result & Hfinalraw & Hrun & Hnext & Hvalue & Hword & Hmeaning & Hextends & Hflag & Hgrowth & Hframe & Htopology_final).
  exists final,next,result. split;[exact Hfinalraw|]. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hword|].
  split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hgrowth|]. split; [exact Hframe|]. split.
  - destruct Hextends as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hframe Hclasses).
  - split; [now apply (ClassLookup.frame_wellformed s final)|exact Htopology_final].
Qed.
End SchemaEvaluationIndexHelpers.
