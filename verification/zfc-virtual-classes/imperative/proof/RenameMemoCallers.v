From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash Lift FormulaTopology Representation RenameStack RenameStorage
  RenameMemoBounds RenameMemoResourceBounds RenameMemoIndexBounds RenameMemoInput RenameMemoTransition
  RenameMemoRun RenameMemoOutput RenameMemoControl PredicateExecution ObservedLocal Observation
  InternBounded InternGrowth FormulaEncoding Intern ClassStorage ClassLookup RenameMemoTopology RenameMemoArenaPrefix HashTable.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoCallers.
Import IndexExecution SipHashExecution IndexSemantics RenameMemoControl.
Lemma rename_extensional p rho sigma : (forall i, rho i=sigma i) -> SetTheory.rename rho p=SetTheory.rename sigma p.
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IHp] in rho,sigma|-*; intros Heq; cbn [SetTheory.rename]; try reflexivity.
  - now rewrite !Heq.
  - now rewrite !Heq.
  - now rewrite IHp with (sigma:=sigma),IHq with (sigma:=sigma).
  - f_equal. apply IHp. intros [|i]; cbn [SetTheory.up]; [reflexivity|now rewrite Heq].
Qed.
Theorem predicate_renaming p shift arg : SetTheory.rename (renaming predicate_mode shift arg) p=
  VirtualClasses.predicate (VirtualClasses.abstract (VirtualClasses.core p)) (fun n=>(n+shift)%nat) arg.
Proof. apply rename_extensional. intros [|i]; reflexivity. Qed.
Theorem predicate_checks bound shift arg :
  Z.of_nat bound+Z.of_nat shift<=maximum -> Z.of_nat bound+Z.of_nat arg<=maximum ->
  word (Z.of_nat shift) /\ word (Z.of_nat arg) /\
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment predicate_mode shift arg)<=maximum.
Proof.
  intros Hshift Harg. unfold word,RenameMemoIndexBounds.increment.
  destruct (Nat.le_ge_cases shift arg) as [Hle|Hle];
    [rewrite Nat.max_r by exact Hle|rewrite Nat.max_l by exact Hle]; repeat split; lia.
Qed.
Theorem shift_checks bound shift : Z.of_nat bound+Z.of_nat shift<=maximum ->
  word (Z.of_nat shift) /\ word (Z.of_nat 0) /\
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment shift_mode shift 0)<=maximum.
Proof. unfold word,RenameMemoIndexBounds.increment,maximum. intros. repeat split; lia. Qed.
Theorem instantiate_checks bound arg : Z.of_nat bound+Z.of_nat arg<=maximum ->
  word (Z.of_nat 0) /\ word (Z.of_nat arg) /\
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment instantiate_mode 0 arg)<=maximum.
Proof. unfold word,RenameMemoIndexBounds.increment,maximum. intros. repeat split; lia. Qed.
Theorem fixed_checks bound m :
  (m=separation_mode \/ m=replacement_left_mode \/ m=replacement_right_mode \/ m=replacement_image_mode) ->
  Z.of_nat bound+2<=maximum -> word (Z.of_nat 0) /\
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m 0 0)<=maximum.
Proof.
  intros [Hmode|[Hmode|[Hmode|Hmode]]] Hroom; subst m; unfold word,RenameMemoIndexBounds.increment,maximum in *; repeat split; lia.
Qed.
Theorem reserve_after initial current root reserve : (current<=initial+S root*S root)%nat ->
  Z.of_nat (initial+S root*S root+reserve)<=RenameMemoResourceBounds.doubling_limit ->
  Z.of_nat (current+reserve)<=RenameMemoResourceBounds.doubling_limit.
Proof. intros Hgrowth Hroom. lia. Qed.
Lemma predicate_arguments root shift arg :
  PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg) vardef_0__rename_node=Z.of_nat root /\
  PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg) vardef_0__rename_initialDepth=Z.of_nat 0 /\
  PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg) vardef_0__rename_mode=mode_number predicate_mode /\
  PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg) vardef_0__rename_shift=Z.of_nat shift /\
  PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg) vardef_0__rename_arg=Z.of_nat arg.
Proof.
  unfold PredicateExecution.rename_arguments. repeat split;
    repeat first [rewrite updated_same|rewrite updated_other by discriminate]; reflexivity.
Qed.
Theorem generated_abstract_predicate s bs ns fs cls root p shift arg bound observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs 0=Some SetTheory.falsity ->
  ns vardef_0__predicate_cls=Z.of_nat cls -> ns vardef_0__predicate_shift=Z.of_nat shift -> ns vardef_0__predicate_arg=Z.of_nat arg ->
  (cls<length (memory s arraydef_0__classes))%nat -> nth_error (memory s arraydef_0__classes) cls=Some (1,Z.of_nat root) ->
  nth_error fs root=Some p -> RenameMemoInput.input_bound s root bound ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  Z.of_nat bound+Z.of_nat shift<=maximum -> Z.of_nat bound+Z.of_nat arg<=maximum ->
  exists final next index, execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (VirtualClasses.predicate (VirtualClasses.abstract (VirtualClasses.core p)) (fun n=>(n+shift)%nat) arg) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\ meta_value final 10=0 /\
    (length next<=length fs+S root*S root)%nat /\ RenameStorage.logical_frame s final /\ FormulaTopology.ordered final (length next).
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Htopology Hfalse Hcls Hshift Harg Hclassbound Hclass Hlookup Hbound Hfuel Hroom Hshiftroom Hargroom.
  destruct (predicate_checks bound shift arg Hshiftroom Hargroom) as [Hshiftword [Hargword Hindices]].
  destruct (RenameMemoInput.canonical_source_bounds s fs root bound p Harena Htopology Hlookup Hbound) as [Hformula Hheight].
  assert (Hceiling : Z.of_nat (0+RenameMemoTransition.height p)<=maximum).
  { destruct (RenameMemoResourceBounds.grid_word root Hfuel) as [Hwidth [Hwidthword _]].
    change (Z.of_nat (S root)<maximum) in Hwidthword. lia. }
  destruct (predicate_arguments root shift arg) as [Hnode [Hbase [Hmode [Hrename_shift Hrename_arg]]]].
  destruct (RenameMemoRun.generated s (fun _=>false)
    (PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg)) fs p root 0 predicate_mode shift arg bound
    Hmeta Hsip Hpositive Herror Harena Htopology Hlookup Hfalse Hnode Hbase Hmode Hrename_shift Hrename_arg Hfuel Hroom
    Hshiftword Hargword Hformula Hindices Hceiling observations)
    as (finished & next & count & Hrename & Hnext & Hcache & Hword & Hmeaning & Hprefix & Hflag & Hempty & Hgrowth & Htopology_final).
  destruct (RenameMemoOutput.exported _ _ _ _ _ _ _ _ Hrename Hprefix) as [Hextends Hframe].
  exists (machine finished),next,(Z.to_nat (meta_value (machine finished) 0)). split.
  - eapply PredicateExecution.generated_abstract with (cls:=Z.of_nat cls) (value:=Z.of_nat root) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + now rewrite Nat2Z.id.
    + rewrite Nat2Z.id. exact (List.nth_error_nth _ _ (0,0) Hclass).
  - split; [exact Hnext|]. split; [now rewrite Z2Nat.id by exact (proj1 Hword)|].
    split; [now rewrite Z2Nat.id by exact (proj1 Hword)|]. split.
    + rewrite <-predicate_renaming. exact Hmeaning.
    + split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hempty|]. split; [exact Hgrowth|]. split; assumption.
Qed.
Theorem generated_set_predicate s bs ns fs cls variable shift arg observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8 = 0 ->
  Z.of_nat (length fs) <= RenameMemoResourceBounds.doubling_limit ->
  ns vardef_0__predicate_cls = Z.of_nat cls -> ns vardef_0__predicate_shift = Z.of_nat shift -> ns vardef_0__predicate_arg = Z.of_nat arg ->
  (cls < length (memory s arraydef_0__classes))%nat ->
  nth_error (memory s arraydef_0__classes) cls = Some (0,Z.of_nat variable) ->
  word (Z.of_nat variable) -> word (Z.of_nat shift) -> word (Z.of_nat arg) -> word (Z.of_nat (variable + shift)) ->
  exists final next index, execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.predicate (VirtualClasses.set variable) (fun n => (n + shift)%nat) arg) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ (length next <= S (length fs))%nat /\ RenameStorage.logical_frame s final /\ FormulaTopology.ordered final (length next).
Proof.
  intros Harena Htopology Herror Hcapacity Hcls Hshift Harg Hbound Hclass Hvariable Hshiftword Hargword Hsumword.
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
  exists final,next,index. split; [exact Hrun|].
  split; [exact Hnext|]. split; [exact Hindex|]. split; [unfold word; lia|]. split; [exact Hmeaning|].
    split; [exact Hextends|]. split; [exact Hflag|].
    split; [exact (InternGrowth.at_most_one s final _ _ fs next Harena Herror Hcapacity Hintern Hnext)|].
    split; [exact (RenameStorage.predicate_frame s bs ns final observations observations Hrun)|].
    eapply RenameMemoTopology.preserves; [exact Harena|exact Hnext|exact Hextends| |exact Htopology].
    exact (InternGrowth.at_most_one s final _ _ fs next Harena Herror Hcapacity Hintern Hnext).
Qed.
Definition predicate_ready s (fs : list SetTheory.formula) index shift arg :=
  match nth_error (memory s arraydef_0__classes) index with
  | Some (0,value)=> Z.of_nat (length fs)<=RenameMemoResourceBounds.doubling_limit /\
      word (Z.of_nat (Z.to_nat value+shift))
  | Some (1,value)=> let root:=Z.to_nat value in
      let bound:=RenameMemoInput.indices_max s (S root) in
      Z.of_nat (RenameMemoBounds.fuel root)<=maximum /\
      Z.of_nat (length fs)+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit /\
      Z.of_nat bound+Z.of_nat shift<=maximum /\ Z.of_nat bound+Z.of_nat arg<=maximum
  | _=>False end.
Definition predicate_growth (s : Machine) index := match nth_error (memory s arraydef_0__classes) index with
  | Some (0,_)=>1%nat | Some (1,value)=>let root:=Z.to_nat value in (S root*S root)%nat | _=>0%nat end.
Lemma predicate_growth_frame s t index : RenameStorage.logical_frame s t -> predicate_growth t index=predicate_growth s index.
Proof. intros [Harrays _]. unfold predicate_growth. now rewrite Harrays by (repeat split; discriminate). Qed.
Theorem indices_max_prefix s t fs next count : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena t next -> (exists extra,next=fs++extra) -> (count<=length fs)%nat ->
  RenameMemoInput.indices_max t count=RenameMemoInput.indices_max s count.
Proof.
  intros Harena Hnext [extra Hprefix]. rewrite Hprefix in Hnext.
  induction count as [|count IH]; intro Hcount; [reflexivity|]. cbn [RenameMemoInput.indices_max].
  rewrite IH by lia. now rewrite (RenameMemoArenaPrefix.canonical_prefix s t fs extra Harena Hnext count ltac:(lia)).
Qed.
Theorem generated_predicate s bs ns fs classes cls index shift arg observations :
  (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
  0<meta_value s 20 -> meta_value s 8=0 -> NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs 0=Some SetTheory.falsity ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s -> nth_error classes index=Some cls ->
  ns vardef_0__predicate_cls=Z.of_nat index -> ns vardef_0__predicate_shift=Z.of_nat shift -> ns vardef_0__predicate_arg=Z.of_nat arg ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) -> predicate_ready s fs index shift arg ->
  exists final next result, execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat result /\ word (Z.of_nat result) /\
    nth_error next result=Some (VirtualClasses.predicate cls (fun n=>(n+shift)%nat) arg) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\
    (length next<=length fs+predicate_growth s index)%nat /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final /\ FormulaTopology.ordered final (length next).
Proof.
  intros Hmeta Hsip Hpositive Herror Harena Htopology Hfalse Hclasses Hwellformed Hlookup Hindex Hshift Harg Hshiftword Hargword Hready.
  destruct (ClassLookup.lookup s fs classes index cls Hclasses Hwellformed Hlookup) as [Hclassbound Hclass].
  assert (Hresult : exists final next result,
    execObserved (funcdef_0__predicate bs ns) (s,observations)=Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0=Z.of_nat result /\ word (Z.of_nat result) /\
    nth_error next result=Some (VirtualClasses.predicate cls (fun n=>(n+shift)%nat) arg) /\
    (exists extra,next=fs++extra) /\ meta_value final 8=0 /\
    (length next<=length fs+predicate_growth s index)%nat /\ RenameStorage.logical_frame s final /\ FormulaTopology.ordered final (length next)).
  { destruct Hclass as [[variable [-> [Hvariable Hraw]]]|[root [p [-> [Hp Hraw]]]]].
    - unfold predicate_ready in Hready. rewrite Hraw,Nat2Z.id in Hready. destruct Hready as [Hcapacity Hsumword].
      destruct (generated_set_predicate s bs ns fs index variable shift arg observations Harena Htopology Herror Hcapacity Hindex Hshift Harg Hclassbound Hraw
        Hvariable Hshiftword Hargword Hsumword) as (final & next & result & Hrun & Hnext & Hvalue & Hword & Hmeaning & Hextends & Hflag & Hgrowth & Hframe & Htopology_final).
      exists final,next,result. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hword|].
      split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [|exact (conj Hframe Htopology_final)].
      unfold predicate_growth. rewrite Hraw. lia.
    - unfold predicate_ready in Hready. rewrite Hraw,Nat2Z.id in Hready. destruct Hready as [Hfuel [Hroom [Hshiftroom Hargroom]]].
      destruct (generated_abstract_predicate s bs ns fs index root p shift arg (RenameMemoInput.indices_max s (S root)) observations
        Hmeta Hsip Hpositive Herror Harena Htopology Hfalse Hindex Hshift Harg Hclassbound Hraw Hp
        (RenameMemoInput.computed_input_bound s root) Hfuel Hroom Hshiftroom Hargroom)
        as (final & next & result & Hrun & Hnext & Hvalue & Hword & Hmeaning & Hextends & Hflag & Hempty & Hgrowth & Hframe & Htopology_final).
      exists final,next,result. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hword|].
      split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [|exact (conj Hframe Htopology_final)].
      unfold predicate_growth. now rewrite Hraw,Nat2Z.id.
  }
  destruct Hresult as (final & next & result & Hrun & Hnext & Hvalue & Hword & Hmeaning & Hextends & Hflag & Hgrowth & Hframe & Htopology_final).
  exists final,next,result. split; [exact Hrun|]. split; [exact Hnext|]. split; [exact Hvalue|]. split; [exact Hword|].
  split; [exact Hmeaning|]. split; [exact Hextends|]. split; [exact Hflag|]. split; [exact Hgrowth|]. split; [exact Hframe|]. split.
  - destruct Hextends as [extra ->]. exact (RenameStorage.classes_transport s final fs extra classes Hframe Hclasses).
  - split; [now apply (ClassLookup.frame_wellformed s final)|exact Htopology_final].
Qed.
End RenameMemoCallers.
