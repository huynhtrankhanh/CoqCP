From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash Lift Observation Intern InternBounded InternGrowth FormulaEncoding Representation RenameStack RenameInvariant RenameRefinement PredicateExecution.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module PredicateRefinement.
Import IndexExecution SipHashExecution IndexSemantics.
Lemma rename_extensional p rho sigma : (forall i, rho i = sigma i) -> SetTheory.rename rho p = SetTheory.rename sigma p.
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IHp] in rho,sigma |- *; intros Heq; cbn [SetTheory.rename]; try reflexivity.
  - now rewrite !Heq.
  - now rewrite !Heq.
  - now rewrite IHp with (sigma:=sigma), IHq with (sigma:=sigma).
  - f_equal. apply IHp. intros [|i]; cbn [SetTheory.up]; [reflexivity|now rewrite Heq].
Qed.
Lemma predicate_renaming p shift arg :
  SetTheory.rename (renaming predicate_mode shift arg) p =
  VirtualClasses.predicate (VirtualClasses.abstract (VirtualClasses.core p)) (fun n => (n + shift)%nat) arg.
Proof. apply rename_extensional. intros [|i]; reflexivity. Qed.
Theorem generated_set_refines s bs ns fs cls variable shift arg observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 ->
  Z.of_nat (length fs) <= RenameInvariant.resource_limit ->
  ns vardef_0__predicate_cls = Z.of_nat cls -> ns vardef_0__predicate_shift = Z.of_nat shift -> ns vardef_0__predicate_arg = Z.of_nat arg ->
  (cls < length (memory s arraydef_0__classes))%nat ->
  nth_error (memory s arraydef_0__classes) cls = Some (0,Z.of_nat variable) ->
  word (Z.of_nat variable) -> word (Z.of_nat shift) -> word (Z.of_nat arg) -> word (Z.of_nat (variable + shift)) ->
  exists final next index, execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.predicate (VirtualClasses.set variable) (fun n => (n + shift)%nat) arg) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ (length next <= S (length fs))%nat.
Proof.
  intros Harena Herror Hcapacity Hcls Hshift Harg Hbound Hclass Hvariable Hshiftword Hargword Hsumword.
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
  exists final,next,index. split.
  - eapply PredicateExecution.generated_set with (cls:=Z.of_nat cls) (value:=Z.of_nat variable) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + now rewrite Nat2Z.id.
    + rewrite Nat2Z.id. exact (List.nth_error_nth _ _ (0,0) Hclass).
    + pose proof (proj1 (proj1 Harena)) as [Hmeta Hrest]. lia.
    + rewrite <-Nat2Z.inj_add. exact (proj2 Hsumword).
    + apply observed_plain; [apply InternalObservation.intern_nf|exact Hintern].
  - split; [exact Hnext|]. split; [exact Hindex|]. split; [unfold word; lia|]. split; [exact Hmeaning|].
    split; [exact Hextends|]. split; [exact Hflag|].
    exact (InternGrowth.at_most_one s final _ _ fs next Harena Herror Hcapacity Hintern Hnext).
Qed.
Theorem generated_abstract_refines s bs ns fs cls root p shift arg observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ns vardef_0__predicate_cls = Z.of_nat cls -> ns vardef_0__predicate_shift = Z.of_nat shift -> ns vardef_0__predicate_arg = Z.of_nat arg ->
  (cls < length (memory s arraydef_0__classes))%nat -> nth_error (memory s arraydef_0__classes) cls = Some (1,Z.of_nat root) ->
  nth_error fs root = Some p ->
  RenameInvariant.fits (renaming predicate_mode shift arg) 0 p -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  Z.of_nat (length fs + RenameStack.work p) <= RenameInvariant.resource_limit ->
  exists final next index, execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.predicate (VirtualClasses.abstract (VirtualClasses.core p)) (fun n => (n + shift)%nat) arg) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\ (length next <= length fs + RenameStack.work p)%nat.
Proof.
  intros Harena Hfalse Herror Hcls Hshift Harg Hbound Hclass Hlookup Hfits Hshiftword Hargword Hbudget.
  assert (Hroot : word (Z.of_nat root)) by (eapply RenameInvariant.word_id; eassumption).
  assert (Hrootlookup : nth_error fs (Z.to_nat (Z.of_nat root)) = Some p) by now rewrite Nat2Z.id.
  destruct (RenameRefinement.generated_rename s (fun _ => false) (PredicateExecution.rename_arguments (Z.of_nat root) (Z.of_nat shift) (Z.of_nat arg))
    fs p 0 predicate_mode shift arg observations Harena Hfalse Herror eq_refl eq_refl eq_refl Hroot Hrootlookup eq_refl Hfits Hshiftword Hargword Hbudget)
    as [final [next [index [Hrename [Hnext [Hindex [Hindexword [Hmeaning [Hextends [Hflag [Hempty Hgrowth]]]]]]]]]]].
  exists final,next,index. split.
  - eapply PredicateExecution.generated_abstract with (cls:=Z.of_nat cls) (value:=Z.of_nat root) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + now rewrite Nat2Z.id.
    + rewrite Nat2Z.id. exact (List.nth_error_nth _ _ (0,0) Hclass).
  - split; [exact Hnext|]. split; [exact Hindex|]. split; [exact Hindexword|]. split.
    + rewrite <-predicate_renaming. exact Hmeaning.
    + split; [exact Hextends|]. split; assumption.
Qed.
End PredicateRefinement.
