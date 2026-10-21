From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives PredicateRefinement ClassPredicate ClassEqualSets ClassLookup ClassStorage RenameStorage Representation RenameInvariant.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassMemberSet.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember.
Definition arguments cls variable : varsfuncdef_0__predicate -> Z :=
  update (update (update (fun _ => 0) vardef_0__predicate_cls cls) vardef_0__predicate_shift 0) vardef_0__predicate_arg variable.
Local Opaque funcdef_0__intern funcdef_0__predicate.
Theorem generated_body (f : Frame) final a b variable observations :
  nums f vardef_0__classMember_a = Z.of_nat a -> nums f vardef_0__classMember_b = Z.of_nat b ->
  (a < length (memory (machine f) arraydef_0__classes))%nat ->
  nth_error (memory (machine f) arraydef_0__classes) a = Some (0,variable) ->
  execObserved (funcdef_0__predicate (fun _=>false) (arguments (Z.of_nat b) variable)) (machine f,observations) = Some (tt,(final,observations)) ->
  execLocalObserved funcdef_0__classMember_body (f,observations) = Some (tt,(setMachine f final,observations)).
Proof.
  intros Ha Hb Habound Hrecord Hpredicate.
  pose proof (List.nth_error_nth _ _ (0,0) Hrecord) as Hnth.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__classMember_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id; exact Habound)
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in assert (Hsame : expression = (0,variable)) by exact Hnth; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__predicate ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__predicate bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(final,observations))) by exact Hpredicate; rewrite Hrun; clear Hrun end
    |progress rewrite Ha |progress rewrite Hb |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Theorem generated_helper s bs ns final a b variable observations :
  ns vardef_0__classMember_a = Z.of_nat a -> ns vardef_0__classMember_b = Z.of_nat b ->
  (a < length (memory s arraydef_0__classes))%nat -> nth_error (memory s arraydef_0__classes) a = Some (0,variable) ->
  execObserved (funcdef_0__predicate (fun _=>false) (arguments (Z.of_nat b) variable)) (s,observations) = Some (tt,(final,observations)) ->
  execObserved (funcdef_0__classMember bs ns) (s,observations) = Some (tt,(final,observations)).
Proof.
  intros Ha Hb Hbound Hrecord Hpredicate.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} final a b variable observations Ha Hb Hbound Hrecord Hpredicate) as Hbody.
  unfold Frame in Hbody. pose proof (eliminate_correct funcdef_0__classMember_body bs ns s observations) as Heliminate.
  rewrite Hbody in Heliminate. exact Heliminate.
Qed.
Lemma predicate_identity cls variable :
  VirtualClasses.predicate cls (fun n => (n + 0)%nat) variable = VirtualClasses.predicate cls (fun n=>n) variable.
Proof.
  destruct cls as [i|body]; cbn [VirtualClasses.predicate]; [now rewrite Nat.add_0_r|].
  apply PredicateRefinement.rename_extensional. intros [|i]; cbn [VirtualClasses.cons]; [reflexivity|now rewrite Nat.add_0_r].
Qed.
Theorem generated_refines s bs ns fs classes a b variable cls observations :
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0 = Some SetTheory.falsity -> meta_value s 8 = 0 ->
  ClassStorage.represents s fs classes -> ClassLookup.wellformed s ->
  nth_error classes a = Some (VirtualClasses.set variable) -> nth_error classes b = Some cls ->
  ns vardef_0__classMember_a = Z.of_nat a -> ns vardef_0__classMember_b = Z.of_nat b ->
  ClassPredicate.fits cls 0 variable -> Z.of_nat (length fs + ClassPredicate.work cls) <= RenameInvariant.resource_limit ->
  exists final next index, execObserved (funcdef_0__classMember bs ns) (s,observations) = Some (tt,(final,observations)) /\
    NativeRepresentation.canonical_arena final next /\ meta_value final 0 = Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index = Some (VirtualClasses.erase (VirtualClasses.class_member (VirtualClasses.set variable) cls)) /\
    (exists extra, next = fs ++ extra) /\ meta_value final 8 = 0 /\
    (length next <= length fs + ClassPredicate.work cls)%nat /\ RenameStorage.logical_frame s final /\
    ClassStorage.represents final next classes /\ ClassLookup.wellformed final.
Proof.
  intros Harena Hfalse Herror Hclasses Hwellformed Ha Hb Hna Hnb Hfits Hbudget.
  destruct (ClassEqualSets.set_lookup s fs classes a variable Hclasses Hwellformed Ha) as [Hbound [Hvariable Hrecord]].
  assert (Hzero : word 0) by (unfold word,maximum; lia).
  destruct (ClassPredicate.generated_refines s (fun _=>false) (arguments (Z.of_nat b) (Z.of_nat variable)) fs classes cls b 0 variable observations
    Harena Hfalse Herror Hclasses Hwellformed Hb eq_refl eq_refl eq_refl Hfits Hzero Hvariable Hbudget)
    as [final [next [index [Hpredicate [Hnext [Hindex [Hindexword [Hmeaning Hpost]]]]]]]].
  exists final,next,index. split.
  - eapply generated_helper; eassumption.
  - split; [exact Hnext|]. split; [exact Hindex|]. split; [exact Hindexword|]. split; [|exact Hpost].
    rewrite predicate_identity in Hmeaning. exact Hmeaning.
Qed.
End ClassMemberSet.
