From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives FormulaCircuit Intern Representation ClassMemberCircuit RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoClassMemberRaw.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoControl.
Definition plan:=ClassMemberCircuit.plan.
Definition values:=ClassMemberCircuit.values.
Definition predicate_arguments cls shift : varsfuncdef_0__predicate->Z :=
  update (update (update (fun _=>0) vardef_0__predicate_cls cls) vardef_0__predicate_shift shift) vardef_0__predicate_arg 0.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classMember.
Local Opaque funcdef_0__intern funcdef_0__predicate Imperative.update.
Theorem generated_general (f : Frame) first second final ids a b tag_a value_a left right observations :
  nums f vardef_0__classMember_a=Z.of_nat a -> nums f vardef_0__classMember_b=Z.of_nat b ->
  (a<length (memory (machine f) arraydef_0__classes))%nat ->
  nth_error (memory (machine f) arraydef_0__classes) a=Some (tag_a,value_a) -> tag_a<>0 ->
  execObserved (funcdef_0__predicate (fun _=>false) (predicate_arguments (Z.of_nat a) 2))
    (machine f,observations)=Some (tt,(first,observations)) ->
  (0<length (memory first arraydef_0__meta))%nat -> meta_value first 0=left ->
  execObserved (funcdef_0__predicate (fun _=>false) (predicate_arguments (Z.of_nat b) 1))
    (first,observations)=Some (tt,(second,observations)) ->
  (0<length (memory second arraydef_0__meta))%nat -> meta_value second 0=right ->
  FormulaCircuit.executes observations plan second [0;left;right] final ids ->
  optionBind (execLocalObserved funcdef_0__classMember_body (f,observations))
    (fun r=>Some (tt,(machine (fst (snd r)),snd (snd r))))=
    Some (tt,(store_meta final 0 (meta_value final 0),observations)).
Proof.
  intros Ha Hb Habound Hrecord_a Hnonsets Hfirst Hfirstmeta Hleft Hsecond Hsecondmeta Hright Htrace.
  pose proof (List.nth_error_nth _ _ (0,0) Hrecord_a) as Hnth_a.
  unfold plan,ClassMemberCircuit.plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  destruct f as [s bs ns]; cbn [machine nums] in *; unfold funcdef_0__classMember_body.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       |arraydef_0__classes => exact Habound
       |arraydef_0__meta => replace (Z.to_nat 0) with 0%nat by reflexivity; assumption end)
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in assert (Hsame : expression = (tag_a,value_a)) by exact Hnth_a; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__predicate ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__predicate bi ni) state) in
       let Hrun := fresh in first
         [assert (Hrun : expression = Some (tt,(first,observations))) by exact Hfirst
         |assert (Hrun : expression = Some (tt,(second,observations))) by exact Hsecond]; rewrite Hrun; clear Hrun end
    |match goal with H : execObserved (funcdef_0__intern _ _) _ = Some (tt,(?after,?trace)) |-
         context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(after,trace))) by exact H; rewrite Hrun; clear Hrun end
    |progress rewrite Ha |progress rewrite Hb |progress rewrite Nat2Z.id
    |match goal with H : meta_value ?source 0 = ?value |- context [meta_value ?source 0] => progress rewrite H end
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. all: reflexivity.
Qed.
Lemma result_semantics observations s left right final ids next p q :
  FormulaCircuit.executes observations plan s [0;left;right] final ids ->
  FormulaCircuit.represents next ids (values p q) ->
  word (meta_value final 0) /\ nth_error next (Z.to_nat (meta_value final 0)) = Some (ClassMemberCircuit.result p q).
Proof.
  intros Htrace Hrep. pose proof (FormulaCircuit.wire next ids (values p q) 15 (ClassMemberCircuit.result p q) Hrep eq_refl) as Hwire.
  unfold plan,ClassMemberCircuit.plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire.
  exact Hwire.
Qed.
End RenameMemoClassMemberRaw.
