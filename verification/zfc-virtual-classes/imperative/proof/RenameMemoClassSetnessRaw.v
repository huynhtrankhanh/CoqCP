From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives FormulaCircuit Intern Representation RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoClassSetnessRaw.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoControl.
Definition plan := [FormulaCircuit.member 0 1; FormulaCircuit.implies 2 1; FormulaCircuit.implies 1 2;
  FormulaCircuit.implies 4 0; FormulaCircuit.implies 3 5; FormulaCircuit.implies 6 0; FormulaCircuit.all 7;
  FormulaCircuit.implies 8 0; FormulaCircuit.all 9; FormulaCircuit.implies 10 0].
Definition result p := SetTheory.ex (SetTheory.all (SetTheory.iff (SetTheory.member 0 1) p)).
Definition values p := [SetTheory.falsity;p; SetTheory.member 0 1;
  SetTheory.implies (SetTheory.member 0 1) p; SetTheory.implies p (SetTheory.member 0 1);
  SetTheory.neg (SetTheory.implies p (SetTheory.member 0 1));
  SetTheory.implies (SetTheory.implies (SetTheory.member 0 1) p) (SetTheory.neg (SetTheory.implies p (SetTheory.member 0 1)));
  SetTheory.iff (SetTheory.member 0 1) p; SetTheory.all (SetTheory.iff (SetTheory.member 0 1) p);
  SetTheory.neg (SetTheory.all (SetTheory.iff (SetTheory.member 0 1) p));
  SetTheory.all (SetTheory.neg (SetTheory.all (SetTheory.iff (SetTheory.member 0 1) p))); result p].
Lemma infer p : FormulaCircuit.infer plan [SetTheory.falsity;p]=Some (values p).
Proof. reflexivity. Qed.
Lemma fits : Forall FormulaCircuit.fits plan.
Proof. repeat constructor; unfold word,maximum; lia. Qed.
Definition predicate_arguments cls shift : varsfuncdef_0__predicate->Z :=
  update (update (update (fun _=>0) vardef_0__predicate_cls cls) vardef_0__predicate_shift shift) vardef_0__predicate_arg 0.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__setness.
Local Opaque funcdef_0__intern funcdef_0__predicate Imperative.update.
Definition set_plan variable := [FormulaCircuit.equal 0 (S variable); FormulaCircuit.implies 1 0; FormulaCircuit.all 2; FormulaCircuit.implies 3 0].
Definition set_values variable := [SetTheory.falsity;SetTheory.equal 0 (S variable); SetTheory.neg (SetTheory.equal 0 (S variable));
  SetTheory.all (SetTheory.neg (SetTheory.equal 0 (S variable))); SetTheory.ex (SetTheory.equal 0 (S variable))].
Lemma set_infer variable : FormulaCircuit.infer (set_plan variable) [SetTheory.falsity]=Some (set_values variable).
Proof. reflexivity. Qed.
Lemma set_fits variable : word (Z.of_nat (S variable)) -> Forall FormulaCircuit.fits (set_plan variable).
Proof. intro Hword. unfold set_plan. constructor; [split; [unfold word,maximum; lia|exact Hword]|]. repeat constructor. Qed.
Theorem generated_set (f : Frame) final ids a variable observations :
  nums f vardef_0__setness_cls=Z.of_nat a ->
  (a<length (memory (machine f) arraydef_0__classes))%nat ->
  nth_error (memory (machine f) arraydef_0__classes) a=Some (0,Z.of_nat variable) ->
  (8<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  word (Z.of_nat (S variable)) ->
  FormulaCircuit.executes observations (set_plan variable) (machine f) [0] final ids ->
  optionBind (execLocalObserved funcdef_0__setness_body (f,observations))
    (fun r=>Some (tt,(machine (fst (snd r)),snd (snd r))))=
    Some (tt,(store_meta final 0 (meta_value final 0),observations)).
Proof.
  intros Ha Habound Hrecord_a Hmeta Herror Hsuccessor Htrace.
  assert (Hnotmax : Z.of_nat variable <> 18446744073709551615) by
    (unfold word,maximum in Hsuccessor; rewrite Nat2Z.inj_succ in Hsuccessor; lia).
  assert (Hadd : coerceInt (Z.of_nat variable+1) 64=Z.of_nat (S variable)) by
    (replace (Z.of_nat variable+1) with (Z.of_nat (S variable)) by lia; apply coerce_word; exact Hsuccessor).
  pose proof (List.nth_error_nth _ _ (0,0) Hrecord_a) as Hnth_a.
  unfold set_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  destruct f as [s bs ns]; cbn [machine nums] in *; unfold funcdef_0__setness_body.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       |arraydef_0__classes => exact Habound
       |arraydef_0__meta => first [exact Hmeta|replace (Z.to_nat 0) with 0%nat by reflexivity; assumption] end)
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in assert (Hsame : expression = (0,Z.of_nat variable)) by exact Hnth_a; rewrite Hsame; clear Hsame end
    |match goal with H : execObserved (funcdef_0__intern _ _) _ = Some (tt,(?after,?trace)) |-
         context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(after,trace))) by exact H; rewrite Hrun; clear Hrun end
    |progress rewrite Ha |progress rewrite Nat2Z.id |progress rewrite Herror |progress rewrite Hadd
    |match goal with H : meta_value ?source 0 = ?value |- context [meta_value ?source 0] => progress rewrite H end
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools addInt]
  ]. all: reflexivity.
Qed.
Lemma set_result_semantics observations s final ids next variable :
  FormulaCircuit.executes observations (set_plan variable) s [0] final ids ->
  FormulaCircuit.represents next ids (set_values variable) ->
  word (meta_value final 0) /\ nth_error next (Z.to_nat (meta_value final 0)) = Some (SetTheory.ex (SetTheory.equal 0 (S variable))).
Proof.
  intros Htrace Hrep. pose proof (FormulaCircuit.wire next ids (set_values variable) 4 (SetTheory.ex (SetTheory.equal 0 (S variable))) Hrep eq_refl) as Hwire.
  unfold set_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire. exact Hwire.
Qed.
Theorem generated_general (f : Frame) first final ids a tag_a value_a left observations :
  nums f vardef_0__setness_cls=Z.of_nat a ->
  (a<length (memory (machine f) arraydef_0__classes))%nat ->
  nth_error (memory (machine f) arraydef_0__classes) a=Some (tag_a,value_a) -> tag_a<>0 ->
  execObserved (funcdef_0__predicate (fun _=>false) (predicate_arguments (Z.of_nat a) 2))
    (machine f,observations)=Some (tt,(first,observations)) ->
  (0<length (memory first arraydef_0__meta))%nat -> meta_value first 0=left ->
  FormulaCircuit.executes observations plan first [0;left] final ids ->
  optionBind (execLocalObserved funcdef_0__setness_body (f,observations))
    (fun r=>Some (tt,(machine (fst (snd r)),snd (snd r))))=
    Some (tt,(store_meta final 0 (meta_value final 0),observations)).
Proof.
  intros Ha Habound Hrecord_a Hnonsets Hfirst Hfirstmeta Hleft Htrace.
  pose proof (List.nth_error_nth _ _ (0,0) Hrecord_a) as Hnth_a.
  unfold plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  destruct f as [s bs ns]; cbn [machine nums] in *; unfold funcdef_0__setness_body.
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
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(first,observations))) by exact Hfirst; rewrite Hrun; clear Hrun end
    |match goal with H : execObserved (funcdef_0__intern _ _) _ = Some (tt,(?after,?trace)) |-
         context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(after,trace))) by exact H; rewrite Hrun; clear Hrun end
    |progress rewrite Ha |progress rewrite Nat2Z.id
    |match goal with H : meta_value ?source 0 = ?value |- context [meta_value ?source 0] => progress rewrite H end
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. all: reflexivity.
Qed.
Lemma result_semantics observations s left final ids next p :
  FormulaCircuit.executes observations plan s [0;left] final ids ->
  FormulaCircuit.represents next ids (values p) ->
  word (meta_value final 0) /\ nth_error next (Z.to_nat (meta_value final 0)) = Some (result p).
Proof.
  intros Htrace Hrep. pose proof (FormulaCircuit.wire next ids (values p) 11 (result p) Hrep eq_refl) as Hwire.
  unfold plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire.
  exact Hwire.
Qed.
End RenameMemoClassSetnessRaw.
