From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives FormulaCircuit Intern Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassEqualCircuit.
Import IndexExecution SipHashExecution ObservedLocal.
Definition plan := [FormulaCircuit.implies 1 2; FormulaCircuit.implies 2 1;
  FormulaCircuit.implies 4 0; FormulaCircuit.implies 3 5; FormulaCircuit.implies 6 0; FormulaCircuit.all 7].
Definition values p q := [SetTheory.falsity;p;q;SetTheory.implies p q;SetTheory.implies q p;
  SetTheory.neg (SetTheory.implies q p);SetTheory.implies (SetTheory.implies p q) (SetTheory.neg (SetTheory.implies q p));
  SetTheory.iff p q;SetTheory.all (SetTheory.iff p q)].
Lemma infer p q : FormulaCircuit.infer plan [SetTheory.falsity;p;q] = Some (values p q).
Proof. reflexivity. Qed.
Lemma fits : Forall FormulaCircuit.fits plan.
Proof. repeat constructor. Qed.
Theorem construct s fs left right p q reserve observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 -> nth_error fs 0 = Some SetTheory.falsity ->
  word left -> word right -> nth_error fs (Z.to_nat left) = Some p -> nth_error fs (Z.to_nat right) = Some q ->
  Z.of_nat (length fs + 6 + reserve) <= 9223372036854775807 ->
  exists final next ids, FormulaCircuit.executes observations plan s [0;left;right] final ids /\
    InternExecution.logical_frame s final /\ NativeRepresentation.canonical_arena final next /\ meta_value final 8 = 0 /\
    FormulaCircuit.represents next ids (values p q) /\ (exists extra,next=fs++extra) /\
    Z.of_nat (length next + reserve) <= 9223372036854775807.
Proof.
  intros Harena Herror Hfalse Hleft Hright Hp Hq Hbudget.
  apply (FormulaCircuit.complete plan s fs [0;left;right] [SetTheory.falsity;p;q] (values p q) reserve observations Harena Herror).
  - constructor; [split; [unfold word,maximum; lia|exact Hfalse]|].
    constructor; [auto|]. constructor; [auto|constructor].
  - apply fits.
  - apply infer.
  - exact Hbudget.
Qed.
Definition predicate_arguments cls : varsfuncdef_0__predicate -> Z :=
  update (update (update (fun _=>0) vardef_0__predicate_cls cls) vardef_0__predicate_shift 1) vardef_0__predicate_arg 0.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__classEqual.
Local Opaque funcdef_0__intern funcdef_0__predicate.
Theorem generated_general (f : Frame) first second final ids a b tag_a tag_b value_a value_b left right observations :
  nums f vardef_0__classEqual_a = Z.of_nat a -> nums f vardef_0__classEqual_b = Z.of_nat b ->
  (a < length (memory (machine f) arraydef_0__classes))%nat -> (b < length (memory (machine f) arraydef_0__classes))%nat ->
  nth_error (memory (machine f) arraydef_0__classes) a = Some (tag_a,value_a) ->
  nth_error (memory (machine f) arraydef_0__classes) b = Some (tag_b,value_b) -> (tag_a<>0 \/ tag_b<>0) ->
  execObserved (funcdef_0__predicate (fun _=>false) (predicate_arguments (Z.of_nat a))) (machine f,observations) = Some (tt,(first,observations)) ->
  (0 < length (memory first arraydef_0__meta))%nat -> meta_value first 0 = left ->
  execObserved (funcdef_0__predicate (fun _=>false) (predicate_arguments (Z.of_nat b))) (first,observations) = Some (tt,(second,observations)) ->
  (0 < length (memory second arraydef_0__meta))%nat -> meta_value second 0 = right ->
  FormulaCircuit.executes observations plan second [0;left;right] final ids ->
  optionBind (execLocalObserved funcdef_0__classEqual_body (f,observations))
    (fun r=>Some (tt,(machine (fst (snd r)),snd (snd r)))) =
    Some (tt,(store_meta final 0 (meta_value final 0),observations)).
Proof.
  intros Ha Hb Habound Hbbound Hrecord_a Hrecord_b Hnonsets Hfirst Hfirstmeta Hleft Hsecond Hsecondmeta Hright Htrace.
  pose proof (List.nth_error_nth _ _ (0,0) Hrecord_a) as Hnth_a.
  pose proof (List.nth_error_nth _ _ (0,0) Hrecord_b) as Hnth_b.
  unfold plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  destruct (Z.eq_dec tag_a 0) as [Htag_a|Htag_a]; destruct (Z.eq_dec tag_b 0) as [Htag_b|Htag_b]; try (exfalso; tauto).
  all: destruct f as [s bs ns]; cbn [machine nums] in *; unfold funcdef_0__classEqual_body.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       |arraydef_0__classes => first [exact Habound|exact Hbbound]
       |arraydef_0__meta => replace (Z.to_nat 0) with 0%nat by reflexivity; assumption end)
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in first
         [assert (Hsame : expression = (tag_a,value_a)) by exact Hnth_a
         |assert (Hsame : expression = (tag_b,value_b)) by exact Hnth_b]; rewrite Hsame; clear Hsame end
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
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. all: reflexivity.
Qed.
Lemma result_semantics observations s left right final ids next p q :
  FormulaCircuit.executes observations plan s [0;left;right] final ids ->
  FormulaCircuit.represents next ids (values p q) ->
  word (meta_value final 0) /\ nth_error next (Z.to_nat (meta_value final 0)) = Some (SetTheory.all (SetTheory.iff p q)).
Proof.
  intros Htrace Hrep. pose proof (FormulaCircuit.wire next ids (values p q) 8 (SetTheory.all (SetTheory.iff p q)) Hrep eq_refl) as Hwire.
  unfold plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  cbn [List.nth app] in Hwire.
  exact Hwire.
Qed.
End ClassEqualCircuit.
