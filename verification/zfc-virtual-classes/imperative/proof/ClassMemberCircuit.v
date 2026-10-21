From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives FormulaCircuit Intern Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ClassMemberCircuit.
Import IndexExecution SipHashExecution ObservedLocal.
Definition plan := [FormulaCircuit.member 0 1;FormulaCircuit.implies 3 1;FormulaCircuit.implies 1 3;
  FormulaCircuit.implies 5 0;FormulaCircuit.implies 4 6;FormulaCircuit.implies 7 0;FormulaCircuit.all 8;
  FormulaCircuit.implies 2 0;FormulaCircuit.implies 9 10;FormulaCircuit.implies 11 0;
  FormulaCircuit.implies 12 0;FormulaCircuit.all 13;FormulaCircuit.implies 14 0].
Definition result p q := SetTheory.ex (SetTheory.conj (SetTheory.all (SetTheory.iff (SetTheory.member 0 1) p)) q).
Definition values p q :=
  let t0 := SetTheory.member 0 1 in
  let t1 := SetTheory.implies t0 p in let t2 := SetTheory.implies p t0 in
  let t3 := SetTheory.neg t2 in let t4 := SetTheory.implies t1 t3 in
  let t5 := SetTheory.neg t4 in let t6 := SetTheory.all t5 in
  let t7 := SetTheory.neg q in let t8 := SetTheory.implies t6 t7 in
  let t9 := SetTheory.neg t8 in let t10 := SetTheory.neg t9 in
  let t11 := SetTheory.all t10 in let t12 := SetTheory.neg t11 in
  [SetTheory.falsity;p;q;t0;t1;t2;t3;t4;t5;t6;t7;t8;t9;t10;t11;t12].
Lemma infer p q : FormulaCircuit.infer plan [SetTheory.falsity;p;q] = Some (values p q).
Proof. reflexivity. Qed.
Lemma fits : Forall FormulaCircuit.fits plan.
Proof. repeat constructor; unfold word,maximum; lia. Qed.
Theorem construct s fs left right p q reserve observations :
  NativeRepresentation.canonical_arena s fs -> meta_value s 8 = 0 -> nth_error fs 0 = Some SetTheory.falsity ->
  word left -> word right -> nth_error fs (Z.to_nat left) = Some p -> nth_error fs (Z.to_nat right) = Some q ->
  Z.of_nat (length fs + 13 + reserve) <= 9223372036854775807 ->
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
End ClassMemberCircuit.
