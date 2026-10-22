From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern FormulaEncoding FormulaTopology Representation
  FormulaCircuit FormulaCircuitProperties AxiomCircuits.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomEqualityCircuits.
Import IndexExecution SipHashExecution.
Inductive kind := member_left | member_right | equal_trans.
Definition selector which : Z := match which with member_left=>6|member_right=>7|equal_trans=>8 end.
Definition witness which i j k := match which with
| member_left=>SetTheory.MemLeft i j k
| member_right=>SetTheory.MemRight i j k
| equal_trans=>SetTheory.EqTrans i j k end.
Definition left_formula which i k := match which with
| member_left=>SetTheory.member i k
| member_right=>SetTheory.member k i
| equal_trans=>SetTheory.equal i k end.
Definition right_formula which j k := match which with
| member_left=>SetTheory.member j k
| member_right=>SetTheory.member k j
| equal_trans=>SetTheory.equal j k end.
Definition left_op which i k := match which with
| member_left=>FormulaCircuit.member i k
| member_right=>FormulaCircuit.member k i
| equal_trans=>FormulaCircuit.equal i k end.
Definition right_op which j k := match which with
| member_left=>FormulaCircuit.member j k
| member_right=>FormulaCircuit.member k j
| equal_trans=>FormulaCircuit.equal j k end.
Definition plan which i j k := [FormulaCircuit.equal i j;left_op which i k;right_op which j k;
  FormulaCircuit.implies 1 2;FormulaCircuit.implies 0 3].
Definition values which i j k := [SetTheory.equal i j;left_formula which i k;right_formula which j k;
  SetTheory.implies (left_formula which i k) (right_formula which j k);
  SetTheory.axiom_formula (witness which i j k)].
Lemma infer which i j k : FormulaCircuit.infer (plan which i j k) []=Some (values which i j k).
Proof. destruct which;reflexivity. Qed.
Lemma fits which i j k : word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat k) ->
  Forall FormulaCircuit.fits (plan which i j k).
Proof.
  intros Hi Hj Hk. destruct which;unfold plan,left_op,right_op;
    repeat constructor;assumption.
Qed.
Theorem construct which i j k s fs reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat k) ->
  Z.of_nat (length fs+5+reserve)<=9223372036854775807 ->
  exists final next ids,
    AxiomCircuits.constructed observations (plan which i j k) [] (values which i j k) reserve s fs final next ids.
Proof.
  intros Harena Hordered Herror Hi Hj Hk Hbudget.
  apply (FormulaCircuitProperties.complete (plan which i j k) s fs [] [] (values which i j k)
    reserve observations Harena Hordered Herror).
  - constructor.
  - now apply fits.
  - apply infer.
  - exact Hbudget.
Qed.
Theorem result observations which i j k s final ids next :
  FormulaCircuit.executes observations (plan which i j k) s [] final ids ->
  FormulaCircuit.represents next ids (values which i j k) ->
  word (meta_value final 0) /\
  nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (witness which i j k)) /\
  SetTheory.derives (SetTheory.axiom_formula (witness which i j k)).
Proof.
  intros Htrace Hrep.
  pose proof (FormulaCircuit.wire next ids (values which i j k) 4
    (SetTheory.axiom_formula (witness which i j k)) Hrep eq_refl) as Hwire.
  destruct which;unfold plan,left_op,right_op in Htrace.
  all: repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H;clear H;subst end.
  all: match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H;clear H;subst end.
  all: cbn [List.nth app] in Hwire;destruct Hwire as [Hword Hmeaning];
    split;[exact Hword|];split;[exact Hmeaning|].
  - apply SetTheory.d_mem_left.
  - apply SetTheory.d_mem_right.
  - apply SetTheory.d_eq.
Qed.
End AxiomEqualityCircuits.
