From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern FormulaEncoding FormulaTopology Representation
  FormulaCircuit FormulaCircuitProperties FormulaCircuitResult AxiomCircuits.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomFixedCircuits.
Import IndexExecution SipHashExecution.
(* Pure ZFC axiom circuits, in the native builder's memoized emission order.
   [target] below checks the complete resulting formula against the independent
   object-theory definition; a successful trace alone is not that check. *)
Inductive kind := extensionality | foundation | pairing | union | power | infinity | choice.
Definition selector which : Z := match which with
| extensionality=>9
| foundation=>10
| pairing=>11
| union=>12
| power=>13
| infinity=>14
| choice=>17
end.
Definition witness which := match which with
| extensionality=>SetTheory.Ext
| foundation=>SetTheory.Found
| pairing=>SetTheory.Pair
| union=>SetTheory.Union
| power=>SetTheory.Power
| infinity=>SetTheory.Infinity
| choice=>SetTheory.Choice
end.
Definition extensionality_plan := [
  FormulaCircuit.member 0 1; FormulaCircuit.member 0 2; FormulaCircuit.implies 1 2;
  FormulaCircuit.implies 2 1; FormulaCircuit.implies 4 0; FormulaCircuit.implies 3 5;
  FormulaCircuit.implies 6 0; FormulaCircuit.all 7; FormulaCircuit.equal 0 1;
  FormulaCircuit.implies 8 9
].
Definition foundation_plan := [
  FormulaCircuit.member 0 1; FormulaCircuit.implies 1 0; FormulaCircuit.all 2;
  FormulaCircuit.implies 3 0; FormulaCircuit.member 0 2; FormulaCircuit.implies 5 0;
  FormulaCircuit.implies 1 6; FormulaCircuit.all 7; FormulaCircuit.implies 8 0;
  FormulaCircuit.implies 1 9; FormulaCircuit.implies 10 0; FormulaCircuit.implies 11 0;
  FormulaCircuit.all 12; FormulaCircuit.implies 13 0; FormulaCircuit.implies 4 14
].
Definition pairing_plan := [
  FormulaCircuit.member 1 0; FormulaCircuit.member 2 0; FormulaCircuit.implies 2 0;
  FormulaCircuit.implies 1 3; FormulaCircuit.implies 4 0; FormulaCircuit.implies 5 0;
  FormulaCircuit.all 6; FormulaCircuit.implies 7 0
].
Definition union_plan := [
  FormulaCircuit.member 0 1; FormulaCircuit.member 1 3; FormulaCircuit.member 0 2;
  FormulaCircuit.implies 2 3; FormulaCircuit.implies 1 4; FormulaCircuit.all 5;
  FormulaCircuit.all 6; FormulaCircuit.implies 7 0; FormulaCircuit.all 8;
  FormulaCircuit.implies 9 0
].
Definition power_plan := [
  FormulaCircuit.member 0 1; FormulaCircuit.member 0 3; FormulaCircuit.implies 1 2;
  FormulaCircuit.all 3; FormulaCircuit.implies 4 1; FormulaCircuit.all 5;
  FormulaCircuit.implies 6 0; FormulaCircuit.all 7; FormulaCircuit.implies 8 0
].
Definition infinity_plan := [
  FormulaCircuit.member 0 1; FormulaCircuit.implies 1 0; FormulaCircuit.all 2;
  FormulaCircuit.implies 3 0; FormulaCircuit.implies 1 4; FormulaCircuit.implies 5 0;
  FormulaCircuit.implies 6 0; FormulaCircuit.all 7; FormulaCircuit.implies 8 0;
  FormulaCircuit.member 0 2; FormulaCircuit.implies 10 0; FormulaCircuit.equal 0 2;
  FormulaCircuit.implies 11 12; FormulaCircuit.implies 1 13; FormulaCircuit.implies 13 1;
  FormulaCircuit.implies 15 0; FormulaCircuit.implies 14 16; FormulaCircuit.implies 17 0;
  FormulaCircuit.all 18; FormulaCircuit.implies 19 0; FormulaCircuit.implies 10 20;
  FormulaCircuit.implies 21 0; FormulaCircuit.implies 22 0; FormulaCircuit.all 23;
  FormulaCircuit.implies 24 0; FormulaCircuit.implies 1 25; FormulaCircuit.all 26;
  FormulaCircuit.implies 27 0; FormulaCircuit.implies 9 28; FormulaCircuit.implies 29 0;
  FormulaCircuit.implies 30 0; FormulaCircuit.all 31; FormulaCircuit.implies 32 0
].
Definition choice_plan := [
  FormulaCircuit.member 0 1; FormulaCircuit.implies 1 0; FormulaCircuit.all 2;
  FormulaCircuit.implies 3 0; FormulaCircuit.implies 1 4; FormulaCircuit.all 5;
  FormulaCircuit.member 1 2; FormulaCircuit.member 0 2; FormulaCircuit.implies 8 2;
  FormulaCircuit.implies 9 0; FormulaCircuit.implies 10 0; FormulaCircuit.all 11;
  FormulaCircuit.implies 12 0; FormulaCircuit.equal 1 0; FormulaCircuit.implies 13 14;
  FormulaCircuit.implies 8 15; FormulaCircuit.implies 7 16; FormulaCircuit.all 17;
  FormulaCircuit.all 18; FormulaCircuit.implies 19 0; FormulaCircuit.implies 6 20;
  FormulaCircuit.implies 21 0; FormulaCircuit.member 0 3; FormulaCircuit.equal 0 1;
  FormulaCircuit.implies 23 24; FormulaCircuit.implies 8 25; FormulaCircuit.all 26;
  FormulaCircuit.implies 27 0; FormulaCircuit.implies 8 28; FormulaCircuit.implies 29 0;
  FormulaCircuit.implies 30 0; FormulaCircuit.implies 1 31; FormulaCircuit.implies 32 0;
  FormulaCircuit.implies 33 0; FormulaCircuit.all 34; FormulaCircuit.implies 35 0;
  FormulaCircuit.implies 8 36; FormulaCircuit.all 37; FormulaCircuit.implies 38 0;
  FormulaCircuit.all 39; FormulaCircuit.implies 40 0; FormulaCircuit.implies 22 41
].
Definition plan which := match which with
| extensionality=>extensionality_plan
| foundation=>foundation_plan
| pairing=>pairing_plan
| union=>union_plan
| power=>power_plan
| infinity=>infinity_plan
| choice=>choice_plan
end.
Definition values which := match FormulaCircuit.infer (plan which) [SetTheory.falsity] with
  | Some result=>result | None=>[] end.
Lemma inferred which : FormulaCircuit.infer (plan which) [SetTheory.falsity]=Some (values which).
Proof. destruct which;reflexivity. Qed.
Lemma target which : nth_error (values which) (length (plan which))=Some (SetTheory.axiom_formula (witness which)).
Proof. destruct which;reflexivity. Qed.
Lemma nonempty which : plan which<>[].
Proof. destruct which;discriminate. Qed.
Lemma fits which : Forall FormulaCircuit.fits (plan which).
Proof.
  destruct which;unfold plan,extensionality_plan,foundation_plan,pairing_plan,union_plan,power_plan,infinity_plan,choice_plan;
    repeat (constructor; [first [exact I|unfold FormulaCircuit.fits,word,maximum;lia]|]);constructor.
Qed.
Theorem construct which s fs reserve observations :
  NativeRepresentation.canonical_arena s fs -> FormulaTopology.ordered s (length fs) -> meta_value s 8=0 ->
  nth_error fs 0=Some SetTheory.falsity ->
  Z.of_nat (length fs+length (plan which)+reserve)<=9223372036854775807 ->
  exists final next ids,
    AxiomCircuits.constructed observations (plan which) [0%Z] (values which) reserve s fs final next ids.
Proof.
  intros Harena Hordered Herror Hfalse Hbudget.
  apply (FormulaCircuitProperties.complete (plan which) s fs [0%Z] [SetTheory.falsity] (values which)
    reserve observations Harena Hordered Herror).
  - constructor;[split;[unfold word,maximum;lia|exact Hfalse]|constructor].
  - apply fits.
  - apply inferred.
  - exact Hbudget.
Qed.
Theorem result observations which s final ids next :
  FormulaCircuit.executes observations (plan which) s [0%Z] final ids ->
  FormulaCircuit.represents next ids (values which) ->
  word (meta_value final 0) /\
  nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.axiom_formula (witness which)) /\
  SetTheory.derives (SetTheory.axiom_formula (witness which)).
Proof.
  intros Htrace Hrep.
  assert (Htarget : nth_error (values which) (length ([0%Z]:list Z)+length (plan which)-1)=Some (SetTheory.axiom_formula (witness which))).
  { assert (Hindex : (length ([0%Z]:list Z)+length (plan which)-1)%nat=length (plan which)) by (cbn [length];lia).
    rewrite Hindex. exact (target which). }
  pose proof (FormulaCircuitResult.meaning observations (plan which) s [0%Z] final ids next (values which)
    (SetTheory.axiom_formula (witness which)) Htrace (nonempty which) Hrep Htarget) as [Hword Hmeaning].
  split;[exact Hword|]. split;[exact Hmeaning|]. destruct which;apply SetTheory.d_set;constructor.
Qed.
End AxiomFixedCircuits.
