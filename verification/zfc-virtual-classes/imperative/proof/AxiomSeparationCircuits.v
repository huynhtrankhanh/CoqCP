From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Intern FormulaCircuit FormulaCircuitResult.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomSeparationCircuits.
Import IndexExecution SipHashExecution.
(* The native builder emits two atoms before its single mode-2 rename. *)
Definition before := [FormulaCircuit.member 0 1;FormulaCircuit.member 0 2].
Definition after := [FormulaCircuit.implies 3 0;FormulaCircuit.implies 2 4;FormulaCircuit.implies 5 0;
  FormulaCircuit.implies 1 6;FormulaCircuit.implies 6 1;FormulaCircuit.implies 8 0;
  FormulaCircuit.implies 7 9;FormulaCircuit.implies 10 0;FormulaCircuit.all 11;
  FormulaCircuit.implies 12 0;FormulaCircuit.all 13;FormulaCircuit.implies 14 0].
Definition initial := [SetTheory.falsity].
Definition middle := [SetTheory.falsity;SetTheory.member 0 1;SetTheory.member 0 2].
Definition renamed p := SetTheory.rename SetTheory.sep_rename p.
Definition values p := match FormulaCircuit.infer after (middle++[renamed p]) with Some result=>result | None=>[] end.
Lemma before_inferred : FormulaCircuit.infer before initial=Some middle.
Proof. reflexivity. Qed.
Lemma after_inferred p : FormulaCircuit.infer after (middle++[renamed p])=Some (values p).
Proof. reflexivity. Qed.
Lemma before_fits : Forall FormulaCircuit.fits before.
Proof. unfold before. repeat (constructor;[unfold FormulaCircuit.fits,word,maximum;lia|]);constructor. Qed.
Lemma after_fits : Forall FormulaCircuit.fits after.
Proof. repeat constructor. Qed.
Lemma target p : nth_error (values p) 15=Some (SetTheory.separation p).
Proof. reflexivity. Qed.
Theorem result observations s ids final result_ids next p :
  length ids=4%nat -> FormulaCircuit.executes observations after s ids final result_ids ->
  FormulaCircuit.represents next result_ids (values p) ->
  word (meta_value final 0) /\ nth_error next (Z.to_nat (meta_value final 0))=Some (SetTheory.separation p) /\
  SetTheory.derives (SetTheory.separation p).
Proof.
  intros Hlength Htrace Hrep.
  pose proof (FormulaCircuitResult.meaning observations after s ids final result_ids next (values p)
    (SetTheory.separation p) Htrace ltac:(discriminate) Hrep) as Hmeaning.
  rewrite Hlength in Hmeaning. specialize (Hmeaning (target p)).
  destruct Hmeaning as [Hword Hmeaning]. split;[exact Hword|]. split;[exact Hmeaning|].
  apply SetTheory.d_set,SetTheory.ax_separation.
Qed.
End AxiomSeparationCircuits.
