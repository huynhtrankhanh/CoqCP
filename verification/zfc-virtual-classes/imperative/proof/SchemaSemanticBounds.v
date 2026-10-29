From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash NativeState FormulaTopology RenameMemoIndexBounds
 SchemaEvaluationIndexBounds SchemaEvaluationIndexCell SchemaInstanceCheckedResources.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From stdpp Require Import numbers list.

Module SchemaSemanticBounds.
Import SchemaInstanceCheckedResources.
Lemma formula_max_bound p bound : RenameMemoIndexBounds.formula_bound bound p -> (formula_max p<=bound)%nat.
Proof.
 induction p as [|i j|i j|p IH q JH|p IH];cbn [formula_max RenameMemoIndexBounds.formula_bound];
 intro H;try lia;try (destruct H as [Hp Hq];specialize(IH Hp);specialize(JH Hq);lia);now apply IH.
Qed.
Lemma formulas_max_bound entries bound : SchemaEvaluationIndexBounds.formulas bound entries -> (formulas_max entries<=bound)%nat.
Proof. intro H. induction H as [|p entries Hp Hentries IH];cbn [formulas_max];[lia|]. pose proof(formula_max_bound p bound Hp);lia. Qed.
Lemma class_max_bound cls bound : SchemaEvaluationIndexBounds.class_bound bound cls -> (class_max cls<=bound)%nat.
Proof. destruct cls;cbn [SchemaEvaluationIndexBounds.class_bound class_max];intro H;[exact H|now apply formula_max_bound]. Qed.
Lemma classes_max_bound entries bound : SchemaEvaluationIndexBounds.classes bound entries -> (classes_max entries<=bound)%nat.
Proof. intro H. induction H as [|cls entries Hcls Hentries IH];cbn [classes_max];[lia|]. pose proof(class_max_bound cls bound Hcls);lia. Qed.
Theorem initial_bound_le native logical bound : NativeState.represents native logical ->
 FormulaTopology.ordered native (length(Protocol.formulas logical)) ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas logical)(Protocol.classes logical) bound ->
 (initial_bound logical<=bound)%nat.
Proof.
 intros Hstate Htop [Hraw Hclasses]. unfold initial_bound. apply Nat.max_lub.
 - apply formulas_max_bound. exact(SchemaEvaluationIndexBounds.canonical_raw_formulas native (Protocol.formulas logical) bound
    (NativeState.formula_representation _ _ Hstate) Htop Hraw).
 - now apply classes_max_bound.
Qed.
End SchemaSemanticBounds.
