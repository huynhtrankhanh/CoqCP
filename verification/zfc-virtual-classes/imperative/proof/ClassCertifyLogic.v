From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Guarantees.
From NativeProof Require Import Index SipHash HistoryRefinement HistoryLookup FormulaEncoding Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ClassCertifyLogic.
Import IndexExecution SipHashExecution.
Lemma native_certificate_theorem s logical tid fid p :
  HistoryRefinement.represents s logical -> (tid<length (Protocol.history logical))%nat ->
  meta_value s 0=Z.of_nat fid -> List.nth tid (memory s arraydef_0__theorems) 0=meta_value s 0 ->
  Protocol.formula_at logical fid=Some p -> Protocol.theorem_at logical tid=Some p.
Proof.
  intros Hhistory Hbound Hresult Hcompare Hformula.
  destruct (nth_error (Protocol.history logical) tid) as [saved|] eqn:Hsaved.
  - destruct (HistoryLookup.native_lookup s logical tid saved Hhistory Hsaved) as [Hnativebound Hnative].
    assert (Hid : saved=fid) by (apply Nat2Z.inj; congruence). subst saved.
    unfold Protocol.theorem_at. now rewrite Hsaved.
  - apply nth_error_None in Hsaved. lia.
Qed.
Theorem native_certificate_sound s logical tid fid cls :
  HistoryRefinement.represents s logical -> Guarantees.history logical ->
  (tid<length (Protocol.history logical))%nat -> meta_value s 0=Z.of_nat fid ->
  List.nth tid (memory s arraydef_0__theorems) 0=meta_value s 0 ->
  Protocol.formula_at logical fid=Some (Protocol.class_setness cls) ->
  SetTheory.derives (Protocol.class_setness cls).
Proof.
  intros Hrep Hsound Hbound Hresult Hcompare Hformula.
  apply (Guarantees.theorem_sound logical tid _ Hsound).
  exact (native_certificate_theorem s logical tid fid _ Hrep Hbound Hresult Hcompare Hformula).
Qed.
Theorem comparison_exact s fs index p tid fid q :
  NativeRepresentation.canonical_arena s fs -> word (Z.of_nat index) -> word (Z.of_nat fid) ->
  nth_error fs index=Some p -> nth_error fs fid=Some q ->
  meta_value s 0=Z.of_nat index -> List.nth tid (memory s arraydef_0__theorems) 0=Z.of_nat fid ->
  (meta_value s 0=List.nth tid (memory s arraydef_0__theorems) 0 <-> p=q).
Proof.
  intros Harena Hindex Hfid Hp Hq Hresult Htheorem. rewrite Hresult,Htheorem.
  apply (FormulaEncoding.formula_id_equality fs (Z.of_nat index) (Z.of_nat fid) p q (proj1 (proj2 (proj2 Harena))) Hindex Hfid);
    now rewrite Nat2Z.id.
Qed.
End ClassCertifyLogic.
