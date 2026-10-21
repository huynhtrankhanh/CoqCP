From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash HashTable Rebuild InternInvariant FormulaEncoding Representation HistoryRefinement HistoryStorage.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module HistoryLookup.
Import IndexExecution SipHashExecution HashTableInvariant.
Lemma native_lookup s logical i fid : HistoryRefinement.represents s logical ->
  nth_error (Protocol.history logical) i = Some fid ->
  (i < length (memory s arraydef_0__theorems))%nat /\
  List.nth i (memory s arraydef_0__theorems) 0 = Z.of_nat fid.
Proof.
  intros Hrep Hlookup. pose proof (HistoryStorage.prefix_capacity s logical Hrep) as Hcapacity.
  assert (Hi : (i < length (Protocol.history logical))%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. destruct Hrep as [_ Hprefix].
  pose proof (f_equal (fun xs => nth_error xs i) Hprefix) as Hentry. cbn beta in Hentry.
  rewrite List.nth_error_firstn, List.nth_error_map, Hlookup in Hentry.
  rewrite (proj2 (Nat.ltb_lt i _) Hi) in Hentry. cbn [option_map] in Hentry.
  exact (List.nth_error_nth _ _ 0 Hentry).
Qed.
Lemma theorem_lookup s logical i p : HistoryRefinement.represents s logical ->
  Protocol.theorem_at logical i = Some p ->
  exists fid, nth_error (Protocol.history logical) i = Some fid /\
    Protocol.formula_at logical fid = Some p /\
    (i < length (memory s arraydef_0__theorems))%nat /\
    List.nth i (memory s arraydef_0__theorems) 0 = Z.of_nat fid.
Proof.
  intros Hrep. unfold Protocol.theorem_at. destruct (nth_error (Protocol.history logical) i) as [fid|] eqn:Hlookup; [|discriminate].
  intro Hp. exists fid. split; [reflexivity|]. split; [exact Hp|]. now apply (native_lookup s logical i fid).
Qed.
Lemma formula_reference s fs fid p : NativeRepresentation.canonical_arena s fs ->
  nth_error fs fid = Some p ->
  (fid < length (memory s arraydef_0__formulas))%nat /\ word (Z.of_nat fid) /\
  FormulaEncoding.normal (tuple_at s fid) /\ FormulaEncoding.decode fs (tuple_at s fid) = Some p.
Proof.
  intros [Htable [Hrep [Hunique Hnormal]]] Hlookup.
  assert (Hfid : (fid < length fs)%nat) by (apply nth_error_Some; congruence).
  pose proof (proj1 Htable) as [_ [_ [_ [_ [Hcapacity [_ Hlimit]]]]]].
  split; [lia|]. split; [unfold word; lia|]. split; [now apply Hnormal|].
  exact (NativeRepresentation.represented_lookup s fs fid p Hrep Hlookup).
Qed.
Theorem modus_ponens_nodes s logical i j p q :
  NativeRepresentation.canonical_arena s (Protocol.formulas logical) -> HistoryRefinement.represents s logical ->
  Protocol.theorem_at logical i = Some (SetTheory.implies p q) -> Protocol.theorem_at logical j = Some p ->
  exists node aid bid,
    (i < length (memory s arraydef_0__theorems))%nat /\
    (j < length (memory s arraydef_0__theorems))%nat /\
    (node < length (memory s arraydef_0__formulas))%nat /\
    List.nth i (memory s arraydef_0__theorems) 0 = Z.of_nat node /\
    List.nth j (memory s arraydef_0__theorems) 0 = Z.of_nat aid /\
    tuple_at s node = (3,Z.of_nat aid,Z.of_nat bid) /\
    nth_error (Protocol.formulas logical) bid = Some q.
Proof.
  intros Harena Hhistory Hi Hj.
  destruct (theorem_lookup s logical i _ Hhistory Hi) as [node [Hni [Hpi [Hbi Hei]]]].
  destruct (theorem_lookup s logical j _ Hhistory Hj) as [aid [Hnj [Hpj [Hbj Hej]]]].
  destruct (formula_reference s _ node _ Harena Hpi) as [Hnode [Hnodeword [Hnormal Hdecode]]].
  destruct (formula_reference s _ aid _ Harena Hpj) as [Haid [Haidword _]].
  destruct (FormulaEncoding.decode_implication _ _ p q Hnormal Hdecode) as [a [b [Htuple [Haword [Hbword [Ha Hb]]]]]].
  assert (Heqa : a = Z.of_nat aid).
  { apply (proj2 (FormulaEncoding.formula_id_equality _ a (Z.of_nat aid) p p (proj1 (proj2 (proj2 Harena))) Haword Haidword Ha ltac:(now rewrite Nat2Z.id))). reflexivity. }
  assert (Heqb : b = Z.of_nat (Z.to_nat b)) by (rewrite Z2Nat.id; [reflexivity|exact (proj1 Hbword)]).
  exists node,aid,(Z.to_nat b). repeat split; try assumption. now rewrite <- Heqa, <- Heqb.
Qed.
End HistoryLookup.
