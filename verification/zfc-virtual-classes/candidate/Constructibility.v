From CoqCP Require Import Options SetTheory.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
From Submission Require Import Semantics InnerModels StableSets.
Import ListNotations.

(* The Def operation and a raw well-founded hierarchy, developed without
   adding axioms. Ordinal invariance, the reflection/replacement argument,
   and a well-ordering of the full class are not claimed by these lemmas. *)
Module Constructibility.
Import SetTheory.
Module S := StableSets.
Module I := InnerModels.
Module N := NegativeSemantics.

Fixpoint bounded (n : nat) (p : formula) : Prop :=
  match p with
  | falsity => True
  | equal i j | member i j => i < n /\ j < n
  | implies p q => bounded n p /\ bounded n q
  | all p => bounded (S n) p
  end.

Definition holds (x : S.tree) := I.satisfies S.member S.equivalent (fun z => S.member z x).

Lemma bounded_environment x p n e e' :
  bounded n p -> (forall i, i < n -> e i = e' i) ->
  (holds x p e <-> holds x p e').
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in n, e, e' |- *;
    cbn [bounded holds I.satisfies]; intros Hb He.
  - reflexivity.
  - destruct Hb as [Hi Hj]. now rewrite (He i Hi), (He j Hj).
  - destruct Hb as [Hi Hj]. now rewrite (He i Hi), (He j Hj).
  - destruct Hb as [Hp Hq]. rewrite (IHp _ _ _ Hp He), (IHq _ _ _ Hq He). reflexivity.
  - assert (Hx : forall z, I.satisfies S.member S.equivalent (fun z => S.member z x)
      p (N.extend z e) <-> I.satisfies S.member S.equivalent (fun z => S.member z x)
      p (N.extend z e')).
    { intro z. apply (IH (S n)); [exact Hb |].
      intros [|i] Hi; cbn [N.extend]; [reflexivity | apply He; lia]. }
    split; intros H z Hz; apply Hx; now apply H.
Qed.

(* Parameters really are elements of x. The bound rules out dependence on the
   arbitrary default used beyond the supplied finite parameter environment. *)
Definition specification (x : S.tree) :=
  { fp : formula * list (S.indices x) | bounded (S (length (snd fp))) (fst fp) }.
Definition parameter_environment (x : S.tree) (z : S.tree) (ps : list (S.indices x)) :=
  N.extend z (fun i => nth i (map (S.child x) ps) S.empty).
Definition defined_subset (x : S.tree) (s : specification x) :=
  let fp := proj1_sig s in
  S.separate (fun z => holds x (fst fp) (parameter_environment x z (snd fp))) x.
Definition definable_successor (x : S.tree) := S.node (specification x) (defined_subset x).

Lemma predicate_respects x (s : specification x) z z' :
  S.equivalent z z' ->
  holds x (fst (proj1_sig s)) (parameter_environment x z (snd (proj1_sig s))) ->
  holds x (fst (proj1_sig s)) (parameter_environment x z' (snd (proj1_sig s))).
Proof.
  intro He. unfold holds. apply (proj1 (I.equivalent_environments S.member S.equivalent
    S.equivalent_refl S.equivalent_sym S.equivalent_trans S.member_left S.member_right
    (fun z => S.member z x) (fst (proj1_sig s))
    (parameter_environment x z (snd (proj1_sig s)))
    (parameter_environment x z' (snd (proj1_sig s)))
    (fun i => match i with
      | 0 => He
      | S n => S.equivalent_refl (nth n (map (S.child x) (snd (proj1_sig s))) S.empty)
      end))).
Qed.

Theorem defined_subset_membership x (s : specification x) z :
  S.member z (defined_subset x s) <-> S.member z x /\
    holds x (fst (proj1_sig s)) (parameter_environment x z (snd (proj1_sig s))).
Proof.
  unfold defined_subset. apply S.separation_membership.
  - intro y. apply I.stable.
  - intros y y' He. now apply predicate_respects.
Qed.

Theorem definition_is_in_successor x (s : specification x) :
  S.member (defined_subset x s) (definable_successor x).
Proof. intro Hn. apply Hn. exists s. apply S.equivalent_refl. Qed.

Theorem successor_contains_only_subsets x y :
  S.member y (definable_successor x) -> forall z, S.member z y -> S.member z x.
Proof.
  intros Hy z Hz. apply S.member_stable. intro Hnot. apply Hy. intros [s He].
  apply Hnot. pose proof (S.member_right y (defined_subset x s) z He Hz) as Hsubset.
  apply defined_subset_membership in Hsubset. exact (proj1 Hsubset).
Qed.

Definition empty_specification x : specification x := exist _ (falsity, []) I.

Theorem successor_of_empty x :
  (forall z, ~ S.member z x) ->
  S.equivalent (definable_successor x) (S.singleton S.empty).
Proof.
  intro Hempty.
  assert (Hsub : forall s : specification x, S.equivalent (defined_subset x s) S.empty).
  { intro s. apply S.empty_if_no_members. intros z Hz.
    apply (Hempty z). exact (S.separated_subset _ x z Hz). }
  apply S.extensionality. intro z. split.
  - intros Hz Hn. apply Hz. intros [s He]. apply Hn. exists true.
    eapply S.equivalent_trans; [exact He | apply Hsub].
  - intros Hz Hn. apply Hz. intros [b He]. apply Hn. exists (empty_specification x).
    destruct b; (eapply S.equivalent_trans; [exact He | apply S.equivalent_sym; apply Hsub]).
Qed.

Definition membership_specification x (i : S.indices x) : specification x.
Proof.
  exists (member 0 1, [i]). cbn [bounded length fst snd]. split; lia.
Defined.

Theorem successor_extends_transitive x :
  S.transitive x -> forall y, S.member y x -> S.member y (definable_successor x).
Proof.
  intros Htrans y Hy Hn. apply Hy. intros [i He].
  assert (Hix : S.member (S.child x i) x).
  { intros Hnot. apply Hnot. exists i. apply S.equivalent_refl. }
  assert (Hdef : S.equivalent (S.child x i) (defined_subset x (membership_specification x i))).
  { apply S.extensionality. intro z. split.
    - intro Hz. apply defined_subset_membership. split.
      + exact (Htrans _ _ Hix Hz).
      + change (~ ~ S.member z (S.child x i)). tauto.
    - intro Hz. apply defined_subset_membership in Hz as [_ Hz].
      change (~ ~ S.member z (S.child x i)) in Hz. now apply S.member_stable. }
  apply Hn. exists (membership_specification x i).
  eapply S.equivalent_trans; eassumption.
Qed.

Theorem successor_transitive x :
  S.transitive x -> S.transitive (definable_successor x).
Proof.
  intros Hx y z Hy Hz. apply successor_extends_transitive; [exact Hx |].
  exact (successor_contains_only_subsets x y Hy z Hz).
Qed.

Definition pair_specification x (i j : S.indices x) : specification x.
Proof.
  exists (disj (equal 0 1) (equal 0 2), [i; j]).
  cbn [bounded disj neg length fst snd]. repeat split; lia.
Defined.

Lemma pair_predicate x (i j : S.indices x) z :
  holds x (disj (equal 0 1) (equal 0 2)) (parameter_environment x z [i; j]) <->
  S.member z (S.pair (S.child x i) (S.child x j)).
Proof.
  change (((~ ~ ~ S.equivalent z (S.child x i)) -> ~ ~ S.equivalent z (S.child x j)) <->
    S.member z (S.pair (S.child x i) (S.child x j))).
  split.
  - intros H Hn.
    assert (Hni : ~ ~ ~ S.equivalent z (S.child x i)).
    { intro Hi. apply Hn. exists true. now apply S.equivalent_stable. }
    apply Hn. exists false. apply S.equivalent_stable. now apply H.
  - intros H Hni Hnj. apply H. intros [b Hb]. destruct b.
    + apply Hni. tauto.
    + exact (Hnj Hb).
Qed.

Lemma defined_pair x (i j : S.indices x) :
  S.equivalent (defined_subset x (pair_specification x i j))
    (S.pair (S.child x i) (S.child x j)).
Proof.
  apply S.extensionality. intro z. split.
  - intro Hz. apply defined_subset_membership in Hz as [_ Hz]. now apply pair_predicate.
  - intro Hz. apply defined_subset_membership. split.
    + apply S.member_stable. intro Hn. apply Hz. intros [b Hb].
      assert (Hchild : S.member (S.child x (if b then i else j)) x).
      { intro Hnot. apply Hnot. exists (if b then i else j). apply S.equivalent_refl. }
      apply Hn. apply (S.member_left (S.child x (if b then i else j)) z x);
        [apply S.equivalent_sym | exact Hchild].
      destruct b; exact Hb.
    + now apply pair_predicate.
Qed.

Theorem pair_in_definable_successor x y z :
  S.member y x -> S.member z x -> S.member (S.pair y z) (definable_successor x).
Proof.
  intros Hy Hz Hn. apply Hy. intros [i Hi]. apply Hz. intros [j Hj].
  apply Hn. exists (pair_specification x i j).
  eapply S.equivalent_trans.
  - apply S.pair_respects; eassumption.
  - apply S.equivalent_sym. apply defined_pair.
Qed.

Definition whole_specification x : specification x.
Proof. exists (equal 0 0, []). cbn [bounded length fst snd]. split; lia. Defined.

Theorem whole_in_definable_successor x : S.member x (definable_successor x).
Proof.
  intro Hn. apply Hn. exists (whole_specification x). apply S.extensionality. intro z. split.
  - intro Hz. apply defined_subset_membership. split; [exact Hz |].
    change (~ ~ S.equivalent z z). intros Hnot. apply Hnot, S.equivalent_refl.
  - intro Hz. apply defined_subset_membership in Hz. exact (proj1 Hz).
Qed.

Definition union_specification x (i : S.indices x) : specification x.
Proof.
  exists (ex (conj (member 0 2) (member 1 0)), [i]).
  cbn [bounded ex neg conj length fst snd]. repeat split; lia.
Defined.

Lemma union_predicate x (i : S.indices x) z : S.transitive x ->
  holds x (ex (conj (member 0 2) (member 1 0))) (parameter_environment x z [i]) <->
  S.member z (S.unions (S.child x i)).
Proof.
  intro Htrans. unfold holds. rewrite I.satisfies_ex. split.
  - intros H. apply S.union_membership. intro Hn. apply H. intros [w [_ Hw]].
    apply I.satisfies_conj in Hw as [Hwx Hzw].
    change (~ ~ S.member w (S.child x i)) in Hwx.
    change (~ ~ S.member z w) in Hzw.
    apply S.member_stable in Hwx, Hzw. apply Hn. exists w. tauto.
  - intro H. apply S.union_membership in H. intro Hn. apply H. intros [w [Hwx Hzw]].
    apply Hn. exists w. split.
    + apply (Htrans (S.child x i) w); [|exact Hwx].
      intros Hnot. apply Hnot. exists i. apply S.equivalent_refl.
    + apply I.satisfies_conj. split.
      * change (~ ~ S.member w (S.child x i)). tauto.
      * change (~ ~ S.member z w). tauto.
Qed.

Lemma defined_union x (i : S.indices x) : S.transitive x ->
  S.equivalent (defined_subset x (union_specification x i)) (S.unions (S.child x i)).
Proof.
  intro Htrans. apply S.extensionality. intro z. split.
  - intro Hz. apply defined_subset_membership in Hz as [_ Hz].
    now apply union_predicate in Hz.
  - intro Hz. apply defined_subset_membership. split.
    + apply S.member_stable. intro Hn. apply S.union_membership in Hz.
      apply Hz. intros [w [Hwx Hzw]]. apply Hn.
      apply (Htrans w z); [|exact Hzw]. apply (Htrans (S.child x i) w); [|exact Hwx].
      intros Hnot. apply Hnot. exists i. apply S.equivalent_refl.
    + now apply union_predicate.
Qed.

Theorem union_in_definable_successor x y : S.transitive x ->
  S.member y x -> S.member (S.unions y) (definable_successor x).
Proof.
  intros Htrans Hy Hn. apply Hy. intros [i Hi].
  apply Hn. exists (union_specification x i). eapply S.equivalent_trans.
  - exact (S.unions_respects y (S.child x i) Hi).
  - apply S.equivalent_sym. now apply defined_union.
Qed.

(* At an ordinal alpha this is the usual union of Def(L_beta), beta < alpha.
   The function is defined on representatives. No theorem here identifies all
   equivalent ordinal representatives or validates ZF for its union class. *)
Fixpoint hierarchy (alpha : S.tree) : S.tree :=
  match alpha with
  | S.node A f => S.unions (S.node A (fun i => definable_successor (hierarchy (f i))))
  end.

Theorem hierarchy_zero : S.equivalent (hierarchy S.empty) S.empty.
Proof.
  apply S.empty_if_no_members. intros z Hz. apply Hz. intros [[i j] He]. destruct i.
Qed.

Theorem hierarchy_one : S.equivalent (hierarchy (S.natural 1)) (S.singleton S.empty).
Proof.
  change (S.equivalent
    (S.unions (S.node (option Empty_set)
      (fun i => definable_successor (hierarchy
        (match i with None => S.empty | Some j => match j with end end)))))
    (S.singleton S.empty)).
  apply (S.unions_constant _ _ _ None). intros [i|]; [destruct i |].
  apply successor_of_empty. intros z Hz.
  apply (S.empty_has_no_members z).
  exact (S.member_right _ _ z hierarchy_zero Hz).
Qed.

Theorem hierarchy_transitive alpha : S.transitive (hierarchy alpha).
Proof.
  induction alpha as [A f IH]. cbn [hierarchy]. apply S.unions_transitive.
  intro i. now apply successor_transitive.
Qed.

Lemma hierarchy_next alpha z :
  S.member z (definable_successor (hierarchy alpha)) ->
  S.member z (hierarchy (S.successor alpha)).
Proof.
  intro Hz. cbn [hierarchy S.successor].
  apply (S.family_member_unions _ _ None). exact Hz.
Qed.

(* This is a stable class of elements of the hierarchy, rather than an
   assertion that the class satisfies ZF or Choice. *)
Definition in_constructible_class x := ~ ~ exists alpha, S.member x (hierarchy alpha).
Theorem empty_constructible : in_constructible_class S.empty.
Proof.
  intro Hn. apply Hn. exists (S.natural 1).
  apply (S.member_right _ _ S.empty (S.equivalent_sym _ _ hierarchy_one)).
  apply S.pair_contains_left.
Qed.
Theorem constructible_class_transitive x y :
  in_constructible_class x -> S.member y x -> in_constructible_class y.
Proof.
  intros Hx Hy Hn. apply Hx. intros [alpha Ha]. apply Hn. exists alpha.
  exact (hierarchy_transitive alpha x y Ha Hy).
Qed.

Lemma common_stage x y : in_constructible_class x -> in_constructible_class y ->
  ~ ~ exists alpha, S.member x (hierarchy alpha) /\ S.member y (hierarchy alpha).
Proof.
  intros Hx Hy Hn. apply Hx. intros [a Ha]. apply Hy. intros [b Hb].
  apply Hn. exists (S.node bool (fun c => if c then a else b)). split; cbn [hierarchy].
  - apply (S.family_member_unions _ _ true).
    apply successor_extends_transitive; [apply hierarchy_transitive | exact Ha].
  - apply (S.family_member_unions _ _ false).
    apply successor_extends_transitive; [apply hierarchy_transitive | exact Hb].
Qed.

Theorem pair_constructible x y :
  in_constructible_class x -> in_constructible_class y -> in_constructible_class (S.pair x y).
Proof.
  intros Hx Hy Hn. apply (common_stage x y Hx Hy). intros [a [Ha Hb]].
  apply Hn. exists (S.successor a). apply hierarchy_next.
  now apply pair_in_definable_successor.
Qed.

Theorem hierarchy_stage_constructible alpha : in_constructible_class (hierarchy alpha).
Proof.
  intro Hn. apply Hn. exists (S.successor alpha). apply hierarchy_next.
  apply whole_in_definable_successor.
Qed.

Theorem union_constructible x : in_constructible_class x -> in_constructible_class (S.unions x).
Proof.
  intros Hx Hn. apply Hx. intros [alpha Ha]. apply Hn. exists (S.successor alpha).
  apply hierarchy_next. apply union_in_definable_successor; [apply hierarchy_transitive | exact Ha].
Qed.
End Constructibility.
