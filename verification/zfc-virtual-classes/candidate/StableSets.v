From CoqCP Require Import Options.
From Stdlib Require Import Init.Specif.

(* A constructive attempt at the model obligation, with no quotient, choice,
   excluded middle, or well-foundedness assumption. None of the results here
   asserts that Replacement or Choice has been validated. *)
Module StableSets.
Inductive tree : Type := node (indices : Type) (children : indices -> tree).

Definition indices (x : tree) : Type := match x with node A _ => A end.
Definition child (x : tree) : indices x -> tree := match x with node _ f => f end.

Fixpoint equivalent (x y : tree) {struct x} : Prop :=
  match x, y with
  | node A f, node B g =>
      (forall i : A, ~ ~ exists j : B, equivalent (f i) (g j)) /\
      (forall j : B, ~ ~ exists i : A, equivalent (f i) (g j))
  end.
Definition member (x y : tree) := ~ ~ exists j, equivalent x (child y j).
Definition transitive (x : tree) :=
  forall y z, member y x -> member z y -> member z x.

Lemma equivalent_stable x y : ~ ~ equivalent x y -> equivalent x y.
Proof.
  destruct x as [A f], y as [B g]. cbn [equivalent].
  intros H. split.
  - intros i Hn. apply H. intros [HL HR]. exact (HL i Hn).
  - intros j Hn. apply H. intros [HL HR]. exact (HR j Hn).
Qed.
Lemma member_stable x y : ~ ~ member x y -> member x y.
Proof. unfold member. tauto. Qed.

Theorem equivalent_refl x : equivalent x x.
Proof.
  induction x as [A f IH]. cbn [equivalent]. split; intros i Hn;
    apply Hn; exists i; apply IH.
Qed.
Theorem equivalent_sym x y : equivalent x y -> equivalent y x.
Proof.
  induction x as [A f IH] in y |- *. destruct y as [B g].
  cbn [equivalent]. intros [HL HR]. split.
  - intros j Hn. apply (HR j). intros [i Hi]. apply Hn. exists i. now apply IH.
  - intros i Hn. apply (HL i). intros [j Hj]. apply Hn. exists j. now apply IH.
Qed.
Theorem equivalent_trans x y z :
  equivalent x y -> equivalent y z -> equivalent x z.
Proof.
  induction x as [A f IH] in y, z |- *.
  destruct y as [B g], z as [C h]. cbn [equivalent].
  intros [Hxy Hyx] [Hyz Hzy]. split.
  - intros i Hn. apply (Hxy i). intros [j Hij].
    apply (Hyz j). intros [k Hjk]. apply Hn. exists k. eapply IH; eassumption.
  - intros k Hn. apply (Hzy k). intros [j Hjk].
    apply (Hyx j). intros [i Hij]. apply Hn. exists i. eapply IH; eassumption.
Qed.

Theorem member_left x y z : equivalent x y -> member x z -> member y z.
Proof.
  intros Hxy Hxz Hn. apply Hxz. intros [i Hi]. apply Hn. exists i.
  eapply equivalent_trans; [apply equivalent_sym; exact Hxy | exact Hi].
Qed.
Theorem member_right x y z : equivalent x y -> member z x -> member z y.
Proof.
  destruct x as [A f], y as [B g]. intros [Hxy Hyx] Hz Hn.
  apply Hz. intros [i Hi]. apply (Hxy i). intros [j Hj]. apply Hn. exists j.
  eapply equivalent_trans; eassumption.
Qed.

Theorem extensionality x y :
  (forall z, member z x <-> member z y) -> equivalent x y.
Proof.
  destruct x as [A f], y as [B g]. intro He. cbn [equivalent]. split.
  - intro i. apply (proj1 (He (f i))). intros Hn. apply Hn. exists i. apply equivalent_refl.
  - intros j Hn. assert (Hy : member (g j) (node B g)).
    { intros Hnot. apply Hnot. exists j. apply equivalent_refl. }
    apply (proj2 (He _) ) in Hy. apply Hy. intros [i Hi]. apply Hn. exists i.
    now apply equivalent_sym.
Qed.

Definition empty := node Empty_set (fun e => match e with end).
Definition pair (x y : tree) := node bool (fun b => if b then x else y).
Definition singleton (x : tree) := pair x x.
Definition separate (P : tree -> Prop) (x : tree) :=
  node { i : indices x | P (child x i) } (fun i => child x (proj1_sig i)).
Definition powerset (x : tree) :=
  node (indices x -> Prop)
    (fun P => node {i : indices x | P i} (fun i => child x (proj1_sig i))).

Definition unions (x : tree) :=
  node {i : indices x & indices (child x i)}
    (fun ij => child (child x (projT1 ij)) (projT2 ij)).
Definition successor (x : tree) :=
  node (option (indices x)) (fun i => match i with None => x | Some j => child x j end).
Fixpoint natural (n : nat) := match n with 0 => empty | S k => successor (natural k) end.
Definition omega := node nat natural.

Lemma empty_has_no_members x : ~ member x empty.
Proof. intro H. apply H. intros [i Hi]. destruct i. Qed.
Lemma pair_contains_left x y : member x (pair x y).
Proof. intros Hn. apply Hn. exists true. apply equivalent_refl. Qed.
Lemma pair_contains_right x y : member y (pair x y).
Proof. intros Hn. apply Hn. exists false. apply equivalent_refl. Qed.
Lemma pair_respects x y x' y' :
  equivalent x x' -> equivalent y y' -> equivalent (pair x y) (pair x' y').
Proof.
  intros Hx Hy. cbn [pair equivalent]. split; intros b Hn; apply Hn; exists b;
    destruct b; assumption.
Qed.

Lemma separated_subset P x z : member z (separate P x) -> member z x.
Proof. intros H Hn. apply H. intros [[i Hi] Hz]. apply Hn. now exists i. Qed.
Lemma empty_if_no_members x : (forall z, ~ member z x) -> equivalent x empty.
Proof.
  intro Hnone. apply extensionality. intro z. split; intros H; exfalso.
  - exact (Hnone z H).
  - exact (empty_has_no_members z H).
Qed.

Theorem separation_membership P x :
  (forall z, ~ ~ P z -> P z) ->
  (forall z z', equivalent z z' -> P z -> P z') ->
  forall z, member z (separate P x) <-> member z x /\ P z.
Proof.
  intros Hstable Hrespect z. split.
  - intro H. split.
    + intros Hn. apply H. intros [[i Hi] Hz]. apply Hn. now exists i.
    + apply Hstable. intro Hn. apply H. intros [[i Hi] Hz]. apply Hn.
      eapply Hrespect; [apply equivalent_sym; exact Hz | exact Hi].
  - intros [Hz HP] Hn. apply Hz. intros [i Hi].
    assert (HPi : P (child x i)) by (eapply Hrespect; eassumption).
    apply Hn. exists (exist _ i HPi). exact Hi.
Qed.

(* Structural induction validates induction for stable extensional predicates.
   This does not produce Acc proofs: Acc itself need not be stable. *)
Theorem stable_member_induction (P : tree -> Prop)
  (Hstable : forall x, ~ ~ P x -> P x)
  (Hrespect : forall x y, equivalent x y -> P x -> P y)
  (Hstep : forall x, (forall y, member y x -> P y) -> P x) : forall x, P x.
Proof.
  intro x. induction x as [A f IH]. apply Hstep. intros y Hy.
  apply Hstable. intro Hn. apply Hy. intros [i Hi]. apply Hn.
  eapply Hrespect; [apply equivalent_sym; exact Hi | apply IH].
Qed.

Theorem foundation_minimal x :
  forall z, member z x -> ~ ~ exists y,
    member y x /\ forall w, member w y -> ~ member w x.
Proof.
  apply (stable_member_induction (fun z => member z x -> ~ ~ exists y,
    member y x /\ forall w, member w y -> ~ member w x)).
  - intros z Hnn Hz Hn. apply Hnn. intros H. exact (H Hz Hn).
  - intros z z' He H Hz'. apply H. eapply member_left.
    + apply equivalent_sym. exact He.
    + exact Hz'.
  - intros z IH Hz Hn.
    assert (Hnone : forall w, member w z -> ~ member w x).
    { intros w Hw Hwx. exact (IH w Hw Hwx Hn). }
    apply Hn. now exists z.
Qed.

Theorem union_membership z x :
  member z (unions x) <-> ~ ~ exists y, member y x /\ member z y.
Proof.
  split.
  - intros H Hn. apply H. intros [[i j] Hz]. apply Hn. exists (child x i). split.
    + intros Hnot. apply Hnot. exists i. apply equivalent_refl.
    + intros Hnot. apply Hnot. now exists j.
  - intros H Hn. apply H. intros [y [Hy Hz]]. apply Hy. intros [i Hi].
    pose proof (member_right _ _ _ Hi Hz) as Hzi.
    apply Hzi. intros [j Hj]. apply Hn. exists (existT _ i j). exact Hj.
Qed.

Theorem unions_respects x y : equivalent x y -> equivalent (unions x) (unions y).
Proof.
  intro He. apply extensionality. intro z. split; intro Hz;
    apply union_membership; intro Hn; apply union_membership in Hz; apply Hz.
  - intros [w [Hw Hzw]]. apply Hn. exists w. split.
    + exact (member_right x y w He Hw).
    + exact Hzw.
  - intros [w [Hw Hzw]]. apply Hn. exists w. split.
    + exact (member_right y x w (equivalent_sym _ _ He) Hw).
    + exact Hzw.
Qed.

Lemma unions_constant (I : Type) (f : I -> tree) (t : tree) (i0 : I) :
  (forall i, equivalent (f i) t) -> equivalent (unions (node I f)) t.
Proof.
  intro Heq. apply extensionality. intro z. split.
  - intros H Hn. apply H. intros [[i j] Hj].
    assert (Hzi : member z (f i)).
    { intros Hnot. apply Hnot. now exists j. }
    exact (member_right (f i) t z (Heq i) Hzi Hn).
  - intros H Hn.
    pose proof (member_right t (f i0) z (equivalent_sym _ _ (Heq i0)) H) as Hi.
    apply Hi. intros [j Hj]. apply Hn. exists (existT _ i0 j). exact Hj.
Qed.

Lemma family_member_unions (I : Type) (f : I -> tree) (i : I) z :
  member z (f i) -> member z (unions (node I f)).
Proof. intros H Hn. apply H. intros [j Hj]. apply Hn. exists (existT _ i j). exact Hj. Qed.

Theorem unions_transitive (I : Type) (f : I -> tree) :
  (forall i, transitive (f i)) -> transitive (unions (node I f)).
Proof.
  intros Htrans y z Hy Hz Hn. apply Hy. intros [[i j] He].
  assert (Hyz : member z (child (f i) j)) by (eapply member_right; eassumption).
  assert (Hchild : member (child (f i) j) (f i)).
  { intros Hnot. apply Hnot. exists j. apply equivalent_refl. }
  pose proof (Htrans i _ _ Hchild Hyz) as Hzi.
  apply Hzi. intros [k Hk]. apply Hn. exists (existT _ i k). exact Hk.
Qed.

Theorem power_contains_subset x y :
  (forall z, member z y -> member z x) -> member y (powerset x).
Proof.
  intro Hsubset. intros Hn.
  apply Hn. exists (fun i => member (child x i) y).
  change (equivalent y (separate (fun t => member t y) x)).
  apply extensionality. intro z.
  assert (Hsep : member z (separate (fun t => member t y) x) <->
    member z x /\ member z y).
  { apply (separation_membership (fun t => member t y) x).
    - intro t. exact (member_stable t y).
    - intros t t' He Ht. exact (member_left t t' y He Ht). }
  split.
  - intro Hy. apply Hsep. split; [apply Hsubset; exact Hy | exact Hy].
  - intro H. now apply Hsep in H as [_ H].
Qed.

Theorem successor_membership z x :
  member z (successor x) <-> ~ ~ (member z x \/ equivalent z x).
Proof.
  split.
  - intros H Hn. apply H. intros [[i|] Hi]; apply Hn.
    + left. intros Hnot. apply Hnot. now exists i.
    + now right.
  - intros H Hn. apply H. intros [Hz | Hz].
    + apply Hz. intros [i Hi]. apply Hn. now exists (Some i).
    + apply Hn. now exists None.
Qed.

Theorem successor_respects x y : equivalent x y -> equivalent (successor x) (successor y).
Proof.
  intro He. apply extensionality. intro z. split; intro Hz;
    apply successor_membership; intro Hn; apply successor_membership in Hz; apply Hz.
  - intros [Hmem | Heq]; apply Hn.
    + left. exact (member_right x y z He Hmem).
    + right. eapply equivalent_trans; eassumption.
  - intros [Hmem | Heq]; apply Hn.
    + left. apply (member_right y x z); [now apply equivalent_sym | exact Hmem].
    + right. eapply equivalent_trans; [exact Heq | now apply equivalent_sym].
Qed.

Theorem omega_contains_empty : member empty omega.
Proof. intros Hn. apply Hn. exists 0. apply equivalent_refl. Qed.
Theorem omega_contains_successor x : member x omega -> member (successor x) omega.
Proof.
  intros H Hn. apply H. intros [n He]. apply Hn. exists (S n).
  now apply successor_respects.
Qed.
End StableSets.
