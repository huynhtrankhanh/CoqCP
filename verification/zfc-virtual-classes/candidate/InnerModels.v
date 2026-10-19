From CoqCP Require Import Options SetTheory.
From Submission Require Import Semantics.

(* Relativization is the bridge needed by an inner-model construction such as
   L. Proving this bridge does not assert that a particular class is an inner
   model. All hypotheses of the final consistency lemmas remain explicit. *)
Module InnerModels.
Import SetTheory.
Module N := NegativeSemantics.

Fixpoint relativize (guard p : formula) : formula :=
  match p with
  | falsity => falsity
  | equal i j => equal i j
  | member i j => member i j
  | implies p q => implies (relativize guard p) (relativize guard q)
  | all p => all (implies guard (relativize guard p))
  end.

Section Interpretation.
Context {D : Type} (membership equality : D -> D -> Prop).
Fixpoint satisfies (M : D -> Prop) (p : formula) (e : nat -> D) : Prop :=
  match p with
  | falsity => False
  | equal i j => ~ ~ equality (e i) (e j)
  | member i j => ~ ~ membership (e i) (e j)
  | implies p q => satisfies M p e -> satisfies M q e
  | all p => forall x, M x -> satisfies M p (N.extend x e)
  end.

Lemma stable M p e : ~ ~ satisfies M p e -> satisfies M p e.
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in e |- *; cbn [satisfies].
  - tauto.
  - tauto.
  - tauto.
  - intros H a. apply IHq. intro Hn. apply H. intro Hf. exact (Hn (Hf a)).
  - intros H x Hx. apply IH. intro Hn. apply H. intro Hf. exact (Hn (Hf x Hx)).
Qed.

Lemma satisfies_conj M p q e :
  satisfies M (conj p q) e <-> satisfies M p e /\ satisfies M q e.
Proof.
  cbn [conj neg satisfies]. split.
  - intro H. split.
    + apply stable. intro Hn. apply H. tauto.
    + apply stable. intro Hn. apply H. tauto.
  - tauto.
Qed.
Lemma satisfies_iff M p q e :
  satisfies M (SetTheory.iff p q) e <-> (satisfies M p e <-> satisfies M q e).
Proof. unfold SetTheory.iff. rewrite satisfies_conj. reflexivity. Qed.
Lemma satisfies_ex M p e :
  satisfies M (ex p) e <-> ~ ~ exists x, M x /\ satisfies M p (N.extend x e).
Proof. cbn [ex neg satisfies]. firstorder. Qed.

Lemma interpretation M guard :
  (forall e x, N.satisfies membership equality guard (N.extend x e) <-> M x) ->
  forall p e, N.satisfies membership equality (relativize guard p) e <-> satisfies M p e.
Proof.
  intros Hguard p. induction p as [|i j|i j|p IHp q IHq|p IH]; intro e;
    cbn [relativize N.satisfies satisfies]; try reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - split.
    + intros H x Hx. apply IH. apply H. now apply Hguard.
    + intros H x Hx. apply IH. apply H. now apply Hguard in Hx.
Qed.

Lemma subtype_interpretation M p (e : nat -> {x : D | M x}) e' :
  (forall i, proj1_sig (e i) = e' i) ->
  (N.satisfies (fun x y => membership (proj1_sig x) (proj1_sig y))
    (fun x y => equality (proj1_sig x) (proj1_sig y)) p e <-> satisfies M p e').
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in e, e' |- *; intro He;
    cbn [N.satisfies satisfies].
  - reflexivity.
  - now rewrite (He i), (He j).
  - now rewrite (He i), (He j).
  - rewrite (IHp _ _ He), (IHq _ _ He). reflexivity.
  - split.
    + intros H x Hx.
      assert (Henv : forall i, proj1_sig (N.extend (exist M x Hx) e i) = N.extend x e' i).
      { intros [|i]; [reflexivity | apply He]. }
      apply (proj1 (IH _ _ Henv)). apply H.
    + intros H [x Hx].
      assert (Henv : forall i, proj1_sig (N.extend (exist M x Hx) e i) = N.extend x e' i).
      { intros [|i]; [reflexivity | apply He]. }
      apply (proj2 (IH _ _ Henv)). exact (H x Hx).
Qed.

Context
  (equality_refl : forall x, equality x x)
  (equality_sym : forall x y, equality x y -> equality y x)
  (equality_trans : forall x y z, equality x y -> equality y z -> equality x z)
  (membership_left : forall x y z, equality x y -> membership x z -> membership y z)
  (membership_right : forall x y z, equality x y -> membership z x -> membership z y).

Lemma equivalent_environments M p e e' :
  (forall i, equality (e i) (e' i)) -> (satisfies M p e <-> satisfies M p e').
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in e, e' |- *; intro He;
    cbn [satisfies].
  - reflexivity.
  - assert (Hforward : equality (e i) (e j) -> equality (e' i) (e' j)).
    { intro H. eapply equality_trans; [apply equality_sym; apply He |].
      eapply equality_trans; [exact H | apply He]. }
    assert (Hbackward : equality (e' i) (e' j) -> equality (e i) (e j)).
    { intro H. eapply equality_trans; [apply He |].
      eapply equality_trans; [exact H | apply equality_sym; apply He]. }
    split; intros H Hn; apply H; intro Hpos; apply Hn; auto.
  - assert (Hforward : membership (e i) (e j) -> membership (e' i) (e' j)).
    { intro H. eapply membership_right; [apply He |].
      eapply membership_left; [apply He | exact H]. }
    assert (Hbackward : membership (e' i) (e' j) -> membership (e i) (e j)).
    { intro H. eapply membership_right; [apply equality_sym; apply He |].
      eapply membership_left; [apply equality_sym; apply He | exact H]. }
    split; intros H Hn; apply H; intro Hpos; apply Hn; auto.
  - rewrite (IHp _ _ He), (IHq _ _ He). reflexivity.
  - assert (Hx : forall x, satisfies M p (N.extend x e) <-> satisfies M p (N.extend x e')).
    { intro x. apply IH. intros [|i]; [apply equality_refl | apply He]. }
    split; intros H x Hx'; apply Hx; now apply H.
Qed.

Theorem consistency_from_inner_model M :
  (exists x, M x) ->
  (forall p, set_axiom p -> forall e, (forall i, M (e i)) -> satisfies M p e) ->
  SetTheory.consistent.
Proof.
  intros [x Hx] Haxioms.
  apply (@N.consistency_from_model {x : D | M x}
    (fun a b => membership (proj1_sig a) (proj1_sig b))
    (fun a b => equality (proj1_sig a) (proj1_sig b))
    (fun a => equality_refl (proj1_sig a))
    (fun a b => equality_sym (proj1_sig a) (proj1_sig b))
    (fun a b c => equality_trans (proj1_sig a) (proj1_sig b) (proj1_sig c))
    (fun a b c => membership_left (proj1_sig a) (proj1_sig b) (proj1_sig c))
    (fun a b c => membership_right (proj1_sig a) (proj1_sig b) (proj1_sig c))
    (exist M x Hx)).
  intros p Hp e.
  apply (proj2 (subtype_interpretation M p e (fun i => proj1_sig (e i)) (fun _ => eq_refl))).
  apply Haxioms; [exact Hp | intro i; exact (proj2_sig (e i))].
Qed.

Theorem consistency_from_relativization M guard :
  (exists x, M x) ->
  (forall e x, N.satisfies membership equality guard (N.extend x e) <-> M x) ->
  (forall p, set_axiom p -> forall e, (forall i, M (e i)) ->
    N.satisfies membership equality (relativize guard p) e) ->
  SetTheory.consistent.
Proof.
  intros Hinh Hguard Haxioms. apply (consistency_from_inner_model M Hinh).
  intros p Hp e He. apply (proj1 (interpretation M guard Hguard p e)).
  exact (Haxioms p Hp e He).
Qed.
End Interpretation.
End InnerModels.
