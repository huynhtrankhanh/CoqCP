From CoqCP Require Import Options SetTheory.

(* A constructive negative interpretation. Classical reasoning in the object
   calculus does not require an excluded-middle axiom in Rocq: all interpreted
   formulas are stable. The separate set-model obligation is not assumed as a
   global axiom and is not claimed to have been discharged. *)
Module NegativeSemantics.
Import SetTheory.
Section Interpretation.
Context {D : Type} (membership equality : D -> D -> Prop).
Definition extend (x : D) (e : nat -> D) (i : nat) :=
  match i with 0 => x | S n => e n end.
Fixpoint satisfies (p : formula) (e : nat -> D) : Prop :=
  match p with
  | falsity => False
  | equal i j => ~ ~ equality (e i) (e j)
  | member i j => ~ ~ membership (e i) (e j)
  | implies p q => satisfies p e -> satisfies q e
  | all p => forall x, satisfies p (extend x e)
  end.

Lemma stable p e : ~ ~ satisfies p e -> satisfies p e.
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in e |- *; cbn [satisfies].
  - tauto.
  - tauto.
  - tauto.
  - intros H a. apply IHq. intros Hn. apply H. intros Hf. exact (Hn (Hf a)).
  - intros H x. apply IH. intros Hn. apply H. intros Hf. exact (Hn (Hf x)).
Qed.

Lemma environment_ext p e e' :
  (forall i, e i = e' i) -> (satisfies p e <-> satisfies p e').
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in e, e' |- *; intro He;
    cbn [satisfies].
  - reflexivity.
  - now rewrite (He i), (He j).
  - now rewrite (He i), (He j).
  - rewrite (IHp _ _ He), (IHq _ _ He). reflexivity.
  - assert (Hx : forall x, satisfies p (extend x e) <-> satisfies p (extend x e')).
    { intro x. apply IH. intros [|i]; cbn [extend]; [reflexivity | apply He]. }
    split; intros H x; apply Hx, H.
Qed.

Lemma satisfies_rename p rho e :
  satisfies (rename rho p) e <-> satisfies p (fun i => e (rho i)).
Proof.
  induction p as [|i j|i j|p IHp q IHq|p IH] in rho, e |- *;
    cbn [satisfies rename]; try reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - assert (Hx : forall x, satisfies (rename (up rho) p) (extend x e) <->
        satisfies p (extend x (fun i => e (rho i)))).
    { intro x. rewrite IH. apply environment_ext. intros [|i]; reflexivity. }
    split; intros H x; apply Hx, H.
Qed.

Lemma satisfies_conj p q e :
  satisfies (conj p q) e <-> satisfies p e /\ satisfies q e.
Proof.
  cbn [conj neg satisfies]. split.
  - intro H. split.
    + apply stable. intro Hn. apply H. tauto.
    + apply stable. intro Hn. apply H. tauto.
  - tauto.
Qed.
Lemma satisfies_iff p q e :
  satisfies (SetTheory.iff p q) e <-> (satisfies p e <-> satisfies q e).
Proof. unfold SetTheory.iff. rewrite satisfies_conj. reflexivity. Qed.
Lemma satisfies_ex p e :
  satisfies (ex p) e <-> ~ ~ exists x, satisfies p (extend x e).
Proof. cbn [ex neg satisfies]. firstorder. Qed.
Lemma satisfies_disj p q e :
  satisfies (disj p q) e <-> ~ ~ (satisfies p e \/ satisfies q e).
Proof.
  cbn [disj neg satisfies]. split.
  - firstorder.
  - intros H Hnp. apply stable. intro Hnq. apply H. tauto.
Qed.

Definition valid p := forall e, satisfies p e.
Definition validates_set_axioms := forall p, set_axiom p -> valid p.

Context
  (equality_refl : forall x, equality x x)
  (equality_sym : forall x y, equality x y -> equality y x)
  (equality_trans : forall x y z, equality x y -> equality y z -> equality x z)
  (membership_left : forall x y z, equality x y -> membership x z -> membership y z)
  (membership_right : forall x y z, equality x y -> membership z x -> membership z y).

Lemma equivalent_environments p e e' :
  (forall i, equality (e i) (e' i)) -> (satisfies p e <-> satisfies p e').
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
  - assert (Hx : forall x, satisfies p (extend x e) <-> satisfies p (extend x e')).
    { intro x. apply IH. intros [|i]; [apply equality_refl | apply He]. }
    split; intros H x; apply Hx, H.
Qed.

Theorem soundness : validates_set_axioms -> forall p, derives p -> valid p.
Proof.
  intros Hset p Hp.
  induction Hp as [p Hax|p q|p q r|p|p j|p q|i|i j k|i j k|i j k|
    p q Hp IHp Hq IHq|p Hp IHp]; unfold valid in *; intro e;
    cbn [satisfies neg shift] in *.
  - exact (Hset p Hax e).
  - tauto.
  - tauto.
  - apply stable.
  - intro H. apply satisfies_rename.
    assert (He : forall i, extend (e j) e i = e (instantiate j i)).
    { intros [|n]; reflexivity. }
    apply (proj1 (environment_ext p _ _ He)). exact (H (e j)).
  - intros H Hp x. apply H. apply satisfies_rename.
    assert (He : forall i, extend x e (S i) = e i) by reflexivity.
    apply (proj2 (environment_ext p _ _ He)). exact Hp.
  - intros Hnot. apply Hnot, equality_refl.
  - intros He Hm Hnot. apply He. intro Hij. apply Hm. intro H.
    apply Hnot. eapply membership_left; eassumption.
  - intros He Hm Hnot. apply He. intro Hij. apply Hm. intro H.
    apply Hnot. eapply membership_right; eassumption.
  - intros Hij Hik Hnot. apply Hij. intro Eij. apply Hik. intro Eik.
    apply Hnot. eapply equality_trans; [apply equality_sym; exact Eij | exact Eik].
  - exact (IHp e (IHq e)).
  - intro x. apply IHp.
Qed.

Theorem consistency_from_model (inhabitant : D) :
  validates_set_axioms -> SetTheory.consistent.
Proof.
  intros Hset Hfalse. exact (soundness Hset falsity Hfalse (fun _ => inhabitant)).
Qed.
End Interpretation.
End NegativeSemantics.
