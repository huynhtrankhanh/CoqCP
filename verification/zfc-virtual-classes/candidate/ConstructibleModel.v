From CoqCP Require Import Options SetTheory.
From Submission Require Import Semantics InnerModels StableSets Constructibility.

(* Initial axiom validations for the stable hierarchy class. These are not
   asserted to constitute the full constructible-inner-model theorem. *)
Module ConstructibleModel.
Import SetTheory.
Module S := StableSets.
Module C := Constructibility.
Module I := InnerModels.
Definition domain := C.in_constructible_class.
Definition sat := I.satisfies S.member S.equivalent domain.
Definition valid p := forall e, (forall i, domain (e i)) -> sat p e.

Lemma sat_member i j e : sat (member i j) e <-> S.member (e i) (e j).
Proof. split; [apply S.member_stable | cbn [sat I.satisfies]; tauto]. Qed.
Lemma sat_equal i j e : sat (equal i j) e <-> S.equivalent (e i) (e j).
Proof. split; [apply S.equivalent_stable | cbn [sat I.satisfies]; tauto]. Qed.
Lemma sat_conj p q e : sat (conj p q) e <-> sat p e /\ sat q e.
Proof. apply I.satisfies_conj. Qed.
Lemma sat_iff p q e : sat (SetTheory.iff p q) e <-> (sat p e <-> sat q e).
Proof. apply I.satisfies_iff. Qed.
Lemma sat_ex p e : sat (ex p) e <->
  ~ ~ exists x, domain x /\ sat p (NegativeSemantics.extend x e).
Proof. apply I.satisfies_ex. Qed.

Theorem validates_extensionality : valid extensionality.
Proof.
  intros e He H. apply sat_equal. apply S.extensionality. intro z. split.
  - intro Hz. assert (Hdom := C.constructible_class_transitive _ _ (He 0) Hz).
    specialize (H z Hdom). apply sat_iff in H. apply S.member_stable.
    apply (proj1 H). cbn [sat I.satisfies NegativeSemantics.extend]. tauto.
  - intro Hz. assert (Hdom := C.constructible_class_transitive _ _ (He 1) Hz).
    specialize (H z Hdom). apply sat_iff in H. apply S.member_stable.
    apply (proj2 H). cbn [sat I.satisfies NegativeSemantics.extend]. tauto.
Qed.

Theorem validates_foundation : valid foundation.
Proof.
  intros e He H. apply sat_ex in H. apply sat_ex. intro Hn.
  apply H. intros [z [_ Hz]]. apply sat_member in Hz.
  apply (S.foundation_minimal (e 0) z Hz). intros [y [Hy Hminimal]].
  apply Hn. exists y. split.
  - exact (C.constructible_class_transitive _ _ (He 0) Hy).
  - apply sat_conj. split.
    + apply sat_member. exact Hy.
    + cbn [sat I.satisfies neg]. intros w Hw Hmem Hbad.
      apply S.member_stable in Hmem, Hbad. exact (Hminimal w Hmem Hbad).
Qed.

Theorem validates_pairing : valid pairing.
Proof.
  intros e He. apply sat_ex. intro Hn. apply Hn. exists (S.pair (e 0) (e 1)). split.
  - apply C.pair_constructible; apply He.
  - apply sat_conj. split; apply sat_member.
    + apply S.pair_contains_left.
    + apply S.pair_contains_right.
Qed.

Theorem validates_union : valid union.
Proof.
  intros e He. apply sat_ex. intro Hn. apply Hn. exists (S.unions (e 0)). split.
  - apply C.union_constructible, He.
  - cbn [sat I.satisfies]. intros y Hy z Hz Hzy Hya Hnot.
    apply S.member_stable in Hzy, Hya. apply Hnot. apply S.union_membership.
    intros Hnone. apply Hnone. exists y. tauto.
Qed.
End ConstructibleModel.
