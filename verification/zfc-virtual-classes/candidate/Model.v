From CoqCP Require Import Options.
From Trusted Require Import SetTheory.
From Submission Require Import Semantics StableSets.

(* Checked progress toward an outright consistency proof. This file validates
   seven axiom families in a concrete constructive interpretation. It is not a
   model of all ZFC; Replacement and Choice are not asserted here. *)
Module TreeModel.
Import SetTheory.
Module S := StableSets.
Module N := NegativeSemantics.
Definition sat := N.satisfies S.member S.equivalent.
Definition valid := N.valid S.member S.equivalent.

Lemma sat_member i j e : sat (member i j) e <-> S.member (e i) (e j).
Proof. split; [apply S.member_stable | cbn [sat N.satisfies]; tauto]. Qed.
Lemma sat_equal i j e : sat (equal i j) e <-> S.equivalent (e i) (e j).
Proof. split; [apply S.equivalent_stable | cbn [sat N.satisfies]; tauto]. Qed.
Lemma sat_conj p q e : sat (conj p q) e <-> sat p e /\ sat q e.
Proof. apply N.satisfies_conj. Qed.
Lemma sat_iff p q e : sat (SetTheory.iff p q) e <-> (sat p e <-> sat q e).
Proof. apply N.satisfies_iff. Qed.
Lemma sat_ex p e : sat (ex p) e <-> ~ ~ exists x, sat p (N.extend x e).
Proof. apply N.satisfies_ex. Qed.

Theorem validates_extensionality : valid extensionality.
Proof.
  intros e H. apply sat_equal. apply S.extensionality. intro z.
  specialize (H z). apply sat_iff in H.
  cbn [sat N.satisfies N.extend] in H.
  split; intro Hz; apply S.member_stable.
  - apply (proj1 H). tauto.
  - apply (proj2 H). tauto.
Qed.

Theorem validates_pairing : valid pairing.
Proof.
  intro e. apply sat_ex. intro Hn. apply Hn. exists (S.pair (e 0) (e 1)).
  apply sat_conj. split; apply sat_member.
  - apply S.pair_contains_left.
  - apply S.pair_contains_right.
Qed.

Theorem validates_foundation : valid foundation.
Proof.
  intros e H. apply sat_ex in H. apply sat_ex. intro Hn.
  apply H. intros [z Hz]. apply sat_member in Hz.
  apply (S.foundation_minimal (e 0) z Hz).
  intros [y [Hy Hminimal]]. apply Hn. exists y. apply sat_conj. split.
  - apply sat_member. exact Hy.
  - cbn [sat N.satisfies neg]. intros w Hw Hwx.
    apply S.member_stable in Hw, Hwx. exact (Hminimal w Hw Hwx).
Qed.

Theorem validates_union : valid union.
Proof.
  intro e. apply sat_ex. intros Hn. apply Hn. exists (S.unions (e 0)).
  cbn [sat N.satisfies]. intros y z Hzy Hyx.
  apply S.member_stable in Hzy, Hyx. intros Hnot. apply Hnot.
  apply S.union_membership. intros Hempty. apply Hempty. exists y. tauto.
Qed.

Theorem validates_power : valid power.
Proof.
  intro e. apply sat_ex. intros Hn. apply Hn. exists (S.powerset (e 0)).
  cbn [sat N.satisfies]. intros y Hsubset Hnot. apply Hnot.
  apply S.power_contains_subset. intros z Hz. apply S.member_stable.
  apply Hsubset. tauto.
Qed.

Theorem validates_separation p : valid (separation p).
Proof.
  intro e. set (P := fun z => sat p (N.extend z e)).
  assert (Hstable : forall z, ~ ~ P z -> P z).
  { intro z. apply N.stable. }
  assert (Hrespect : forall z z', S.equivalent z z' -> P z -> P z').
  { intros z z' He. unfold P, sat.
    apply (proj1 (N.equivalent_environments S.member S.equivalent
      S.equivalent_refl S.equivalent_sym S.equivalent_trans S.member_left S.member_right
      p (N.extend z e) (N.extend z' e) (fun i =>
        match i with 0 => He | S n => S.equivalent_refl (e n) end))). }
  apply sat_ex. intro Hn. apply Hn. exists (S.separate P (e 0)).
  intro z. apply sat_iff.
  assert (Hsep := S.separation_membership P (e 0) Hstable Hrespect z).
  assert (Hrename :
    sat (rename sep_rename p) (N.extend z (N.extend (S.separate P (e 0)) e)) <-> P z).
  { unfold P, sat. rewrite N.satisfies_rename. apply N.environment_ext.
    intros [|i]; reflexivity. }
  split.
  - intro Hz. apply sat_member in Hz. apply Hsep in Hz as [Hz HP].
    apply sat_conj. split; [apply sat_member; exact Hz | now apply Hrename].
  - intro Hz. apply sat_conj in Hz as [Hz HP]. apply sat_member in Hz.
    apply sat_member. apply Hsep. split; [exact Hz | now apply Hrename in HP].
Qed.

Theorem validates_infinity : valid infinity.
Proof.
  intro e. apply sat_ex. intro Hn. apply Hn. exists S.omega. apply sat_conj. split.
  - apply sat_ex. intro Hempty. apply Hempty. exists S.empty. apply sat_conj. split.
    + apply sat_member. apply S.omega_contains_empty.
    + cbn [sat N.satisfies neg]. intros z Hz. apply S.member_stable in Hz.
      exact (S.empty_has_no_members z Hz).
  - intros y Hy. apply S.member_stable in Hy. apply sat_ex. intro Hsucc. apply Hsucc.
    exists (S.successor y). apply sat_conj. split.
    + apply sat_member. now apply S.omega_contains_successor.
    + intro z. apply sat_iff. split.
      * intro Hz. apply sat_member in Hz. apply S.successor_membership in Hz.
        cbn [sat N.satisfies disj neg]. intros Hnotmem Hnoteq.
        apply Hz. intros [Hm | He].
        -- apply Hnotmem. tauto.
        -- apply Hnoteq. exact He.
      * intro Hz. cbn [sat N.satisfies disj neg] in Hz. apply sat_member.
        apply S.successor_membership. intro Hnone.
        assert (Hnm : ~ ~ ~ S.member z y).
        { intro Hm. apply S.member_stable in Hm. apply Hnone. now left. }
        pose proof (Hz Hnm) as He. apply S.equivalent_stable in He.
        apply Hnone. now right.
Qed.

(* A sufficient route, with both unfinished premises explicit. This is not
   supplied as SOLUTION.correct and does not add assumptions to the library. *)
Theorem consistency_if_remaining_axioms :
  (forall p, valid (replacement p)) -> valid choice -> SetTheory.consistent.
Proof.
  intros Hreplacement Hchoice.
  apply (N.consistency_from_model S.member S.equivalent S.equivalent_refl
    S.equivalent_sym S.equivalent_trans S.member_left S.member_right S.empty).
  intros p Hax. destruct Hax.
  - exact validates_extensionality.
  - exact validates_foundation.
  - exact validates_pairing.
  - exact validates_union.
  - exact validates_power.
  - exact validates_infinity.
  - apply validates_separation.
  - apply Hreplacement.
  - exact Hchoice.
Qed.
End TreeModel.
