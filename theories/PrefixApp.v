From stdpp Require Import numbers list.

Lemma prefixOfAppSingleton {A : Type} (l1 l2 : list A) (x : A) : l1 `prefix_of` l2 ++ [x] -> l1 `prefix_of` l2 \/ l1 = l2 ++ [x].
Proof.
  unfold prefix. intro h.
  destruct h as [w h].
  induction w using rev_ind.
  - right. rewrite app_nil_r in h. easy.
  - left. exists w. pose proof app_inj_tail l2 (l1 ++ w) x x0 as H.
    rewrite <- app_assoc in H. tauto.
Qed.

Lemma prefixAppCases {A : Type} (l x y : list A) (h : l `prefix_of` x ++ y) : l `prefix_of` x \/ exists l', l = x ++ l'.
Proof.
  induction y using rev_ind.
  - left. rewrite app_nil_r in h. tauto.
  - rewrite app_assoc in h. pose proof (prefixOfAppSingleton _ _ _ h). destruct H.
    * tauto.
    * rewrite H. right. exists (y ++ [x0]). rewrite app_assoc. easy.
Qed.

Lemma prefixSingleton {A : Type} (l : list A) (x : A) (h : l `prefix_of` [x]) : l = [] \/ l = [x].
Proof.
  destruct h as [w h]. destruct l.
  - left. reflexivity.
  - right. inversion h. symmetry in H1. pose proof app_eq_nil _ _ H1 as H2. destruct H2 as [Hleft Hright]. rewrite Hleft. reflexivity.
Qed.
