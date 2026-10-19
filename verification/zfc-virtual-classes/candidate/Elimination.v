From CoqCP Require Import Options.
From Trusted Require Import SetTheory VirtualClasses.
Import SetTheory VirtualClasses.

Lemma axiom_derivable a : derives (axiom_formula a).
Proof.
  destruct a; cbn [axiom_formula];
    first [apply d_k | apply d_s | apply d_dne | apply d_inst | apply d_dist |
      apply d_refl | apply d_mem_left | apply d_mem_right | apply d_eq |
      apply d_set; constructor].
Qed.

Theorem eliminate p : proves p -> derives (erase p).
Proof.
  intro h. induction h; cbn [erase] in *.
  - now apply d_set.
  - apply d_k.
  - apply d_s.
  - apply d_dne.
  - apply d_inst.
  - apply d_dist.
  - apply d_refl.
  - apply d_mem_left.
  - apply d_mem_right.
  - apply d_eq.
  - eapply d_mp; eassumption.
  - now apply d_gen.
  - congruence.
Qed.

Theorem embed p : derives p -> proves (core p).
Proof.
  intro h. induction h as [p Hax | p q | p q r | p | p j | p q |
    i | i j k | i j k | i j k | p q Hp IHp Hq IHq | p Hp IHp].
  - now apply p_set.
  - apply p_k.
  - apply p_s.
  - apply p_dne.
  - apply p_inst.
  - apply p_dist.
  - apply p_refl.
  - apply p_mem_left.
  - apply p_mem_right.
  - apply p_eq.
  - eapply p_mp with (p := core p).
    + eapply p_expand; [exact IHp | reflexivity].
    + exact IHq.
  - eapply p_expand; [apply p_gen; exact IHp | reflexivity].
Qed.

Theorem conservative p : proves p <-> derives (erase p).
Proof.
  split; [apply eliminate |]. intro h.
  eapply p_expand; [apply embed; exact h | reflexivity].
Qed.
