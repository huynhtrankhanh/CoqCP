From CoqCP Require Import Options.
From Submission Require Import KoxiaModular KoxiaPrimeCertificate.
From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory Lists.List Bool.Bool Lia Sorting.Permutation.
Import ListNotations.
Local Open Scope Z_scope.

Definition trialPrime (p : Z) (bound : nat) : bool :=
  forallb (fun d => negb (Z.eqb (p mod Z.of_nat d) 0)) (seq 2 (bound-1)).
Lemma trialPrime_sound p bound :
  1 < p -> p < (Z.of_nat bound + 1)^2 -> trialPrime p bound = true -> Z.prime p.
Proof.
  intros hp square checked. unfold Z.prime. split; [exact hp |].
  assert (small : forall d, 1 < d <= Z.of_nat bound -> ~ Z.divide d p).
  { intros d range divided. unfold trialPrime in checked. rewrite forallb_forall in checked.
    specialize (checked (Z.to_nat d)).
    assert (member : In (Z.to_nat d) (seq 2 (bound-1))) by (apply in_seq; lia).
    specialize (checked member). rewrite Z2Nat.id in checked by lia.
    apply negb_true_iff, Z.eqb_neq in checked. apply checked.
    apply Z.mod_divide; [lia | exact divided]. }
  intros d range [q product].
  destruct (Z_le_dec d (Z.of_nat bound)) as [within | above].
  - apply (small d ltac:(lia)). exists q. exact product.
  - assert (positive : 1 < q) by nia.
    assert (within : q <= Z.of_nat bound) by (rewrite Z.pow_2_r in square; nia).
    apply (small q ltac:(lia)). exists d. nia.
Qed.

Theorem koxiaModulus_prime : Z.prime koxiaModulus.
Proof.
  exact koxia_prime_from_binary_certificate.
Qed.
