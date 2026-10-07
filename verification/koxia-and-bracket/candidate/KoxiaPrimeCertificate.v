From CoqCP Require Import Options.
From Submission Require Import KoxiaModular.
From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory Bool.Bool Lia.
Local Open Scope Z_scope.

(* A binary divisor counter avoids repeatedly converting a growing unary
   divisor during independent kernel reduction of the certificate. *)
Fixpoint divisorCheck p start fuel : bool :=
  match fuel with
  | O => true
  | S fuel => negb (Z.eqb (p mod start) 0) && divisorCheck p (start+1) fuel
  end.
Lemma divisorCheck_sound p start fuel : divisorCheck p start fuel=true ->
  forall d, start <= d < start+Z.of_nat fuel -> p mod d<>0.
Proof.
  induction fuel as [|fuel IH] in start |- *.
  - intros checked d range. cbn in range. lia.
  - cbn [divisorCheck]. rewrite andb_true_iff. intros [first rest] d range.
    destruct (Z.eq_dec d start) as [->|different].
    + apply negb_true_iff, Z.eqb_neq in first. exact first.
    + apply (IH (start+1) rest d). rewrite Nat2Z.inj_succ in range. lia.
Qed.
Lemma divisorCheck_prime p bound : 0<=bound -> 1<p -> p<(bound+1)^2 ->
  (forall d, 1<d<=bound -> p mod d<>0) -> Z.prime p.
Proof.
  intros boundPositive hp square checked. unfold Z.prime. split; [exact hp|].
  intros d range [q product].
  destruct (Z_le_dec d bound) as [within|above].
  - apply (checked d ltac:(lia)). apply Z.mod_divide; [lia|]. exists q. exact product.
  - assert (positive : 1<q) by nia.
    assert (within : q<=bound) by (rewrite Z.pow_2_r in square; nia).
    apply (checked q ltac:(lia)). apply Z.mod_divide; [lia|]. exists d. nia.
Qed.
Lemma koxia_divisor_certificate : divisorCheck koxiaModulus 2 31594=true.
Proof. vm_compute. reflexivity. Qed.
Theorem koxia_prime_from_binary_certificate : Z.prime koxiaModulus.
Proof.
  apply (divisorCheck_prime koxiaModulus 31595).
  - lia.
  - unfold koxiaModulus; lia.
  - unfold koxiaModulus. change (998244353<998307216). lia.
  - intros d range. apply (divisorCheck_sound koxiaModulus 2 31594 koxia_divisor_certificate d).
    change (2<=d<31596). lia.
Qed.
