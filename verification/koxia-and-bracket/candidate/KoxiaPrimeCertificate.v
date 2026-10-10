From CoqCP Require Import Options.
From Submission Require Import KoxiaModular.
From Stdlib Require Import ZArith.ZArith ZArith.Znumtheory Bool.Bool Lia.
Local Open Scope Z_scope.

(* Multiples of 2, 3 or 5 cannot divide a modulus coprime to those factors.
   Skip their expensive modulus divisions; the lemma checks this implication. *)
Definition checkDivisor p d : bool :=
  if Z.even d then true else
  if Z.eqb (d mod 3) 0 then true else
  if Z.eqb (d mod 5) 0 then true else negb (Z.eqb (p mod d) 0).
Lemma checkDivisor_sound p d : 0<d ->
  p mod 2<>0 -> p mod 3<>0 -> p mod 5<>0 ->
  checkDivisor p d=true -> p mod d<>0.
Proof.
  intros positive two three five checked.
  assert (nonfactor : forall f, 0<f -> p mod f<>0 -> d mod f=0 -> p mod d<>0).
  { intros f hf hp hd bad. apply hp. apply Z.mod_divide; [lia|].
    eapply Z.divide_trans.
    - apply Z.mod_divide; [lia|exact hd].
    - apply Z.mod_divide; [lia|exact bad]. }
  unfold checkDivisor in checked.
  destruct (Z.even d) eqn:even.
  - apply (nonfactor 2); [lia|exact two|].
    apply Z.even_spec in even. destruct even as [k hk].
    apply Z.mod_divide; [lia|]. exists k. lia.
  - destruct (Z.eqb (d mod 3) 0) eqn:third.
    + apply (nonfactor 3); [lia|exact three|]. apply Z.eqb_eq in third. exact third.
    + destruct (Z.eqb (d mod 5) 0) eqn:fifth.
      * apply (nonfactor 5); [lia|exact five|]. apply Z.eqb_eq in fifth. exact fifth.
      * apply negb_true_iff, Z.eqb_neq in checked. exact checked.
Qed.

(* A balanced binary counter bounds reduction depth logarithmically. Both
   halves cover adjacent divisor ranges; odd counts check the final divisor. *)
Fixpoint divisorCheck p start (fuel : positive) : bool :=
  match fuel with
  | xH => checkDivisor p start
  | xO half => divisorCheck p start half && divisorCheck p (start+Z.pos half) half
  | xI half => divisorCheck p start half && divisorCheck p (start+Z.pos half) half &&
      checkDivisor p (start+2*Z.pos half)
  end.
Lemma divisorCheck_sound p start fuel : divisorCheck p start fuel=true ->
  forall d, start <= d < start+Z.pos fuel -> checkDivisor p d=true.
Proof.
  induction fuel as [half IH|half IH|] in start |- *.
  - cbn [divisorCheck]. rewrite !andb_true_iff. intros [[first second] last] d range.
    rewrite Pos2Z.inj_xI in range.
    destruct (Z_lt_ge_dec d (start+Z.pos half)) as [left|right].
    + apply (IH start first d). lia.
    + destruct (Z_lt_ge_dec d (start+2*Z.pos half)) as [middle|final].
      * apply (IH (start+Z.pos half) second d). lia.
      * assert (d=start+2*Z.pos half) by lia. subst d.
        exact last.
  - cbn [divisorCheck]. rewrite andb_true_iff. intros [first second] d range.
    rewrite Pos2Z.inj_xO in range.
    destruct (Z_lt_ge_dec d (start+Z.pos half)) as [left|right].
    + apply (IH start first d). lia.
    + apply (IH (start+Z.pos half) second d). lia.
  - cbn [divisorCheck]. intros checked d range.
    assert (d=start) by (change (start<=d<start+1) in range; lia).
    subst d. exact checked.
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
Lemma koxia_divisor_certificate : divisorCheck koxiaModulus 2 31594%positive=true.
Proof. vm_compute. reflexivity. Qed.
Theorem koxia_prime_from_binary_certificate : Z.prime koxiaModulus.
Proof.
  apply (divisorCheck_prime koxiaModulus 31595).
  - lia.
  - unfold koxiaModulus; lia.
  - unfold koxiaModulus. change (998244353<998307216). lia.
  - intros d range. apply checkDivisor_sound; try lia.
    + unfold koxiaModulus; vm_compute; discriminate.
    + unfold koxiaModulus; vm_compute; discriminate.
    + unfold koxiaModulus; vm_compute; discriminate.
    + apply (divisorCheck_sound koxiaModulus 2 31594%positive koxia_divisor_certificate d).
      change (2<=d<31596). lia.
Qed.
