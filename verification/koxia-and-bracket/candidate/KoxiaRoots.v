From CoqCP Require Import Options.
From Submission Require Import KoxiaModular.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat Lists.List Bool.Bool Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition stageSize (stage : nat) := 2^Z.of_nat stage.
Definition stageRoot stage := modularPower 3 ((koxiaModulus-1)/stageSize stage).
Definition stageInverse stage := modularPower (stageSize stage) (koxiaModulus-2).
Definition verifyStage stage :=
  Z.eqb (modularPower (stageRoot stage) (stageSize stage)) 1 &&
  Z.eqb ((stageSize stage * stageInverse stage) mod koxiaModulus) 1 &&
  (if Nat.eqb stage 0 then Z.eqb (stageRoot stage) 1
   else Z.eqb (modularPower (stageRoot stage) (stageSize (stage-1))) (koxiaModulus-1)).

Lemma stage_checks : forallb verifyStage (seq 0 21) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma verified_stage stage : (stage <= 20)%nat -> verifyStage stage = true.
Proof.
  intro range. pose proof stage_checks as checks. rewrite forallb_forall in checks.
  apply checks. apply in_seq. lia.
Qed.
Lemma stageSize_positive stage : 0 < stageSize stage.
Proof. unfold stageSize. apply Z.pow_pos_nonneg; lia. Qed.
Lemma stageSize_bound stage : (stage <= 20)%nat -> stageSize stage <= 1048576.
Proof.
  intro bound. change (stageSize stage <= stageSize 20).
  unfold stageSize. apply Z.pow_le_mono_r; lia.
Qed.
Lemma stageRoot_bounds stage : 0 <= stageRoot stage < koxiaModulus.
Proof. unfold stageRoot, modularPower. apply fastPower_bounds. unfold koxiaModulus; lia. Qed.

Local Opaque fastPower modularPower.

Theorem stageRoot_full_order stage : (stage <= 20)%nat ->
  (stageRoot stage)^stageSize stage mod koxiaModulus = 1.
Proof.
  intro bound. pose proof (verified_stage stage bound) as verified.
  unfold verifyStage in verified. apply andb_prop in verified as [parts _].
  apply andb_prop in parts as [full _]. apply Z.eqb_eq in full.
  rewrite modularPower_correct in full; [exact full |].
  pose proof (stageSize_positive stage). pose proof (stageSize_bound stage bound).
  change (0 <= stageSize stage < 18446744073709551616). lia.
Qed.
Theorem stageRoot_half_order stage : (1 <= stage <= 20)%nat ->
  (stageRoot stage)^stageSize (stage-1) mod koxiaModulus = koxiaModulus-1.
Proof.
  intro bound. pose proof (verified_stage stage ltac:(lia)) as verified.
  unfold verifyStage in verified. apply andb_prop in verified as [_ half]. assert (nonzero : Nat.eqb stage 0 = false) by (apply Nat.eqb_neq; lia). rewrite nonzero in half.
  apply Z.eqb_eq in half. rewrite modularPower_correct in half; [exact half |].
  pose proof (stageSize_positive (stage-1)). pose proof (stageSize_bound (stage-1) ltac:(lia)).
  change (0 <= stageSize (stage-1) < 18446744073709551616). lia.
Qed.
Theorem stageSize_inverse stage : (stage <= 20)%nat ->
  (stageSize stage * stageInverse stage) mod koxiaModulus = 1.
Proof.
  intro bound. pose proof (verified_stage stage bound) as verified.
  unfold verifyStage in verified. apply andb_prop in verified as [parts _].
  apply andb_prop in parts as [_ inverse]. apply Z.eqb_eq. exact inverse.
Qed.

Local Transparent fastPower modularPower.

Theorem stageRoot_zero : stageRoot 0 = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma root_square_checks : forallb
  (fun stage => Z.eqb ((stageRoot (S stage) * stageRoot (S stage)) mod koxiaModulus) (stageRoot stage))
  (seq 0 20) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem stageRoot_square stage : (stage < 20)%nat ->
  (stageRoot (S stage)*stageRoot (S stage)) mod koxiaModulus = stageRoot stage.
Proof.
  intro bound. pose proof root_square_checks as checks. rewrite forallb_forall in checks.
  specialize (checks stage ltac:(apply in_seq; lia)). apply Z.eqb_eq. exact checks.
Qed.
