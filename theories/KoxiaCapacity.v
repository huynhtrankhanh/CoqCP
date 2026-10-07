From CoqCP Require Import Options KoxiaRoots KoxiaFourier KoxiaSizes KoxiaArena KoxiaLeafRun KoxiaPolynomial KoxiaTraversal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Lemma stageSize_monotone first last : (first<=last)%nat -> stageSize first<=stageSize last.
Proof. intro bound. unfold stageSize. apply Z.pow_le_mono_r; lia. Qed.
Lemma ceilingStage_cap fuel target start cap : (start<=cap)%nat -> (cap-start<=fuel)%nat -> target<=stageSize cap ->
  (ceilingStage fuel target start<=cap)%nat.
Proof.
  induction fuel as [|fuel IH] in start |- *.
  - intros order enough targetBound. cbn [ceilingStage]. exact order.
  - intros order enough targetBound. cbn [ceilingStage]. destruct (bool_decide (stageSize start<target)) eqn:small; [|exact order].
    apply bool_decide_eq_true in small.
    assert (strict : (start<cap)%nat).
    { destruct (Nat.eq_dec start cap) as [->|different]; [lia|lia]. }
    apply IH; try assumption; lia.
Qed.
Lemma ceilingStage_global n target : 1<=target -> target<=2*Z.of_nat n+1 -> Z.of_nat n<=500000 ->
  (sizeNat (ceilingStage 20 target 0)<=sizeNat (ceilingStage 20 (2*Z.of_nat n+1) 0))%nat.
Proof.
  intros positive targetBound inputBound.
  destruct (ceilingStage_correct (2*Z.of_nat n+1) ltac:(lia)) as [globalStage globalSizes].
  pose proof (ceilingStage_cap 20 target 0 (ceilingStage 20 (2*Z.of_nat n+1) 0) ltac:(lia) ltac:(lia) ltac:(lia)) as order.
  apply Nat2Z.inj_le. rewrite <-!stageSize_nat. apply stageSize_monotone. exact order.
Qed.
Lemma node_output_poly_room n len events : (len+length events<=S n)%nat ->
  (len+ordinaryCount events<=2*n+64)%nat.
Proof. intro room. pose proof (ordinaryCount_bound events) as countBound. lia. Qed.
Lemma node_convolution_capacity n len events : (len+length events<=S n)%nat ->
  (specialCount events<len)%nat -> Z.of_nat n<=500000 ->
  1<=Z.of_nat (len-specialCount events+length events)<=1048576 /\
  (sizeNat (ceilingStage 20 (Z.of_nat (len-specialCount events+length events)) 0)<=
    sizeNat (ceilingStage 20 (2*Z.of_nat n+1) 0))%nat.
Proof.
  intros room highPresent inputBound. split; [lia|]. apply ceilingStage_global; lia.
Qed.
Lemma tree_left_poly_room len leftEvents rightEvents limit :
  (len+length (leftEvents++rightEvents)<=limit)%nat ->
  (Nat.min len (specialCount (leftEvents++rightEvents))+length leftEvents<=limit)%nat.
Proof. rewrite length_app. lia. Qed.
Lemma tree_right_poly_room len leftEvents rightEvents limit :
  (len+length (leftEvents++rightEvents)<=limit)%nat ->
  (Nat.min len (specialCount (leftEvents++rightEvents))+ordinaryCount leftEvents+length rightEvents<=limit)%nat.
Proof. rewrite length_app. pose proof (ordinaryCount_bound leftEvents). lia. Qed.
Lemma interval_middle start span : ((start+start+span)/2=start+span/2)%nat.
Proof.
  pose proof (Nat.div_mod span 2 ltac:(lia)) as division.
  pose proof (Nat.mod_upper_bound span 2 ltac:(lia)) as remainder.
  symmetry. apply Nat.div_unique with (r:=(span mod 2)%nat); lia.
Qed.
