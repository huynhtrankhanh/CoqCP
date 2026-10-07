From CoqCP Require Import Options.
From Submission Require Import KoxiaPolynomial KoxiaFourier KoxiaLeafRun KoxiaTraversal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Definition specialCount events := (length events-ordinaryCount events)%nat.
Lemma specialCount_bound events : (specialCount events<=length events)%nat.
Proof. unfold specialCount. lia. Qed.
Lemma event_counts events : (specialCount events+ordinaryCount events=length events)%nat.
Proof. unfold specialCount. pose proof (ordinaryCount_bound events). lia. Qed.
Lemma ordinaryCount_app leftEvents rightEvents :
  ordinaryCount (leftEvents++rightEvents)=(ordinaryCount leftEvents+ordinaryCount rightEvents)%nat.
Proof.
  induction leftEvents as [|event events IH]; [reflexivity|]. destruct event; cbn [ordinaryCount app]; rewrite IH; lia.
Qed.
Lemma specialCount_app leftEvents rightEvents :
  specialCount (leftEvents++rightEvents)=(specialCount leftEvents+specialCount rightEvents)%nat.
Proof. unfold specialCount. rewrite length_app,ordinaryCount_app. pose proof (ordinaryCount_bound leftEvents). pose proof (ordinaryCount_bound rightEvents). lia. Qed.
Lemma specialCount_agrees events : specials events=Z.of_nat (specialCount events).
Proof.
  induction events as [|event events IH]; [reflexivity|].
  pose proof (ordinaryCount_bound events) as bound. cbn [specials]. rewrite IH.
  unfold specialCount. cbn [length ordinaryCount flag]. destruct event; cbn; lia.
Qed.
Definition savedLength len cut span := if Nat.ltb cut len then (len-cut+span)%nat else 0%nat.
Definition arenaNeed :=
  fix arenaNeed tree len := match tree with
  | Leaf _ => 0%nat
  | Branch leftTree rightTree =>
    let events := treeEvents leftTree++treeEvents rightTree in
    let cut := specialCount events in
    let small := Nat.min len cut in
    (savedLength len cut (length events)+Nat.max (arenaNeed leftTree small)
      (arenaNeed rightTree (small+ordinaryCount (treeEvents leftTree))))%nat
  end.
Lemma savedLength_root events : (savedLength 1 (specialCount events) (length events)<=S (length events))%nat.
Proof. unfold savedLength. destruct (Nat.ltb (specialCount events) 1) eqn:present; [apply Nat.ltb_lt in present; assert (zero : specialCount events=0%nat) by lia; rewrite zero; lia|lia]. Qed.
Lemma savedLength_child_left len leftEvents rightEvents :
  (savedLength (Nat.min len (specialCount (leftEvents++rightEvents))) (specialCount leftEvents) (length leftEvents)
    <=length (leftEvents++rightEvents))%nat.
Proof.
  unfold savedLength. rewrite specialCount_app,length_app. destruct (Nat.ltb (specialCount leftEvents) (Nat.min len (specialCount leftEvents+specialCount rightEvents))) eqn:present; [|lia].
  apply Nat.ltb_lt in present. pose proof (specialCount_bound rightEvents). lia.
Qed.
Lemma savedLength_child_right len leftEvents rightEvents :
  (savedLength (Nat.min len (specialCount (leftEvents++rightEvents))+ordinaryCount leftEvents) (specialCount rightEvents) (length rightEvents)
    <=length (leftEvents++rightEvents))%nat.
Proof.
  unfold savedLength. rewrite specialCount_app,length_app. destruct (Nat.ltb (specialCount rightEvents) (Nat.min len (specialCount leftEvents+specialCount rightEvents)+ordinaryCount leftEvents)) eqn:present; [|lia].
  apply Nat.ltb_lt in present. pose proof (event_counts leftEvents). lia.
Qed.
Theorem arenaNeed_bound fuel events len :
  (arenaNeed (balancedTree fuel events) len<=savedLength len (specialCount events) (length events)+2*length events+fuel)%nat.
Proof.
  induction fuel as [|fuel IH] in events,len |- *.
  - cbn [balancedTree]. destruct (Nat.leb (length events) 32); cbn [arenaNeed]; lia.
  - cbn [balancedTree]. destruct (Nat.leb (length events) 32) eqn:small; [cbn [arenaNeed]; lia|].
    cbn [arenaNeed]. rewrite !balancedTree_events.
    set (leftEvents := firstn (length events/2) events).
    set (rightEvents := skipn (length events/2) events).
    assert (concatenated : leftEvents++rightEvents=events) by (unfold leftEvents,rightEvents; apply firstn_skipn).
    pose proof (IH leftEvents (Nat.min len (specialCount (leftEvents++rightEvents)))) as leftBound.
    pose proof (IH rightEvents (Nat.min len (specialCount (leftEvents++rightEvents))+ordinaryCount leftEvents)%nat) as rightBound.
    pose proof (savedLength_child_left len leftEvents rightEvents) as leftSaved.
    pose proof (savedLength_child_right len leftEvents rightEvents) as rightSaved.
    rewrite concatenated in leftBound,rightBound,leftSaved,rightSaved |- *.
    assert (leftHalf : (2*length leftEvents<=length events)%nat).
    { unfold leftEvents. rewrite length_firstn. pose proof (Nat.div_mod (length events) 2 ltac:(lia)) as division. pose proof (Nat.mod_upper_bound (length events) 2 ltac:(lia)) as remainder.
      assert (halfBound : (length events/2<=length events)%nat) by (apply Nat.div_le_upper_bound; lia). rewrite Nat.min_l by exact halfBound. lia. }
    assert (rightHalf : (2*length rightEvents<=S (length events))%nat).
    { unfold rightEvents. rewrite length_skipn. pose proof (Nat.div_mod (length events) 2 ltac:(lia)) as division. pose proof (Nat.mod_upper_bound (length events) 2 ltac:(lia)) as remainder. lia. }
    lia.
Qed.
Theorem arenaNeed_root events : (arenaNeed (balancedTree 20 events) 1<=3*length events+21)%nat.
Proof. pose proof (arenaNeed_bound 20 events 1) as bound. pose proof (savedLength_root events) as savedBound. lia. Qed.

Theorem balancedTree_root_bounds events n : Z.of_nat (length events)<=Z.of_nat n ->
  Z.of_nat n<=500000 ->
  leavesSmall (balancedTree 20 events) /\
  (treeHeight (balancedTree 20 events)<32)%nat /\
  (treeVisits (balancedTree 20 events)<=4*length events+1)%nat /\
  (arenaNeed (balancedTree 20 events) 1<=4*n+128)%nat.
Proof.
  intros eventsBound nBound. split.
  - apply balancedTree_small. apply Nat2Z.inj_le.
    rewrite Nat2Z.inj_mul,<-stageSize_nat.
    change (Z.of_nat (length events)<=32*1048576). lia.
  - split.
    + pose proof (balancedTree_height 20 events) as height. lia.
    + split; [apply balancedTree_visits|].
      pose proof (arenaNeed_root events) as arenaBound. lia.
Qed.
