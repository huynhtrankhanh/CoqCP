From CoqCP Require Import Options.
From Submission Require Import KoxiaPolynomial KoxiaFourier KoxiaLeafRun KoxiaBufferSplit.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Fixpoint balancedTree fuel (events : list bool) : EventTree :=
  if Nat.leb (length events) 32 then Leaf events else
    match fuel with
    | O => Leaf events
    | S fuel => Branch (balancedTree fuel (firstn (length events/2) events))
      (balancedTree fuel (skipn (length events/2) events))
    end.
Fixpoint treeHeight tree := match tree with Leaf _ => 0%nat | Branch leftTree rightTree => S (Nat.max (treeHeight leftTree) (treeHeight rightTree)) end.
Fixpoint treeVisits tree := match tree with Leaf _ => 1%nat | Branch leftTree rightTree => (3+treeVisits leftTree+treeVisits rightTree)%nat end.
Fixpoint leavesSmall tree := match tree with Leaf events => (length events<=32)%nat | Branch leftTree rightTree => leavesSmall leftTree /\ leavesSmall rightTree end.
Lemma balancedTree_events fuel events : treeEvents (balancedTree fuel events)=events.
Proof.
  induction fuel as [|fuel IH] in events |- *; cbn [balancedTree]; destruct (Nat.leb (length events) 32); try reflexivity.
  cbn [treeEvents]. rewrite !IH. apply firstn_skipn.
Qed.
Lemma balancedTree_height fuel events : (treeHeight (balancedTree fuel events)<=fuel)%nat.
Proof.
  induction fuel as [|fuel IH] in events |- *; cbn [balancedTree]; destruct (Nat.leb (length events) 32); cbn [treeHeight]; try lia.
  pose proof (IH (firstn (length events/2) events)). pose proof (IH (skipn (length events/2) events)). lia.
Qed.
Lemma half_list_lengths (events : list bool) :
  (length (firstn (length events/2) events)+length (skipn (length events/2) events)=length events)%nat /\
  ((32<length events)%nat -> (0<length (firstn (length events/2) events))%nat /\ (0<length (skipn (length events/2) events))%nat).
Proof.
  assert (halfBound : (length events/2<=length events)%nat) by (apply Nat.div_le_upper_bound; lia).
  rewrite firstn_length,skipn_length,Nat.min_l by exact halfBound.
  pose proof (Nat.div_mod (length events) 2 ltac:(lia)) as division.
  pose proof (Nat.mod_upper_bound (length events) 2 ltac:(lia)) as remainder. split; [lia|intros; lia].
Qed.
Lemma balancedTree_small fuel events : (length events<=32*sizeNat fuel)%nat -> leavesSmall (balancedTree fuel events).
Proof.
  induction fuel as [|fuel IH] in events |- *.
  - intro room. change (length events<=32)%nat in room. cbn [balancedTree]. rewrite (proj2 (Nat.leb_le _ _) room). exact room.
  - intro room. cbn [balancedTree]. destruct (Nat.leb (length events) 32) eqn:small.
    + cbn [leavesSmall]. apply Nat.leb_le. exact small.
    + cbn [leavesSmall]. rewrite sizeNat_succ in room.
      assert (halfBound : (length events/2<=length events)%nat) by (apply Nat.div_le_upper_bound; lia).
      pose proof (Nat.div_mod (length events) 2 ltac:(lia)) as division.
      pose proof (Nat.mod_upper_bound (length events) 2 ltac:(lia)) as remainder.
      split; apply IH; rewrite ?firstn_length,?skipn_length,?Nat.min_l by exact halfBound; nia.
Qed.
Lemma balancedTree_visits_positive fuel events : (0<length events)%nat ->
  (treeVisits (balancedTree fuel events)<=4*length events-3)%nat.
Proof.
  induction fuel as [|fuel IH] in events |- *.
  - intro positive. cbn [balancedTree]. destruct (Nat.leb (length events) 32); cbn [treeVisits]; lia.
  - intro positive. cbn [balancedTree]. destruct (Nat.leb (length events) 32) eqn:small.
    + cbn [treeVisits]; lia.
    + apply Nat.leb_gt in small. destruct (half_list_lengths events) as [sum sizes].
      destruct (sizes small) as [leftPositive rightPositive]. cbn [treeVisits].
      pose proof (IH (firstn (length events/2) events) leftPositive) as leftBound.
      pose proof (IH (skipn (length events/2) events) rightPositive) as rightBound. lia.
Qed.
Theorem balancedTree_visits fuel events : (treeVisits (balancedTree fuel events)<=4*length events+1)%nat.
Proof.
  destruct events as [|event events].
  - destruct fuel; reflexivity.
  - pose proof (balancedTree_visits_positive fuel (event::events) ltac:(cbn [length]; lia)). lia.
Qed.
