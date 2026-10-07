From CoqCP Require Import Options.
From Submission Require Import KoxiaPolynomial KoxiaLeafRun KoxiaBufferSplit KoxiaArena KoxiaTraversal KoxiaCapacity KoxiaTreeBuffers KoxiaVisitSchedule KoxiaVisitMemory KoxiaPrefixFlags.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Lia.

Fixpoint wellSplit tree : Prop :=
  match tree with
  | Leaf events => length events<=32
  | Branch leftTree rightTree =>
      let span := length (treeEvents leftTree++treeEvents rightTree) in
      32<span /\ length (treeEvents leftTree)=span/2 /\ wellSplit leftTree /\ wellSplit rightTree
  end.

Theorem balancedTree_wellSplit fuel events : leavesSmall (balancedTree fuel events) ->
  wellSplit (balancedTree fuel events).
Proof.
  induction fuel as [|fuel IH] in events |- *.
  - cbn [balancedTree]. destruct (Nat.leb (length events) 32); exact (fun hypothesis=>hypothesis).
  - cbn [balancedTree]. destruct (Nat.leb (length events) 32) eqn:small; [exact (fun hypothesis=>hypothesis)|].
    cbn [leavesSmall wellSplit]. intros [leftSmall rightSmall].
    rewrite !balancedTree_events,firstn_skipn. apply Nat.leb_gt in small.
    assert (halfBound : length events/2<=length events) by (apply Nat.div_le_upper_bound; lia).
    repeat split; try assumption.
    + rewrite length_firstn,Nat.min_l by exact halfBound. reflexivity.
    + apply IH. exact leftSmall.
    + apply IH. exact rightSmall.
Qed.

Lemma prefixFlags_app values start leftEvents rightEvents : prefixFlags values start (leftEvents++rightEvents) ->
  prefixFlags values start leftEvents /\ prefixFlags values (start+length leftEvents) rightEvents.
Proof.
  intro flags. split.
  - intros index range. rewrite <-app_nth1 with (l':=rightEvents) by exact range.
    apply flags. rewrite length_app. lia.
  - intros index range. rewrite <-app_nth2_plus with (l:=leftEvents).
    replace (start+length leftEvents+index)%nat with (start+(length leftEvents+index))%nat by lia.
    apply flags. rewrite length_app. lia.
Qed.

Definition frameStructure (prefix : list Z) n depth frame :=
  match frame with
  | VisitTree start tree => wellSplit tree /\ start+length (treeEvents tree)<=n /\
      prefixFlags prefix start (treeEvents tree) /\ depth+treeHeight tree<32
  | VisitRight start middle span tree saved savedLen base =>
      wellSplit tree /\ start+span<=n /\ middle=(start+start+span)/2 /\
      middle+length (treeEvents tree)=start+span /\ prefixFlags prefix middle (treeEvents tree) /\
      S depth+treeHeight tree<32
  | VisitMerge start span saved savedLen base => start+span<=n /\ depth<32
  end.

Fixpoint stackStructure prefix n stack : Prop :=
  match stack with
  | []=>True
  | frame::stack=>frameStructure prefix n (length stack) frame /\ stackStructure prefix n stack
  end.

Fixpoint stackPolyRoom limit stack len : Prop :=
  match stack with
  | []=>len<=limit
  | VisitTree _ tree::stack =>
      len+length (treeEvents tree)<=limit /\ stackPolyRoom limit stack (len+ordinaryCount (treeEvents tree))
  | VisitRight _ _ _ tree _ savedLen _::stack =>
      len+length (treeEvents tree)<=limit /\
      stackPolyRoom limit stack (Nat.max (len+ordinaryCount (treeEvents tree)) savedLen)
  | VisitMerge _ _ _ savedLen _::stack =>
      Nat.max len savedLen<=limit /\ stackPolyRoom limit stack (Nat.max len savedLen)
  end.

Fixpoint stackArenaRoom limit stack len top : Prop :=
  top<=limit /\
  match stack with
  | []=>True
  | VisitTree _ tree::stack=>top+arenaNeed tree len<=limit /\
      stackArenaRoom limit stack (len+ordinaryCount (treeEvents tree)) top
  | VisitRight _ _ _ tree _ savedLen base::stack=>top+arenaNeed tree len<=limit /\
      stackArenaRoom limit stack (Nat.max (len+ordinaryCount (treeEvents tree)) savedLen) base
  | VisitMerge _ _ _ savedLen base::stack=>stackArenaRoom limit stack (Nat.max len savedLen) base
  end.

Lemma stackPolyRoom_current limit stack len : stackPolyRoom limit stack len -> len<=limit.
Proof.
  destruct stack as [|frame stack]; [exact (fun hypothesis=>hypothesis)|].
  destruct frame; cbn [stackPolyRoom]; intros [room rest]; lia.
Qed.

Fixpoint stackArenaLayout arena stack top : Prop :=
  match stack with
  | []=>True
  | VisitTree _ _::stack=>stackArenaLayout arena stack top
  | VisitRight _ _ _ _ saved savedLen base::stack | VisitMerge _ _ saved savedLen base::stack =>
      top=base+savedLen /\ savedLen=length saved /\ arenaContains arena base saved /\
      stackArenaLayout arena stack base
  end.

Lemma stackArenaLayout_transfer before after stack top : stackArenaLayout before stack top ->
  (forall index, index<top -> nth index after 0%Z=nth index before 0%Z) -> stackArenaLayout after stack top.
Proof.
  induction stack as [|frame stack IH] in top |- *; [intros; exact I|].
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
  - cbn [stackArenaLayout]. apply IH.
  - cbn [stackArenaLayout]. intros [topEq [lengthEq [contains layout]]] same.
    repeat split; try assumption.
    + apply arenaContains_transfer with (before:=before) (bound:=top); [exact contains|lia|exact same].
    + apply IH with (top:=base); [exact layout|]. intros index range. apply same. lia.
  - cbn [stackArenaLayout]. intros [topEq [lengthEq [contains layout]]] same.
    repeat split; try assumption.
    + apply arenaContains_transfer with (before:=before) (bound:=top); [exact contains|lia|exact same].
    + apply IH with (top:=base); [exact layout|]. intros index range. apply same. lia.
Qed.

Lemma stackStructure_branch prefix n stack start leftTree rightTree saved savedLen top :
  stackStructure prefix n (VisitTree start (Branch leftTree rightTree)::stack) ->
  stackStructure prefix n
    (VisitTree start leftTree::VisitRight start (start+length (treeEvents leftTree))
      (length (treeEvents leftTree++treeEvents rightTree)) rightTree saved savedLen top::stack).
Proof.
  cbn [stackStructure frameStructure wellSplit treeEvents treeHeight].
  intros [[ [large [half [leftSplit rightSplit]]] [interval [flags height]]] outer].
  destruct (prefixFlags_app _ _ _ _ flags) as [leftFlags rightFlags].
  rewrite length_app in interval,half.
  pose proof (Nat.le_max_l (treeHeight leftTree) (treeHeight rightTree)).
  pose proof (Nat.le_max_r (treeHeight leftTree) (treeHeight rightTree)).
  cbn [length].
  repeat split; try assumption; try (rewrite ?length_app,?interval_middle; lia).
Qed.

Lemma output_length_merge_parts len leftEvents rightEvents :
  Nat.max (Nat.min len (specialCount (leftEvents++rightEvents))+ordinaryCount leftEvents+ordinaryCount rightEvents)
    (savedLength len (specialCount (leftEvents++rightEvents)) (length (leftEvents++rightEvents)))=
  len+ordinaryCount (leftEvents++rightEvents).
Proof.
  replace (Nat.min len (specialCount (leftEvents++rightEvents))+ordinaryCount leftEvents+ordinaryCount rightEvents)
    with (Nat.min len (specialCount (leftEvents++rightEvents))+ordinaryCount (leftEvents++rightEvents))
    by (rewrite ordinaryCount_app; lia).
  apply output_length_merge.
Qed.

Lemma stackPolyRoom_branch limit stack start leftTree rightTree values len top :
  stackPolyRoom limit (VisitTree start (Branch leftTree rightTree)::stack) len ->
  stackPolyRoom limit
    (VisitTree start leftTree::VisitRight start (start+length (treeEvents leftTree))
      (length (treeEvents leftTree++treeEvents rightTree)) rightTree
      (savedBuffer values len (specialCount (treeEvents leftTree++treeEvents rightTree))
        (length (treeEvents leftTree++treeEvents rightTree)))
      (savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
        (length (treeEvents leftTree++treeEvents rightTree))) top::stack)
    (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree))).
Proof.
  cbn [stackPolyRoom treeEvents]. intros [room outer].
  rewrite output_length_merge_parts.
  split; [apply tree_left_poly_room; exact room|].
  split; [apply tree_right_poly_room; exact room|exact outer].
Qed.

Lemma stackArenaRoom_branch limit stack start leftTree rightTree values len top :
  stackArenaRoom limit (VisitTree start (Branch leftTree rightTree)::stack) len top ->
  stackArenaRoom limit
    (VisitTree start leftTree::VisitRight start (start+length (treeEvents leftTree))
      (length (treeEvents leftTree++treeEvents rightTree)) rightTree
      (savedBuffer values len (specialCount (treeEvents leftTree++treeEvents rightTree))
        (length (treeEvents leftTree++treeEvents rightTree)))
      (savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
        (length (treeEvents leftTree++treeEvents rightTree))) top::stack)
    (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree)))
    (top+savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
      (length (treeEvents leftTree++treeEvents rightTree))).
Proof.
  cbn [stackArenaRoom treeEvents arenaNeed]. intros [topRoom [room outer]].
  pose proof (Nat.le_max_l
    (arenaNeed leftTree (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree))))
    (arenaNeed rightTree (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree))+
      ordinaryCount (treeEvents leftTree)))) as leftNeed.
  pose proof (Nat.le_max_r
    (arenaNeed leftTree (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree))))
    (arenaNeed rightTree (Nat.min len (specialCount (treeEvents leftTree++treeEvents rightTree))+
      ordinaryCount (treeEvents leftTree)))) as rightNeed.
  rewrite output_length_merge_parts.
  repeat split; try lia; exact outer.
Qed.
