From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash SchemaGraph SchemaMetadata SchemaRepresentation SchemaMarking SchemaMarkingNative
  SchemaMarkingClosure SchemaMarkingSchedule SchemaMarkingControl ObservedLocal RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaMarkingRun.
Import IndexExecution SipHashExecution ObservedLocal.
Definition natural (s:Machine) root := forall node, (node<SchemaGraph.width root)%nat ->
  exists k a b c d x y, SchemaMetadata.node_at s node=(Z.of_nat k,Z.of_nat a,Z.of_nat b,Z.of_nat c,Z.of_nat d,x,y).
Lemma represented_natural s logical root : SchemaRepresentation.represents s logical ->
  (root<length (memory s arraydef_0__schemaNodes))%nat -> natural s root.
Proof.
  intros Hrep Hroot node Hnode.
  pose proof (SchemaMetadata.represents_length s _ (SchemaRepresentation.metadata _ _ Hrep)) as Hlength.
  assert (Hbound:(node<length (Protocol.expressions logical))%nat) by (unfold SchemaGraph.width in Hnode;lia).
  destruct (nth_error (Protocol.expressions logical) node) as [expression|] eqn:Hexpression;
    [|apply nth_error_None in Hexpression;lia].
  destruct (SchemaRepresentation.lookup s logical node expression Hrep Hexpression) as (raw & Hraw & Hentry).
  destruct Hentry as (k & a & b & c & d & Hencode & Hfit & Hmeaning).
  exists k,a,b,c,d,(SchemaMetadata.kind expression),(Z.of_nat (SchemaMetadata.arity expression)).
  unfold SchemaMetadata.node_at. rewrite (List.nth_error_nth _ _ _ Hraw). exact Hencode.
Qed.
Definition same_arrays (source after:Machine) := forall name, name<>arraydef_0__schemaMarks -> memory after name=memory source name.
Definition good root source (f:SchemaMarking.Frame) marked :=
  SchemaMarkingNative.represents root (machine f) marked /\ same_arrays source (machine f) /\
  (SchemaMarking.size root<=length (memory (machine f) arraydef_0__schemaMarks))%nat /\
  forall node depth, In (node,depth) marked -> SchemaGraph.reachable source root node depth.
Lemma same_node source after : same_arrays source after -> SchemaMetadata.node_at after=SchemaMetadata.node_at source.
Proof. intro Hsame. unfold SchemaMetadata.node_at. now rewrite Hsame by discriminate. Qed.
Lemma step_sound source root marked node depth : SchemaGraph.ordered source ->
  (root<length (memory source arraydef_0__schemaNodes))%nat ->
  (forall n d, In (n,d) marked -> SchemaGraph.reachable source root n d) ->
  forall n d, In (n,d) (SchemaMarkingClosure.step (SchemaMarkingSchedule.dependencies source root) (node,depth) marked) ->
  SchemaGraph.reachable source root n d.
Proof.
  intros Hordered Hroot Hsound n d. rewrite SchemaMarkingClosure.step_in. intros [Hin|[Hparent Hchild]];[now apply Hsound|].
  apply (SchemaMarkingSchedule.graph_to_reachable source root (n,d)).
  eapply SchemaMarkingClosure.reachable_child;[|exact Hchild].
  apply SchemaMarkingSchedule.reachable_to_graph;[exact Hordered|exact Hroot|now apply Hsound].
Qed.
Theorem generated_cell root source (f:SchemaMarking.Frame) marked node depth remaining observations :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat -> natural source root ->
  Z.of_nat (SchemaMarking.size root)<=maximum -> good root source f marked ->
  nums f vardef_0__schemaInstance_node=Z.of_nat node ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
  Z.of_nat (SchemaGraph.width root)-Z.of_nat remaining-1=Z.of_nat depth ->
  exists after,
    execLocalObserved (SchemaMarking.mark_depth_body (Z.of_nat (SchemaGraph.width root)) remaining) (f,observations)=Some (KeepGoing,(after,observations)) /\
    good root source after (SchemaMarkingClosure.step (SchemaMarkingSchedule.dependencies source root) (node,depth) marked) /\
    nums after vardef_0__schemaInstance_root=nums f vardef_0__schemaInstance_root /\
    nums after vardef_0__schemaInstance_width=nums f vardef_0__schemaInstance_width /\
    nums after vardef_0__schemaInstance_node=nums f vardef_0__schemaInstance_node.
Proof.
  intros Hordered Hroot Hnatural Hroom [Hrep [Hsame [Hcapacity Hsound]]] Hnode Hwidth Hnb Hdb Hdepth.
  destruct (Z.eq_dec (SchemaMarking.cell (machine f) (SchemaGraph.key root node depth)) 0) as [Hzero|Hnonzero].
  - assert (Hnot:~In (node,depth) marked) by (intro Hin;apply (proj2 (Hrep node depth Hnb Hdb)) in Hin;contradiction).
    assert (Hstep:SchemaMarkingClosure.step (SchemaMarkingSchedule.dependencies source root) (node,depth) marked=marked).
    { unfold SchemaMarkingClosure.step. destruct (List.in_dec (fun x y=>decide (x=y)) (node,depth) marked);[contradiction|reflexivity]. }
    exists (setNum f vardef_0__schemaInstance_key (Z.of_nat (SchemaGraph.key root node depth))). split.
    + now apply SchemaMarking.generated_unmarked_cell.
    + rewrite Hstep. split;[unfold good;cbn [machine setNum];auto|]. cbn [nums setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. auto.
  - assert (Hreachable:SchemaGraph.reachable source root node depth) by (apply Hsound;apply (proj1 (Hrep node depth Hnb Hdb));exact Hnonzero).
    destruct (Hnatural node Hnb) as (k & a & b & c & d & x & y & Hraw).
    assert (HrawNative:SchemaMetadata.node_at (machine f) node=(Z.of_nat k,Z.of_nat a,Z.of_nat b,Z.of_nat c,Z.of_nat d,x,y)) by (rewrite (same_node source (machine f) Hsame);exact Hraw).
    assert (Hchildren:SchemaGraph.children (SchemaMetadata.node_at source node)=SchemaGraph.children_fields k a b c d).
    { rewrite Hraw. unfold SchemaGraph.children. now rewrite !Nat2Z.id. }
    assert (Hbounds:forall child extra, In (child,extra) (SchemaGraph.children_fields k a b c d) ->
      (child<SchemaGraph.width root /\ depth+extra<SchemaGraph.width root)%nat).
    { intros child extra Hin. rewrite <-Hchildren in Hin. destruct (SchemaGraph.reachable_grid _ _ _ _ Hordered Hroot
        (SchemaGraph.child_reachable _ _ _ _ _ _ Hreachable Hin)) as [Hc [Hd _]]. auto. }
    assert (Hdeps:SchemaMarkingSchedule.dependencies source root (node,depth)=
      map (fun pair=>(fst pair,(depth+snd pair)%nat)) (SchemaGraph.children_fields k a b c d)).
    { unfold SchemaMarkingSchedule.dependencies. destruct (le_dec (node+depth) root) as [Hsafe|Hunsafe];[now rewrite Hchildren|].
      destruct (SchemaGraph.reachable_bound _ _ _ _ Hordered Hroot Hreachable) as [_ Hsafe]. lia. }
    assert (Hstep:SchemaMarkingClosure.step (SchemaMarkingSchedule.dependencies source root) (node,depth) marked=
      map (fun pair=>(fst pair,(depth+snd pair)%nat)) (SchemaGraph.children_fields k a b c d)++marked).
    { unfold SchemaMarkingClosure.step. destruct (List.in_dec (fun x y=>decide (x=y)) (node,depth) marked) as [Hin|Hnot];[now rewrite Hdeps|].
      exfalso. apply Hnot,(proj1 (Hrep node depth Hnb Hdb)),Hnonzero. }
    set (after:=setMachine (SchemaMarking.loaded (setNum f vardef_0__schemaInstance_key (Z.of_nat (SchemaGraph.key root node depth))) k a b c d)
      (SchemaMarking.mark_children (machine f) root depth (SchemaGraph.children_fields k a b c d))).
    exists after. split.
    + apply (SchemaMarking.generated_marked_cell f root node depth remaining k a b c d x y observations);try assumption.
      * rewrite Hsame by discriminate. unfold SchemaGraph.width in Hnb. lia.
      * intros child extra Hin. destruct (Hbounds child extra Hin) as [Hc Hd]. now apply SchemaGraph.grid_bound.
    + split.
      * split.
        -- rewrite Hstep. unfold after. cbn [machine setMachine]. now apply SchemaMarkingNative.children_represents.
        -- split.
           ++ intros name Hname. unfold after. cbn [machine setMachine]. rewrite SchemaMarkingNative.children_other by exact Hname. now apply Hsame.
           ++ split.
              ** unfold after. cbn [machine setMachine]. now rewrite SchemaMarkingNative.children_length.
              ** now apply step_sound.
      * unfold after,SchemaMarking.loaded. cbn [nums setNum setMachine]. repeat rewrite RenameMemoControl.updated_other by discriminate. auto.
Qed.
Lemma sweep_append {A} `{EqDecision A} (children:A->list A) left right marked :
  SchemaMarkingClosure.sweep children (left++right) marked=
    SchemaMarkingClosure.sweep children right (SchemaMarkingClosure.sweep children left marked).
Proof. induction left as [|head rest IH] in marked|-*;cbn;[reflexivity|apply IH]. Qed.
Theorem generated_depths root source :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat -> natural source root ->
  Z.of_nat (SchemaMarking.size root)<=maximum -> forall count (f:SchemaMarking.Frame) marked node observations,
  (count<=SchemaGraph.width root)%nat -> good root source f marked ->
  nums f vardef_0__schemaInstance_node=Z.of_nat node ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  (node<SchemaGraph.width root)%nat ->
  exists after,
    execLocalObserved (loop count (SchemaMarking.mark_depth_body (Z.of_nat (SchemaGraph.width root)))) (f,observations)=Some (tt,(after,observations)) /\
    good root source after (SchemaMarkingClosure.sweep (SchemaMarkingSchedule.dependencies source root)
      (map (fun depth=>(node,depth)) (seq (SchemaGraph.width root-count) count)) marked) /\
    nums after vardef_0__schemaInstance_root=nums f vardef_0__schemaInstance_root /\
    nums after vardef_0__schemaInstance_width=nums f vardef_0__schemaInstance_width /\
    nums after vardef_0__schemaInstance_node=nums f vardef_0__schemaInstance_node.
Proof.
  intros Hordered Hroot Hnatural Hroom count. induction count as [|count IH];intros f marked node observations Hcount Hgood Hnode Hwidth Hnb.
  - exists f. split;[reflexivity|]. split;[exact Hgood|]. auto.
  - destruct (generated_cell root source f marked node (SchemaGraph.width root-S count) count observations
      Hordered Hroot Hnatural Hroom Hgood Hnode Hwidth Hnb ltac:(lia) ltac:(lia))
      as (middle & Hfirst & Hmiddle & Hmr & Hmw & Hmn).
    destruct (IH middle _ node observations ltac:(lia) Hmiddle ltac:(now rewrite Hmn) ltac:(now rewrite Hmw) Hnb)
      as (after & Hrest & Hafter & Har & Haw & Han).
    exists after. split.
    + rewrite loop_S,local_bind,Hfirst. cbn [optionBind fst snd]. exact Hrest.
    + split.
      * cbn [seq map SchemaMarkingClosure.sweep].
        replace (S (SchemaGraph.width root-S count)) with (SchemaGraph.width root-count)%nat by lia. exact Hafter.
      * repeat split;congruence.
Qed.
Theorem generated_rows root source :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat -> natural source root ->
  Z.of_nat (SchemaMarking.size root)<=maximum -> forall count (f:SchemaMarking.Frame) marked observations,
  (count<=SchemaGraph.width root)%nat -> good root source f marked ->
  nums f vardef_0__schemaInstance_root=Z.of_nat root ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  exists after,
    execLocalObserved (loop count (SchemaMarking.mark_outer_body (Z.of_nat (SchemaGraph.width root)))) (f,observations)=Some (tt,(after,observations)) /\
    good root source after (SchemaMarkingClosure.sweep (SchemaMarkingSchedule.dependencies source root)
      (SchemaMarkingSchedule.grid (SchemaGraph.width root) count) marked) /\
    nums after vardef_0__schemaInstance_root=nums f vardef_0__schemaInstance_root /\
    nums after vardef_0__schemaInstance_width=nums f vardef_0__schemaInstance_width.
Proof.
  intros Hordered Hroot Hnatural Hroom count. induction count as [|count IH];intros f marked observations Hcount Hgood Hrootnum Hwidth.
  - exists f. split;[reflexivity|]. split;[exact Hgood|]. auto.
  - set (rowframe:=setNum f vardef_0__schemaInstance_node (Z.of_nat count)).
    assert (Hrowgood:good root source rowframe marked) by exact Hgood.
    assert (Hrownode:nums rowframe vardef_0__schemaInstance_node=Z.of_nat count).
    { unfold rowframe. cbn [nums setNum]. apply RenameMemoControl.updated_same. }
    assert (Hrowwidth:nums rowframe vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root)).
    { unfold rowframe. cbn [nums setNum]. rewrite RenameMemoControl.updated_other by discriminate. exact Hwidth. }
    destruct (generated_depths root source Hordered Hroot Hnatural Hroom (SchemaGraph.width root) rowframe marked count observations
      ltac:(lia) Hrowgood Hrownode Hrowwidth ltac:(lia)) as (middle & Hdepths & Hmiddle & Hmr & Hmw & Hmn).
    replace (SchemaGraph.width root-SchemaGraph.width root)%nat with 0%nat in Hmiddle by lia.
    assert (HmiddleRoot:nums middle vardef_0__schemaInstance_root=Z.of_nat root).
    { rewrite Hmr. unfold rowframe. cbn [nums setNum]. rewrite RenameMemoControl.updated_other by discriminate. exact Hrootnum. }
    assert (HmiddleWidth:nums middle vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root)) by (now rewrite Hmw).
    destruct (IH middle _ observations ltac:(lia) Hmiddle HmiddleRoot HmiddleWidth) as (after & Hrest & Hafter & Har & Haw).
    exists after. split.
    + rewrite loop_S,local_bind,(SchemaMarkingControl.generated_row f root count observations Hrootnum Hwidth ltac:(lia)).
      * fold rowframe. unfold SchemaMarking.Frame in Hdepths. rewrite Hdepths. cbn [optionBind fst snd]. exact Hrest.
      * destruct (SchemaGraph.grid_words root 0 0 ltac:(unfold SchemaGraph.width;lia) ltac:(unfold SchemaGraph.width;lia) Hroom) as [[_ Hword] _]. exact Hword.
    + split.
      * change (good root source after (SchemaMarkingClosure.sweep (SchemaMarkingSchedule.dependencies source root)
          (SchemaMarkingSchedule.row (SchemaGraph.width root) count++SchemaMarkingSchedule.grid (SchemaGraph.width root) count) marked)).
        rewrite sweep_append. exact Hafter.
      * split.
        -- rewrite Har,Hmr. unfold rowframe. cbn [nums setNum]. now rewrite RenameMemoControl.updated_other by discriminate.
        -- rewrite Haw,Hmw. unfold rowframe. cbn [nums setNum]. now rewrite RenameMemoControl.updated_other by discriminate.
Qed.
Theorem generated_marking root source (f:SchemaMarking.Frame) observations :
  SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat -> natural source root ->
  Z.of_nat (SchemaMarking.size root)<=maximum -> good root source f [(root,0%nat)] ->
  nums f vardef_0__schemaInstance_root=Z.of_nat root ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  exists after,
    execLocalObserved SchemaMarking.marked_pass (f,observations)=Some (tt,(after,observations)) /\
    (forall node depth, (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
      (SchemaMarking.cell (machine after) (SchemaGraph.key root node depth)<>0 <-> SchemaGraph.reachable source root node depth)) /\
    same_arrays source (machine after) /\
    (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaMarks))%nat /\
    nums after vardef_0__schemaInstance_root=Z.of_nat root /\
    nums after vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root).
Proof.
  intros Hordered Hroot Hnatural Hroom Hgood Hrootnum Hwidth.
  destruct (generated_rows root source Hordered Hroot Hnatural Hroom (SchemaGraph.width root) f [(root,0%nat)] observations
    ltac:(lia) Hgood Hrootnum Hwidth) as (after & Hrun & [Hrep [Hsame [Hcapacity Hsound]]] & Hr & Hw).
  exists after. split;[now rewrite (SchemaMarkingControl.generated_marked_pass f root observations Hwidth)|].
  split;[|repeat split;try assumption;congruence]. intros node depth Hn Hd. rewrite (Hrep node depth Hn Hd). now apply SchemaMarkingSchedule.scheduled_marks_exact.
Qed.
Lemma node_transport left right : SchemaMetadata.node_at left=SchemaMetadata.node_at right ->
  forall root node depth, SchemaGraph.reachable left root node depth <-> SchemaGraph.reachable right root node depth.
Proof.
  intro Hsame. assert (Hforward:forall a b, SchemaMetadata.node_at a=SchemaMetadata.node_at b ->
    forall root node depth, SchemaGraph.reachable a root node depth -> SchemaGraph.reachable b root node depth).
  { intros a b Hnodes root node depth Hreach. induction Hreach as [|node depth child extra Hreach IH Hin];[constructor|].
    eapply SchemaGraph.child_reachable;[exact IH|now rewrite <-Hnodes]. }
  intros root node depth. split;apply Hforward;congruence.
Qed.
Lemma grown_nodes s root : SchemaMetadata.node_at (SchemaMarking.grown s root)=SchemaMetadata.node_at s.
Proof. unfold SchemaMetadata.node_at. now rewrite SchemaMarking.grown_other by discriminate. Qed.
Lemma grown_ordered s root : SchemaGraph.ordered s -> SchemaGraph.ordered (SchemaMarking.grown s root).
Proof.
  intros Hordered node child extra Hbound Hin. rewrite grown_nodes in Hin.
  rewrite SchemaMarking.grown_other in Hbound by discriminate. now apply Hordered.
Qed.
Lemma prepared_good (f:SchemaMarking.Frame) root :
  good root (SchemaMarking.grown (machine f) root) (SchemaMarking.prepared_frame f root) [(root,0%nat)].
Proof.
  unfold good,SchemaMarking.prepared_frame. cbn [machine setMachine]. split.
  - apply SchemaMarkingNative.initialized_represents.
  - split.
    + intros name Hname. unfold SchemaMarking.initialized.
      rewrite SchemaGraph.marked_other,SchemaMarking.clear_other by exact Hname. reflexivity.
    + split;[apply SchemaMarking.initialized_capacity|]. intros node depth [Heq|Hnone];[|contradiction].
      inversion Heq;subst. constructor.
Qed.
Theorem generated_initial_marking root (f:SchemaMarking.Frame) observations :
  SchemaGraph.ordered (machine f) ->
  (root<length (memory (machine f) arraydef_0__schemaNodes))%nat -> natural (machine f) root ->
  Z.of_nat (SchemaMarking.size root)<=maximum ->
  nums f vardef_0__schemaInstance_root=Z.of_nat root ->
  exists after,
    execLocalObserved (SchemaMarking.initial_with SchemaMarking.marked_pass) (f,observations)=Some (tt,(after,observations)) /\
    execLocalObserved funcdef_0__schemaInstance_body (f,observations)=
      execLocalObserved SchemaMarking.evaluation (after,observations) /\
    (forall node depth, (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
      (SchemaMarking.cell (machine after) (SchemaGraph.key root node depth)<>0 <-> SchemaGraph.reachable (machine f) root node depth)) /\
    same_arrays (SchemaMarking.grown (machine f) root) (machine after) /\
    (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaMarks))%nat /\
    (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaValues))%nat /\
    nums after vardef_0__schemaInstance_root=Z.of_nat root /\
    nums after vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root).
Proof.
  intros Hordered Hroot Hnatural Hroom Hrootnum.
  assert (HgrownRoot:(root<length (memory (SchemaMarking.grown (machine f) root) arraydef_0__schemaNodes))%nat).
  { now rewrite SchemaMarking.grown_other by discriminate. }
  assert (HgrownNatural:natural (SchemaMarking.grown (machine f) root) root).
  { unfold natural in *. now rewrite grown_nodes. }
  assert (HpreparedRoot:nums (SchemaMarking.prepared_frame f root) vardef_0__schemaInstance_root=Z.of_nat root).
  { unfold SchemaMarking.prepared_frame. cbn [nums setMachine setNum]. repeat rewrite RenameMemoControl.updated_other by discriminate. exact Hrootnum. }
  assert (HpreparedWidth:nums (SchemaMarking.prepared_frame f root) vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root)).
  { unfold SchemaMarking.prepared_frame. cbn [nums setMachine setNum]. rewrite RenameMemoControl.updated_other by discriminate. apply RenameMemoControl.updated_same. }
  destruct (generated_marking root (SchemaMarking.grown (machine f) root) (SchemaMarking.prepared_frame f root) observations
    (grown_ordered _ _ Hordered) HgrownRoot HgrownNatural Hroom (prepared_good f root) HpreparedRoot HpreparedWidth)
    as (after & Hrun & Hexact & Hsame & Hmarks & Hr & Hw).
  exists after. split.
  - rewrite (SchemaMarking.generated_initial SchemaMarking.marked_pass f root observations Hrootnum Hroom). exact Hrun.
  - split.
    + rewrite SchemaMarking.actual_initial,(SchemaMarking.generated_initial SchemaMarking.remaining f root observations Hrootnum Hroom).
      unfold SchemaMarking.Frame in Hrun. rewrite SchemaMarking.remaining_parts,local_bind,Hrun. reflexivity.
    + split.
      * intros node depth Hn Hd. rewrite Hexact by assumption. apply node_transport,grown_nodes.
      * split;[exact Hsame|]. split;[exact Hmarks|]. split.
        -- rewrite Hsame by discriminate. apply SchemaMarking.grown_values.
        -- auto.
Qed.
Theorem generated_represented_initial_marking root (f:SchemaMarking.Frame) logical observations :
  SchemaRepresentation.represents (machine f) logical ->
  (root<length (memory (machine f) arraydef_0__schemaNodes))%nat ->
  Z.of_nat (SchemaMarking.size root)<=maximum ->
  nums f vardef_0__schemaInstance_root=Z.of_nat root ->
  exists after,
    execLocalObserved (SchemaMarking.initial_with SchemaMarking.marked_pass) (f,observations)=Some (tt,(after,observations)) /\
    execLocalObserved funcdef_0__schemaInstance_body (f,observations)=
      execLocalObserved SchemaMarking.evaluation (after,observations) /\
    (forall node depth, (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
      (SchemaMarking.cell (machine after) (SchemaGraph.key root node depth)<>0 <-> SchemaGraph.reachable (machine f) root node depth)) /\
    same_arrays (SchemaMarking.grown (machine f) root) (machine after) /\
    (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaMarks))%nat /\
    (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaValues))%nat /\
    nums after vardef_0__schemaInstance_root=Z.of_nat root /\
    nums after vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root).
Proof.
  intros Hrep Hroot Hroom Hrootnum. apply generated_initial_marking;try assumption.
  - now apply SchemaGraph.represented_ordered with (logical:=logical).
  - now apply represented_natural with (logical:=logical).
Qed.
End SchemaMarkingRun.
