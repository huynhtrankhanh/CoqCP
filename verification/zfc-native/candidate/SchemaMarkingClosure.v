From Stdlib Require Import Lists.List Lia.
From stdpp Require Import base list.
Import ListNotations.
Module SchemaMarkingClosure.
Section Generic.
Context {A:Type} `{EqDecision A}.
Variable children:A->list A.
Definition step (node:A) marked := if List.in_dec (fun x y=>decide (x=y)) node marked then children node++marked else marked.
Fixpoint sweep schedule marked := match schedule with
| []=>marked | node::rest=>sweep rest (step node marked) end.
Fixpoint forward schedule : Prop := match schedule with
| []=>True | node::rest=>(forall child, In child (children node)->In child rest)/\forward rest end.
Lemma step_in node marked value : In value (step node marked) <->
  In value marked \/ (In node marked /\ In value (children node)).
Proof. unfold step. destruct (List.in_dec (fun x y=>decide (x=y)) node marked);rewrite ?in_app_iff;tauto. Qed.
Lemma step_monotone node marked value : In value marked -> In value (step node marked).
Proof. rewrite step_in. tauto. Qed.
Lemma sweep_monotone schedule marked value : In value marked -> In value (sweep schedule marked).
Proof. induction schedule as [|node rest IH] in marked|-*;cbn;[tauto|]. intro Hin. apply IH,step_monotone,Hin. Qed.
Lemma forward_targets schedule : forward schedule -> forall node child,
  In node schedule -> In child (children node)->In child schedule.
Proof.
  induction schedule as [|head rest IH];[cbn;tauto|]. intros [Hhead Hrest] node child [->|Hin] Hchild.
  - right. now apply Hhead.
  - right. eapply IH;eauto.
Qed.
Lemma sweep_outside schedule marked value : forward schedule -> ~In value schedule ->
  (In value (sweep schedule marked)<->In value marked).
Proof.
  induction schedule as [|node rest IH] in marked|-*;[cbn;tauto|]. intros [Hhead Hrest] Hout. cbn.
  rewrite (IH (step node marked) Hrest ltac:(intro Hin;apply Hout;right;exact Hin)). rewrite step_in.
  assert (~In value (children node)) by (intro Hin;apply Hout;right;now apply Hhead).
  tauto.
Qed.
Theorem sweep_closed schedule marked : List.NoDup schedule -> forward schedule ->
  forall node child, In node schedule -> In node (sweep schedule marked) ->
    In child (children node) -> In child (sweep schedule marked).
Proof.
  induction schedule as [|head rest IH] in marked|-*;[cbn;tauto|].
  intros Hdup [Hhead Hrest] node child Hnode Hmarked Hchild.
  inversion Hdup as [|head' rest' Hnot Hduprest];subst.
  destruct Hnode as [Hsame|Hnode];[subst node|].
  - cbn in Hmarked|-*. apply sweep_monotone. rewrite step_in. right. split;[|exact Hchild].
    apply (proj1 (sweep_outside rest (step head marked) head Hrest Hnot)) in Hmarked.
    rewrite step_in in Hmarked. destruct Hmarked as [Hmarked|[_ Hself]];[exact Hmarked|].
    exfalso. apply Hnot. now apply Hhead.
  - cbn in Hmarked|-*. eapply IH;eauto.
Qed.
Inductive reachable root : A->Prop :=
| reachable_root : reachable root root
| reachable_child parent child : reachable root parent -> In child (children parent)->reachable root child.
Theorem sweep_coverage schedule root : List.NoDup schedule -> forward schedule ->
  (forall node, reachable root node->In node schedule) ->
  forall node, reachable root node -> In node (sweep schedule [root]).
Proof.
  intros Hdup Hforward Hall node Hreach. induction Hreach as [|parent child Hparent IH Hchild].
  - apply sweep_monotone. now left.
  - eapply sweep_closed;[exact Hdup|exact Hforward|apply Hall;exact Hparent|exact IH|exact Hchild].
Qed.
Lemma step_sound root node marked : (forall value, In value marked->reachable root value) ->
  forall value, In value (step node marked)->reachable root value.
Proof. intros Hsound value. rewrite step_in. intros [Hin|[Hnode Hchild]];[now apply Hsound|].
  eapply reachable_child;[exact (Hsound node Hnode)|exact Hchild]. Qed.
Theorem sweep_sound schedule root marked : (forall value, In value marked->reachable root value) ->
  forall value, In value (sweep schedule marked)->reachable root value.
Proof.
  induction schedule as [|head rest IH] in marked|-*;cbn;[tauto|].
  intro Hsound. apply IH. now apply step_sound.
Qed.
Theorem sweep_exact schedule root : List.NoDup schedule -> forward schedule ->
  (forall node, reachable root node->In node schedule) ->
  forall node, In node (sweep schedule [root])<->reachable root node.
Proof.
  intros Hdup Hforward Hall node. split.
  - apply sweep_sound. intros value [<-|Hnone];[constructor|contradiction].
  - now apply sweep_coverage.
Qed.
End Generic.
End SchemaMarkingClosure.
