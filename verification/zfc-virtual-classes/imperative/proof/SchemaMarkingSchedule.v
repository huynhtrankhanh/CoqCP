From CoqCP Require Import Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash SchemaGraph SchemaMetadata SchemaMarkingClosure.
From Stdlib Require Import Lists.List Lia.
From stdpp Require Import base list.
Import ListNotations.
Module SchemaMarkingSchedule.
Import IndexExecution SipHashExecution.
Definition row width (node:nat) := map (fun depth=>(node,depth)) (seq 0 width).
Fixpoint grid width count := match count with 0=>[]|S node=>row width node++grid width node end.
Lemma row_in width node pair : In pair (row width node)<->fst pair=node /\ snd pair<width.
Proof.
  destruct pair as [n d]. unfold row. rewrite in_map_iff. cbn. split.
  - intros (depth & Heq & Hin). inversion Heq;subst. apply in_seq in Hin. lia.
  - intros [-> Hd]. exists d. split;[reflexivity|apply in_seq;lia].
Qed.
Lemma grid_in width count node depth : In (node,depth) (grid width count)<->node<count /\ depth<width.
Proof.
  induction count as [|count IH];cbn;[lia|]. rewrite in_app_iff,row_in,IH. cbn. lia.
Qed.
Lemma nodup_map_injective {A B} (f:A->B) xs : (forall x y, f x=f y->x=y) -> List.NoDup xs -> List.NoDup (map f xs).
Proof.
  intros Hinj Hdup. induction Hdup as [|x xs Hnot Hdup IH];cbn;[constructor|]. constructor;[|exact IH].
  intro Hin. apply in_map_iff in Hin. destruct Hin as (y & Heq & Hy). apply Hinj in Heq. subst y. contradiction.
Qed.
Lemma nodup_append {A} (left right:list A) : List.NoDup left -> List.NoDup right ->
  (forall x, In x left -> ~In x right) -> List.NoDup (left++right).
Proof.
  intros Hleft Hright Hdisjoint. induction Hleft as [|x xs Hnot Hdup IH];cbn;[exact Hright|].
  constructor.
  - rewrite in_app_iff. intro Hin. destruct Hin as [Hin|Hin];[contradiction|exact (Hdisjoint x (or_introl eq_refl) Hin)].
  - apply IH. intros y Hy. apply Hdisjoint. now right.
Qed.
Lemma grid_nodup width count : List.NoDup (grid width count).
Proof.
  induction count as [|count IH];cbn;[constructor|]. apply nodup_append;[|exact IH|].
  - unfold row. apply nodup_map_injective;[intros x y Hxy;now inversion Hxy|apply seq_NoDup].
  - intros [node depth] Hrow Hgrid. apply row_in in Hrow. apply grid_in in Hgrid. cbn in Hrow. lia.
Qed.
Definition dependencies (s:Machine) root pair :=
  let '(node,depth):=pair in
  if le_dec (node+depth) root then
    map (fun child=> (fst child,depth+snd child)) (SchemaGraph.children (SchemaMetadata.node_at s node))
  else [].
Lemma dependency s root node depth child childDepth : SchemaGraph.ordered s ->
  root<length (memory s arraydef_0__schemaNodes) ->
  In (child,childDepth) (dependencies s root (node,depth)) ->
  child<node /\ child+childDepth<=root.
Proof.
  intros Hordered Hroot. unfold dependencies. destruct (le_dec (node+depth) root) as [Hsafe|Hunsafe];[|contradiction].
  rewrite in_map_iff. intros ([id extra] & Heq & Hin). cbn in Heq. inversion Heq;subst id childDepth.
  destruct (Hordered node child extra ltac:(lia) Hin) as [Hlower Hextra]. lia.
Qed.
Lemma forward_prefix {A} (children:A->list A) prefix suffix :
  SchemaMarkingClosure.forward children suffix ->
  (forall node child, In node prefix -> In child (children node)->In child suffix) ->
  SchemaMarkingClosure.forward children (prefix++suffix).
Proof.
  induction prefix as [|head rest IH];cbn;[tauto|]. intros Hsuffix Hall. split.
  - intros child Hchild. apply in_or_app. right. exact (Hall head child (or_introl eq_refl) Hchild).
  - apply IH;[exact Hsuffix|]. intros node child Hnode Hchild. exact (Hall node child (or_intror Hnode) Hchild).
Qed.
Theorem grid_forward s root count : SchemaGraph.ordered s ->
  root<length (memory s arraydef_0__schemaNodes) ->
  SchemaMarkingClosure.forward (dependencies s root) (grid (SchemaGraph.width root) count).
Proof.
  intros Hordered Hroot. induction count as [|count IH];[exact I|].
  change (SchemaMarkingClosure.forward (dependencies s root) (row (SchemaGraph.width root) count++grid (SchemaGraph.width root) count)).
  apply forward_prefix;[exact IH|].
  intros [node depth] [child childDepth] Hrow Hchild. apply row_in in Hrow. cbn in Hrow. destruct Hrow as [-> Hdepth].
  destruct (dependency s root count depth child childDepth Hordered Hroot Hchild) as [Hlower Hsum].
  apply grid_in. unfold SchemaGraph.width. lia.
Qed.
Lemma reachable_to_graph s root node depth : SchemaGraph.ordered s ->
  root<length (memory s arraydef_0__schemaNodes) -> SchemaGraph.reachable s root node depth ->
  SchemaMarkingClosure.reachable (dependencies s root) (root,0) (node,depth).
Proof.
  intros Hordered Hroot Hreach. induction Hreach as [|node depth child extra Hreach IH Hin];[constructor|].
  eapply SchemaMarkingClosure.reachable_child;[exact IH|]. unfold dependencies.
  destruct (SchemaGraph.reachable_bound _ _ _ _ Hordered Hroot Hreach) as [_ Hsafe].
  destruct (le_dec (node+depth) root);[|lia]. apply in_map_iff. exists (child,extra). split;[reflexivity|exact Hin].
Qed.
Lemma graph_to_reachable s root pair : SchemaMarkingClosure.reachable (dependencies s root) (root,0) pair ->
  SchemaGraph.reachable s root (fst pair) (snd pair).
Proof.
  intro Hreach. induction Hreach as [|[node depth] [child childDepth] Hreach IH Hin];[constructor|].
  unfold dependencies in Hin. destruct (le_dec (node+depth) root);[|contradiction].
  apply in_map_iff in Hin. destruct Hin as ([id extra] & Heq & Hin). cbn in Heq. inversion Heq;subst id childDepth.
  eapply SchemaGraph.child_reachable;[exact IH|exact Hin].
Qed.
Theorem scheduled_marks_exact s root node depth : SchemaGraph.ordered s ->
  root<length (memory s arraydef_0__schemaNodes) ->
  (In (node,depth) (SchemaMarkingClosure.sweep (dependencies s root)
    (grid (SchemaGraph.width root) (SchemaGraph.width root)) [(root,0)]) <-> SchemaGraph.reachable s root node depth).
Proof.
  intros Hordered Hroot. rewrite SchemaMarkingClosure.sweep_exact.
  - split;[apply graph_to_reachable|now apply reachable_to_graph].
  - apply grid_nodup.
  - now apply grid_forward.
  - intros [n d] Hreach. apply graph_to_reachable in Hreach.
    destruct (SchemaGraph.reachable_grid _ _ _ _ Hordered Hroot Hreach) as [Hn [Hd _]]. now apply grid_in.
Qed.
End SchemaMarkingSchedule.
