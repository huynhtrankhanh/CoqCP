From CoqCP Require Import Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash SchemaGraph SchemaMarking SchemaMarkingSchedule ArrayFacts Overflow.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import base list.
Import ListNotations.
Open Scope Z_scope.
Module SchemaMarkingNative.
Import IndexExecution SipHashExecution.
Definition represents root (s:Machine) marked := forall node depth,
  (node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
  (SchemaMarking.cell s (SchemaGraph.key root node depth)<>0 <-> In (node,depth) marked).
Lemma initialized_represents s root : represents root (SchemaMarking.initialized s root) [(root,0%nat)].
Proof.
  intros node depth Hnode Hdepth. rewrite SchemaMarking.initialized_cell by (now apply SchemaGraph.grid_bound).
  destruct (Nat.eqb (SchemaGraph.key root node depth) (SchemaGraph.key root root 0)) eqn:Hkey.
  - apply Nat.eqb_eq in Hkey. destruct (SchemaGraph.key_injective root node depth root 0 Hdepth ltac:(unfold SchemaGraph.width;lia) Hkey) as [-> ->]. cbn. lia.
  - cbn. split;[lia|]. intros [Heq|Hnone];[inversion Heq;subst;rewrite Nat.eqb_refl in Hkey;discriminate|contradiction].
Qed.
Lemma mark_cell s index target : (index<length (memory s arraydef_0__schemaMarks))%nat ->
  SchemaMarking.cell (SchemaGraph.marked s index) target=
  if Nat.eqb target index then 1 else SchemaMarking.cell s target.
Proof.
  intro Hbound. unfold SchemaMarking.cell,SchemaGraph.marked. cbn [memory withMemory].
  change (List.nth target (<[index:=1]>(memory s arraydef_0__schemaMarks)) 0=if Nat.eqb target index then 1 else List.nth target (memory s arraydef_0__schemaMarks) 0).
  destruct (Nat.eq_dec target index) as [->|Hneq].
  - rewrite Nat.eqb_refl. now apply OverflowExecution.nth_insert_same.
  - rewrite (proj2 (Nat.eqb_neq _ _) Hneq). now apply ArrayFacts.nth_insert_other.
Qed.
Lemma marked_represents root s marked child childDepth : represents root s marked ->
  (SchemaMarking.size root<=length (memory s arraydef_0__schemaMarks))%nat ->
  (child<SchemaGraph.width root)%nat -> (childDepth<SchemaGraph.width root)%nat ->
  represents root (SchemaGraph.marked s (SchemaGraph.key root child childDepth)) ((child,childDepth)::marked).
Proof.
  intros Hrep Hcapacity Hchild Hcd node depth Hnode Hdepth.
  rewrite mark_cell by (pose proof (SchemaGraph.grid_bound root child childDepth Hchild Hcd);unfold SchemaMarking.size in Hcapacity;lia).
  destruct (Nat.eqb (SchemaGraph.key root node depth) (SchemaGraph.key root child childDepth)) eqn:Hkey.
  - apply Nat.eqb_eq in Hkey. destruct (SchemaGraph.key_injective root node depth child childDepth Hdepth Hcd Hkey) as [-> ->]. cbn. lia.
  - rewrite Hrep by assumption. cbn. split;[tauto|]. intros [Heq|Hin];[inversion Heq;subst;rewrite Nat.eqb_refl in Hkey;discriminate|exact Hin].
Qed.
Lemma represents_membership root s left right : represents root s left ->
  (forall pair, In pair left <-> In pair right) -> represents root s right.
Proof. intros Hrep Heq node depth Hn Hd. rewrite <-Heq. now apply Hrep. Qed.
Theorem children_represents root s marked depth children : represents root s marked ->
  (SchemaMarking.size root<=length (memory s arraydef_0__schemaMarks))%nat ->
  (forall child extra, In (child,extra) children -> (child<SchemaGraph.width root /\ depth+extra<SchemaGraph.width root)%nat) ->
  represents root (SchemaMarking.mark_children s root depth children)
    (map (fun pair=>(fst pair,(depth+snd pair)%nat)) children++marked).
Proof.
  induction children as [|[child extra] rest IH] in s,marked|-*;cbn;[tauto|]. intros Hrep Hcapacity Hall.
  destruct (Hall child extra (or_introl eq_refl)) as [Hchild Hdepth].
  pose proof (marked_represents root s marked child (depth+extra) Hrep Hcapacity Hchild Hdepth) as Hmarked.
  assert (Hrest:represents root (SchemaMarking.mark_children (SchemaGraph.marked s (SchemaGraph.key root child (depth+extra))) root depth rest)
    (map (fun pair=>(fst pair,(depth+snd pair)%nat)) rest++(child,(depth+extra)%nat)::marked)).
  { apply IH;[exact Hmarked|rewrite SchemaMarking.marked_length;exact Hcapacity|]. intros c e Hin. apply Hall. now right. }
  eapply represents_membership;[exact Hrest|]. intro pair. rewrite !in_app_iff. cbn. tauto.
Qed.
End SchemaMarkingNative.
