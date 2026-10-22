From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashTable FormulaEncoding Representation
  FormulaTopology RenameStack RenameMemoWork RenameMemoSchedule RenameMemoArenaWork RenameMemoArenaPrefix.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Import ListNotations.
Module RenameMemoScheduleRelation.
Import SetTheory IndexExecution SipHashExecution.

Inductive frame (fs : list formula) (root : nat) : RenameMemoSchedule.frame -> RenameStack.frame -> Prop :=
| visit node depth p : (node<=root)%nat -> nth_error fs node=Some p ->
    frame fs root (RenameMemoSchedule.visit node depth) (RenameStack.visit p depth)
| left node depth p q : (node<=root)%nat -> nth_error fs node=Some (implies p q) ->
    frame fs root (RenameMemoSchedule.waiting_left node depth) (RenameStack.left_done p q depth)
| right node depth p q value : (node<=root)%nat -> nth_error fs node=Some (implies p q) ->
    frame fs root (RenameMemoSchedule.waiting_right node depth) (RenameStack.right_done p q depth value)
| body node depth p : (node<=root)%nat -> nth_error fs node=Some (all p) ->
    frame fs root (RenameMemoSchedule.waiting_body node depth) (RenameStack.body_done p depth).
Definition relates fs root := Forall2 (frame fs root).
Definition shape (fs : list formula) (graph : nat->RenameMemoWork.shape) (node : nat) p : Prop := match p with
| falsity | equal _ _ | member _ _ => graph node=RenameMemoWork.leaf
| implies p q => exists lhs rhs, graph node=RenameMemoWork.binary lhs rhs /\
    nth_error fs lhs=Some p /\ nth_error fs rhs=Some q
| all p => exists child, graph node=RenameMemoWork.binder child /\ nth_error fs child=Some p
end.
Definition coherent fs root graph := forall node p, (node<=root)%nat -> nth_error fs node=Some p -> shape fs graph node p.

Lemma decoded_shape s fs count node p : (node<count)%nat ->
  FormulaEncoding.decode fs (HashTableInvariant.tuple_at s node)=Some p ->
  shape fs (RenameMemoArenaWork.graph s count) node p.
Proof.
  intros Hnode Hdecode. unfold shape, RenameMemoArenaWork.graph.
  destruct (Nat.lt_dec node count) as [Hin|Hout]; [|lia].
  destruct (HashTableInvariant.tuple_at s node) as [[tag a] b] eqn:Hraw.
  cbn [FormulaEncoding.decode] in Hdecode.
  destruct (Z.eq_dec tag 0) as [->|H0].
  - injection Hdecode as <-. cbn [shape]. reflexivity.
  - destruct (Z.eq_dec tag 1) as [->|H1].
    + injection Hdecode as <-. cbn [shape]. reflexivity.
    + destruct (Z.eq_dec tag 2) as [->|H2].
      * injection Hdecode as <-. cbn [shape]. reflexivity.
      * destruct (Z.eq_dec tag 3) as [->|H3].
        -- destruct (nth_error fs (Z.to_nat a)) as [lhs|] eqn:Hlhs; [|discriminate].
           destruct (nth_error fs (Z.to_nat b)) as [rhs|] eqn:Hrhs; [|discriminate].
           injection Hdecode as <-. cbn [shape]. exists (Z.to_nat a),(Z.to_nat b). auto.
        -- destruct (Z.eq_dec tag 4) as [->|H4]; [|discriminate].
           destruct (nth_error fs (Z.to_nat a)) as [child|] eqn:Hchild; [|discriminate].
           injection Hdecode as <-. cbn [shape]. exists (Z.to_nat a). auto.
Qed.
Theorem canonical_coherent s fs root : NativeRepresentation.canonical_arena s fs ->
  (root<length fs)%nat -> coherent fs root (RenameMemoArenaWork.graph s (S root)).
Proof.
  intros [_ [Hrep _]] Hroot node p Hnode Hlookup. apply decoded_shape; [lia|].
  now apply NativeRepresentation.represented_lookup with (s:=s).
Qed.
Theorem extended_coherent s t fs extra root : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena t (fs++extra) -> (root<length fs)%nat ->
  coherent fs root (RenameMemoArenaWork.graph t (S root)).
Proof.
  intros Harena Hnext Hroot node p Hnode Hlookup.
  pose proof (canonical_coherent s fs root Harena Hroot node p Hnode Hlookup) as Hshape.
  destruct p; cbn [shape] in *;
    now rewrite (RenameMemoArenaPrefix.source_graph s t fs extra root Harena Hnext Hroot node).
Qed.

Theorem source_id_unique fs extra node other p : FormulaEncoding.unique (fs++extra) ->
  nth_error fs node=Some p -> nth_error (fs++extra) other=Some p -> node=other.
Proof. intros Hunique Hnode Hother. apply Hunique with (p:=p); [now apply FormulaEncoding.nth_error_extend|assumption]. Qed.
Lemma frame_extend fs extra root indexed typed : frame fs root indexed typed -> frame (fs++extra) root indexed typed.
Proof. intro Hframe. destruct Hframe; constructor; try assumption; now apply FormulaEncoding.nth_error_extend. Qed.
Theorem relates_extend fs extra root indexed typed : relates fs root indexed typed -> relates (fs++extra) root indexed typed.
Proof. intro Hrel. induction Hrel as [|i t itail ts Hframe Htail IH]; [constructor|]. constructor; [now apply frame_extend|exact IH]. Qed.
Lemma relates_length fs root indexed typed : relates fs root indexed typed -> length indexed=length typed.
Proof. intro Hrel. induction Hrel; cbn; congruence. Qed.
Lemma relates_visit fs root indexed p depth tail : relates fs root indexed (RenameStack.visit p depth::tail) ->
  exists node indices, indexed=RenameMemoSchedule.visit node depth::indices /\ (node<=root)%nat /\
    nth_error fs node=Some p /\ relates fs root indices tail.
Proof.
  intro Hrel. inversion Hrel as [|index task indices tasks Hframe Htail]; subst.
  inversion Hframe; subst. eauto 10.
Qed.
Lemma relates_left fs root indexed p q depth tail : relates fs root indexed (RenameStack.left_done p q depth::tail) ->
  exists node indices, indexed=RenameMemoSchedule.waiting_left node depth::indices /\ (node<=root)%nat /\
    nth_error fs node=Some (implies p q) /\ relates fs root indices tail.
Proof.
  intro Hrel. inversion Hrel as [|index task indices tasks Hframe Htail]; subst.
  inversion Hframe; subst. eauto 10.
Qed.
Lemma relates_right fs root indexed p q depth value tail : relates fs root indexed (RenameStack.right_done p q depth value::tail) ->
  exists node indices, indexed=RenameMemoSchedule.waiting_right node depth::indices /\ (node<=root)%nat /\
    nth_error fs node=Some (implies p q) /\ relates fs root indices tail.
Proof.
  intro Hrel. inversion Hrel as [|index task indices tasks Hframe Htail]; subst.
  inversion Hframe; subst. eauto 10.
Qed.
Lemma relates_body fs root indexed p depth tail : relates fs root indexed (RenameStack.body_done p depth::tail) ->
  exists node indices, indexed=RenameMemoSchedule.waiting_body node depth::indices /\ (node<=root)%nat /\
    nth_error fs node=Some (all p) /\ relates fs root indices tail.
Proof.
  intro Hrel. inversion Hrel as [|index task indices tasks Hframe Htail]; subst.
  inversion Hframe; subst. eauto 10.
Qed.
Lemma child_bound graph root node child : RenameMemoWork.older graph -> (node<=root)%nat ->
  ((exists other, graph node=RenameMemoWork.binary child other \/ graph node=RenameMemoWork.binary other child) \/
    graph node=RenameMemoWork.binder child) -> (child<=root)%nat.
Proof.
  intros Hgraph Hnode Hchild. specialize (Hgraph node).
  destruct Hchild as [[other [Hshape|Hshape]]|Hshape]; rewrite Hshape in Hgraph; cbn in Hgraph; lia.
Qed.

(* The miss premise is a semantic fact supplied by the native cache relation:
   a failed lookup cannot belong to the list of already completed keys. *)
Theorem tick_move fs root graph rho indexed typed value visited completed hits returns :
  coherent fs root graph -> RenameMemoWork.older graph -> relates fs root indexed typed -> indexed<>[] ->
  (forall node depth tail, indexed=RenameMemoSchedule.visit node depth::tail -> ~In (node,depth) completed) ->
  exists next, RenameMemoSchedule.move graph
      (RenameMemoSchedule.config visited completed indexed hits returns) next /\
    relates fs root (RenameMemoSchedule.stack next) (fst (RenameStack.tick rho (typed,value))).
Proof.
  intros Hcoherent Hgraph Hrel Hnonempty Hmiss.
  destruct Hrel as [|index task indices tasks Hframe Htail]; [contradiction|].
  destruct Hframe as [node depth p Hnode Hlookup|node depth p q Hnode Hlookup|
    node depth p q leftvalue Hnode Hlookup|node depth p Hnode Hlookup].
  - assert (Habsent : ~In (node,depth) completed).
    { apply (Hmiss node depth indices); reflexivity. }
    pose proof (Hcoherent node p Hnode Hlookup) as Hshape.
    destruct p as [|i j|i j|p q|p]; cbn [shape] in Hshape.
    + eexists. split; [now apply RenameMemoSchedule.leaf|exact Htail].
    + eexists. split; [now apply RenameMemoSchedule.leaf|exact Htail].
    + eexists. split; [now apply RenameMemoSchedule.leaf|exact Htail].
    + destruct Hshape as [lhs [rhs [Hg [Hl Hr]]]].
      eexists. split; [now apply RenameMemoSchedule.binary with (lhs:=lhs) (rhs:=rhs)|].
      cbn [RenameMemoSchedule.stack RenameStack.tick fst]. constructor; [|constructor; [now constructor|exact Htail]].
      constructor; [apply child_bound with (graph:=graph) (node:=node); [exact Hgraph|exact Hnode|left; exists rhs; now left]|exact Hl].
    + destruct Hshape as [child [Hg Hchild]].
      eexists. split; [now apply RenameMemoSchedule.binder with (body:=child)|].
      cbn [RenameMemoSchedule.stack RenameStack.tick fst]. constructor; [|constructor; [now constructor|exact Htail]].
      constructor; [apply child_bound with (graph:=graph) (node:=node); [exact Hgraph|exact Hnode|now right]|exact Hchild].
  - destruct (Hcoherent node (implies p q) Hnode Hlookup) as [lhs [rhs [Hg [Hl Hr]]]].
    eexists. split; [now apply RenameMemoSchedule.next with (lhs:=lhs) (rhs:=rhs)|].
    cbn [RenameMemoSchedule.stack RenameStack.tick fst]. constructor; [|constructor; [now constructor|exact Htail]].
    constructor; [apply child_bound with (graph:=graph) (node:=node); [exact Hgraph|exact Hnode|left; exists lhs; now right]|exact Hr].
  - eexists. split; [apply RenameMemoSchedule.join|exact Htail].
  - eexists. split; [apply RenameMemoSchedule.close|exact Htail].
Qed.
Theorem cached_move fs root graph node depth tail p tasks visited completed hits returns :
  relates fs root (RenameMemoSchedule.visit node depth::tail) (RenameStack.visit p depth::tasks) ->
  exists next, RenameMemoSchedule.move graph
    (RenameMemoSchedule.config visited completed (RenameMemoSchedule.visit node depth::tail) hits returns) next /\
    relates fs root (RenameMemoSchedule.stack next) tasks.
Proof.
  intro Hrel. inversion Hrel as [|index task indices tailtyped Hframe Htail]; subst.
  eexists. split; [apply RenameMemoSchedule.hit|exact Htail].
Qed.
End RenameMemoScheduleRelation.
