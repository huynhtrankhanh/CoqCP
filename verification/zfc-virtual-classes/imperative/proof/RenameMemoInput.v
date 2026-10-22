From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashTable FormulaEncoding Representation FormulaTopology
  RenameMemoWork RenameMemoArenaWork RenameMemoScheduleRelation RenameMemoIndexBounds RenameMemoTransition.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Module RenameMemoInput.
Import SetTheory IndexExecution SipHashExecution.
Definition atomic_bound (fs : list formula) root bound := forall node i j, (node<=root)%nat ->
  (nth_error fs node=Some (equal i j) \/ nth_error fs node=Some (member i j)) ->
  (i<=bound /\ j<=bound)%nat.

(* A shared source DAG needs only its stored atomic indices bounded. The
   backwards edge order propagates that bound through every source formula. *)
Theorem source_bounds fs root graph bound : RenameMemoScheduleRelation.coherent fs root graph ->
  RenameMemoWork.older graph -> atomic_bound fs root bound -> forall node, (node<=root)%nat ->
  forall p, nth_error fs node=Some p ->
  RenameMemoIndexBounds.formula_bound bound p /\ (RenameMemoTransition.height p<=node)%nat.
Proof.
  intros Hcoherent Hgraph Hatomic node. induction node as [node IH] using lt_wf_ind.
  intros Hnode p Hlookup. pose proof (Hcoherent node p Hnode Hlookup) as Hshape.
  destruct p as [|i j|i j|p q|p]; cbn [RenameMemoIndexBounds.formula_bound RenameMemoTransition.height].
  - split; [exact I|lia].
  - split; [apply Hatomic with (node:=node); [exact Hnode|now left]|lia].
  - split; [apply Hatomic with (node:=node); [exact Hnode|now right]|lia].
  - destruct Hshape as [lhs [rhs [Hg [Hl Hr]]]].
    pose proof (Hgraph node) as Hchildren. rewrite Hg in Hchildren. destruct Hchildren as [Hlhs Hrhs].
    destruct (IH lhs Hlhs ltac:(lia) p Hl) as [Hp Hph].
    destruct (IH rhs Hrhs ltac:(lia) q Hr) as [Hq Hqh]. split; [now split|lia].
  - destruct Hshape as [child [Hg Hchild]].
    pose proof (Hgraph node) as Hchildren. rewrite Hg in Hchildren.
    destruct (IH child Hchildren ltac:(lia) p Hchild) as [Hp Hph]. split; [exact Hp|lia].
Qed.
Theorem source_height fs root graph : RenameMemoScheduleRelation.coherent fs root graph ->
  RenameMemoWork.older graph -> forall node, (node<=root)%nat -> forall p,
  nth_error fs node=Some p -> (RenameMemoTransition.height p<=node)%nat.
Proof.
  intros Hcoherent Hgraph node. induction node as [node IH] using lt_wf_ind.
  intros Hnode p Hlookup. pose proof (Hcoherent node p Hnode Hlookup) as Hshape.
  destruct p as [|i j|i j|p q|p]; cbn [RenameMemoTransition.height]; try lia.
  - destruct Hshape as [lhs [rhs [Hg [Hl Hr]]]].
    pose proof (Hgraph node) as Hchildren. rewrite Hg in Hchildren. destruct Hchildren as [Hlhs Hrhs].
    pose proof (IH lhs Hlhs ltac:(lia) p Hl). pose proof (IH rhs Hrhs ltac:(lia) q Hr). lia.
  - destruct Hshape as [child [Hg Hchild]].
    pose proof (Hgraph node) as Hchildren. rewrite Hg in Hchildren.
    pose proof (IH child Hchildren ltac:(lia) p Hchild). lia.
Qed.

Definition raw_bound bound (raw : FormulaEncoding.raw_node) := let '(tag,a,b):=raw in
  (tag=1%Z \/ tag=2%Z) -> (Z.to_nat a<=bound /\ Z.to_nat b<=bound)%nat.
Definition input_bound s root bound := forall node, (node<=root)%nat ->
  raw_bound bound (HashTableInvariant.tuple_at s node).
Lemma decoded_atomic_bound fs raw bound p : FormulaEncoding.decode fs raw=Some p -> raw_bound bound raw ->
  match p with equal i j | member i j=>(i<=bound /\ j<=bound)%nat | _=>True end.
Proof.
  destruct raw as [[tag a] b]. unfold FormulaEncoding.decode,raw_bound.
  intros Hdecode Hraw.
  destruct (Z.eq_dec tag 0%Z) as [->|H0].
  - injection Hdecode as <-. exact I.
  - destruct (Z.eq_dec tag 1%Z) as [->|H1].
    + injection Hdecode as <-. apply Hraw. now left.
    + destruct (Z.eq_dec tag 2%Z) as [->|H2].
      * injection Hdecode as <-. apply Hraw. now right.
      * destruct (Z.eq_dec tag 3%Z) as [->|H3].
        -- destruct (nth_error fs (Z.to_nat a)) as [lhs|] eqn:Hl; [|discriminate].
           destruct (nth_error fs (Z.to_nat b)) as [rhs|] eqn:Hr; [|discriminate].
           injection Hdecode as <-. exact I.
        -- destruct (Z.eq_dec tag 4%Z) as [->|H4]; [|discriminate].
           destruct (nth_error fs (Z.to_nat a)) as [child|] eqn:Hchild; [|discriminate].
           injection Hdecode as <-. exact I.
Qed.
Theorem canonical_atomic_bound s fs root bound : NativeRepresentation.canonical_arena s fs ->
  input_bound s root bound -> atomic_bound fs root bound.
Proof.
  intros [_ [Hrep _]] Hinput node i j Hnode [Hlookup|Hlookup].
  - pose proof (NativeRepresentation.represented_lookup s fs node (equal i j) Hrep Hlookup) as Hdecode.
    exact (decoded_atomic_bound fs _ bound (equal i j) Hdecode (Hinput node Hnode)).
  - pose proof (NativeRepresentation.represented_lookup s fs node (member i j) Hrep Hlookup) as Hdecode.
    exact (decoded_atomic_bound fs _ bound (member i j) Hdecode (Hinput node Hnode)).
Qed.
Theorem canonical_source_bounds s fs root bound source : NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs root=Some source -> input_bound s root bound ->
  RenameMemoIndexBounds.formula_bound bound source /\ (RenameMemoTransition.height source<=root)%nat.
Proof.
  intros Harena Hordered Hlookup Hinput.
  assert (Hroot : (root<length fs)%nat) by (apply nth_error_Some; congruence).
  apply (source_bounds fs root (RenameMemoArenaWork.graph s (S root)) bound).
  - now apply RenameMemoScheduleRelation.canonical_coherent.
  - apply RenameMemoArenaWork.graph_older. intros parent child Hparent Hchild. apply Hordered with (parent:=parent); [lia|exact Hchild].
  - now apply canonical_atomic_bound with (s:=s).
  - lia.
  - exact Hlookup.
Qed.
Theorem canonical_source_height s fs root source : NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs root=Some source ->
  (RenameMemoTransition.height source<=root)%nat.
Proof.
  intros Harena Hordered Hlookup.
  assert (Hroot : (root<length fs)%nat) by (apply nth_error_Some; congruence).
  apply (source_height fs root (RenameMemoArenaWork.graph s (S root))).
  - now apply RenameMemoScheduleRelation.canonical_coherent.
  - apply RenameMemoArenaWork.graph_older. intros parent child Hparent Hchild. apply Hordered with (parent:=parent); [lia|exact Hchild].
  - lia.
  - exact Hlookup.
Qed.
Theorem source_depth_word s fs root source base : NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs root=Some source ->
  (Z.of_nat base+Z.of_nat root<=maximum)%Z ->
  (Z.of_nat (base+RenameMemoTransition.height source)<=maximum)%Z.
Proof. intros Harena Hordered Hlookup Hword. pose proof (canonical_source_height s fs root source Harena Hordered Hlookup). lia. Qed.
Definition raw_index_max (raw : FormulaEncoding.raw_node) := let '(tag,a,b):=raw in
  if Z.eq_dec tag 1%Z then Nat.max (Z.to_nat a) (Z.to_nat b)
  else if Z.eq_dec tag 2%Z then Nat.max (Z.to_nat a) (Z.to_nat b) else 0%nat.
Fixpoint indices_max s count : nat := match count with
  | 0=>0 | S count=>Nat.max (indices_max s count) (raw_index_max (HashTableInvariant.tuple_at s count)) end.
Lemma raw_bound_monotone lower upper raw : raw_bound lower raw -> (lower<=upper)%nat -> raw_bound upper raw.
Proof. destruct raw as [[tag a] b]. unfold raw_bound. intros Hraw Hbound Htag. destruct (Hraw Htag). split; lia. Qed.
Lemma raw_bound_max raw : raw_bound (raw_index_max raw) raw.
Proof.
  destruct raw as [[tag a] b]. unfold raw_bound,raw_index_max.
  intros [Htag | Htag]; subst tag; cbn; split; [apply Nat.le_max_l|apply Nat.le_max_r|apply Nat.le_max_l|apply Nat.le_max_r].
Qed.
Lemma stored_index_bound s count node : (node<count)%nat ->
  raw_bound (indices_max s count) (HashTableInvariant.tuple_at s node).
Proof.
  induction count as [|count IH]; [lia|]. intro Hnode. cbn [indices_max].
  destruct (Nat.eq_dec node count) as [->|Hother].
  - apply raw_bound_monotone with (lower:=raw_index_max (HashTableInvariant.tuple_at s count)); [apply raw_bound_max|apply Nat.le_max_r].
  - apply raw_bound_monotone with (lower:=indices_max s count); [apply IH; lia|apply Nat.le_max_l].
Qed.
Theorem computed_input_bound s root : input_bound s root (indices_max s (S root)).
Proof. intros node Hnode. apply stored_index_bound. lia. Qed.
Theorem computed_source_bounds s fs root source : NativeRepresentation.canonical_arena s fs ->
  FormulaTopology.ordered s (length fs) -> nth_error fs root=Some source ->
  RenameMemoIndexBounds.formula_bound (indices_max s (S root)) source /\
  (RenameMemoTransition.height source<=root)%nat.
Proof. intros Harena Hordered Hlookup. apply canonical_source_bounds with (s:=s) (fs:=fs) (root:=root); [exact Harena|exact Hordered|exact Hlookup|apply computed_input_bound]. Qed.
End RenameMemoInput.
