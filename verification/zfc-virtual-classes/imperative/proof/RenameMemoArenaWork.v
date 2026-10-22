From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashTable FormulaTopology RenameMemoBounds RenameMemoWork.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Module RenameMemoArenaWork.
Import IndexExecution SipHashExecution.
Definition graph (s : Machine) count node : RenameMemoWork.shape :=
  if Nat.lt_dec node count then
    let '(tag,a,b):=HashTableInvariant.tuple_at s node in
    if Z.eq_dec tag 3%Z then RenameMemoWork.binary (Z.to_nat a) (Z.to_nat b)
    else if Z.eq_dec tag 4%Z then RenameMemoWork.binder (Z.to_nat a) else RenameMemoWork.leaf
  else RenameMemoWork.leaf.
Theorem graph_older s count : FormulaTopology.ordered s count -> RenameMemoWork.older (graph s count).
Proof.
  intros Hordered node. unfold graph. destruct (Nat.lt_dec node count) as [Hnode|Hnode]; [|exact I].
  destruct (HashTableInvariant.tuple_at s node) as [[tag a] b] eqn:Hraw.
  destruct (Z.eq_dec tag 3%Z) as [->|H3].
  - split; apply Hordered with (parent:=node); try assumption; rewrite Hraw; left; split; [reflexivity|now left|reflexivity|now right].
  - destruct (Z.eq_dec tag 4%Z) as [->|H4]; [|exact I].
    apply Hordered with (parent:=node); [exact Hnode|]. rewrite Hraw. right. split; reflexivity.
Qed.
Theorem arena_polynomial s count root base : FormulaTopology.ordered s count ->
  exists final steps,
    RenameMemoWork.run (S root) (graph s count) root base []=Some (final,steps) /\ List.NoDup final /\
    In (root,base) final /\ (length final<=S root*S root)%nat /\ (steps<=4*(S root*S root)+1)%nat /\
    (steps<=RenameMemoBounds.fuel root)%nat.
Proof. intro Hordered. apply RenameMemoWork.root_polynomial. now apply graph_older. Qed.
End RenameMemoArenaWork.
