From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashTable FormulaEncoding Representation RenameMemoArenaWork.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoArenaPrefix.
Import IndexExecution SipHashExecution.
Theorem canonical_prefix s t fs extra : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena t (fs++extra) ->
  forall index, (index<length fs)%nat -> HashTableInvariant.tuple_at t index=HashTableInvariant.tuple_at s index.
Proof.
  intros [Htable [Hrep [Hunique Hnormal]]] [Htable' [Hrep' [Hunique' Hnormal']]] index Hindex.
  destruct (nth_error fs index) as [source|] eqn:Hlookup; [|apply nth_error_None in Hlookup; lia].
  apply FormulaEncoding.decode_injective with (meaning:=fs++extra) (p:=source); try assumption.
  - apply Hnormal'. rewrite length_app. lia.
  - now apply Hnormal.
  - apply NativeRepresentation.represented_lookup with (s:=t); [exact Hrep'|now apply FormulaEncoding.nth_error_extend].
  - apply FormulaEncoding.decode_extend. now apply NativeRepresentation.represented_lookup with (s:=s).
Qed.
Theorem source_graph s t fs extra root : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena t (fs++extra) -> (root<length fs)%nat ->
  forall node, RenameMemoArenaWork.graph t (S root) node=RenameMemoArenaWork.graph s (S root) node.
Proof.
  intros Harena Hnext Hroot node. unfold RenameMemoArenaWork.graph. destruct (Nat.lt_dec node (S root)) as [Hnode|Hnode]; [|reflexivity].
  now rewrite (canonical_prefix s t fs extra Harena Hnext node ltac:(lia)).
Qed.
End RenameMemoArenaPrefix.
