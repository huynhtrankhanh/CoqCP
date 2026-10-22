From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashTable FormulaEncoding FormulaTopology Representation RenameMemoArenaPrefix.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Module RenameMemoTopology.
Import SetTheory IndexExecution SipHashExecution.
Fixpoint size p : nat := match p with
  | falsity | equal _ _ | member _ _=>1
  | implies p q=>S (size p+size q)
  | all p=>S (size p) end.
Lemma decoded_child_smaller fs raw p child : FormulaEncoding.decode fs raw=Some p ->
  FormulaTopology.children raw child -> exists q,nth_error fs child=Some q /\ (size q<size p)%nat.
Proof.
  destruct raw as [[tag a] b]. intros Hdecode [[Htag [Ha|Hb]]|[Htag Ha]]; subst tag; subst child.
  all: cbn [FormulaEncoding.decode] in Hdecode.
  all: destruct (nth_error fs (Z.to_nat a)) as [left|] eqn:Hleft; try discriminate.
  all: try (lazymatch type of Hdecode with context [nth_error ?meaning ?index]=>
    destruct (nth_error meaning index) as [right|] eqn:Hright; try discriminate end).
  all: injection Hdecode as <-; eexists; split; [reflexivity|cbn [size]; lia].
Qed.
Theorem child_distinct s fs parent child : NativeRepresentation.represents s fs ->
  (parent<length fs)%nat -> FormulaTopology.children (HashTableInvariant.tuple_at s parent) child -> child<>parent.
Proof.
  intros Hrep Hparent Hchild Hsame. subst child.
  destruct (nth_error fs parent) as [p|] eqn:Hlookup; [|apply nth_error_None in Hlookup; lia].
  pose proof (NativeRepresentation.represented_lookup s fs parent p Hrep Hlookup) as Hdecode.
  destruct (decoded_child_smaller fs _ p parent Hdecode Hchild) as [q [Hq Hsmaller]].
  rewrite Hlookup in Hq. injection Hq as <-. lia.
Qed.
(* No intern-specific effect proof is required. A fresh final node cannot point
   to itself because its represented child has strictly smaller formula size. *)
Theorem preserves s t fs next : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena t next -> (exists extra,next=fs++extra) ->
  (length next<=S (length fs))%nat -> FormulaTopology.ordered s (length fs) ->
  FormulaTopology.ordered t (length next).
Proof.
  intros Harena Hnext [extra Hextends] Hgrowth Hordered parent child Hparent Hchild.
  destruct (Nat.lt_dec parent (length fs)) as [Hold|Hnew].
  - apply Hordered; [exact Hold|].
    assert (Hraw : HashTableInvariant.tuple_at t parent=HashTableInvariant.tuple_at s parent).
    { eapply RenameMemoArenaPrefix.canonical_prefix; [exact Harena|rewrite <-Hextends; exact Hnext|exact Hold]. }
    now rewrite <-Hraw.
  - assert (Hlast : parent=length fs) by lia.
    pose proof (FormulaTopology.decoded_children next (HashTableInvariant.tuple_at t parent)
      (List.nth parent next falsity) child (proj1 (proj2 Hnext) parent Hparent) Hchild) as Hallocated.
    pose proof (child_distinct t next parent child (proj1 (proj2 Hnext)) Hparent Hchild) as Hdistinct.
    lia.
Qed.
End RenameMemoTopology.
