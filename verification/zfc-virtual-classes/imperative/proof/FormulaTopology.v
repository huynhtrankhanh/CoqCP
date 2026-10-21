From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash HashTable InternTail InternInvariant Intern InternBounded
  FormulaEncoding Representation RenameMemoBounds.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module FormulaTopology.
Import IndexExecution SipHashExecution HashTableInvariant InternTailExecution FormulaEncoding.
Definition children (raw : raw_node) child := let '(tag,a,b) := raw in
  (tag = 3 /\ (child = Z.to_nat a \/ child = Z.to_nat b)) \/ (tag = 4 /\ child = Z.to_nat a).
Definition ordered s count := forall parent child, (parent < count)%nat ->
  children (tuple_at s parent) child -> (child < parent)%nat.
Theorem decoded_children fs raw p child : decode fs raw = Some p -> children raw child -> (child < length fs)%nat.
Proof.
  destruct raw as [[tag a] b]. intros Hdecode [[Htag [Ha|Hb]]|[Htag Ha]]; subst tag; subst child.
  all: cbn [decode] in Hdecode.
  all: destruct (nth_error fs (Z.to_nat a)) as [left|] eqn:Hleft; try discriminate.
  all: try (destruct (nth_error fs (Z.to_nat b)) as [right|] eqn:Hright; try discriminate).
  all: apply nth_error_Some; congruence.
Qed.
Theorem empty s : ordered s 0.
Proof. intros parent child Hparent. lia. Qed.
Theorem same s t count : ordered s count ->
  (forall parent, (parent < count)%nat -> tuple_at t parent = tuple_at s parent) -> ordered t count.
Proof. intros Hordered Hsame parent child Hparent Hchild. apply Hordered; [exact Hparent|]. now rewrite <-Hsame by exact Hparent. Qed.
Theorem append s t fs raw p : ordered s (length fs) -> decode fs raw = Some p ->
  (forall parent, (parent < length fs)%nat -> tuple_at t parent = tuple_at s parent) ->
  tuple_at t (length fs) = raw -> ordered t (S (length fs)).
Proof.
  intros Hordered Hdecode Hsame Hnew parent child Hparent Hchild.
  destruct (Nat.lt_dec parent (length fs)) as [Hold|Hlast].
  - apply Hordered; [exact Hold|]. now rewrite <-Hsame by exact Hold.
  - assert (parent = length fs) as -> by lia. rewrite Hnew in Hchild. now apply decoded_children with (raw:=raw) (p:=p).
Qed.
Theorem canonical_preserves s t fs raw p : ordered s (length fs) -> decode fs raw = Some p ->
  InternExecution.canonical s t (length fs) raw -> ordered t (Z.to_nat (meta_value t 1)).
Proof.
  intros Hordered Hdecode [_ [count [index [Hshape [Htable [Hindex [Hresult [Hraw Hprefix]]]]]]]].
  pose proof (proj1 (proj2 Htable)) as Hcount. rewrite Hcount,Nat2Z.id.
  destruct Hshape as [->|[-> ->]]; [now apply same with (s:=s)|].
  now apply append with (s:=s) (raw:=raw) (p:=p).
Qed.
Theorem generated_intern_preserves s bs ns fs p : NativeRepresentation.canonical_arena s fs ->
  ordered s (length fs) -> meta_value s 8 = 0 -> Z.of_nat (length fs) <= 9223372036854775807 ->
  decode fs (ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b) = Some p ->
  exists final, exec (funcdef_0__intern bs ns) s = Some (tt,final) /\ meta_value final 8 = 0 /\
    ordered final (Z.to_nat (meta_value final 1)).
Proof.
  intros Harena Hordered Herror Hcapacity Hdecode.
  destruct (InternBounded.generated_intern_bounded s bs ns (length fs) (proj1 Harena) Herror Hcapacity)
    as [final [Hrun [Hframe Hcanonical]]].
  exists final. split; [exact Hrun|]. split; [exact (proj1 Hcanonical)|].
  now apply canonical_preserves with (s:=s) (fs:=fs)
    (raw:=(ns vardef_0__intern_tag,ns vardef_0__intern_a,ns vardef_0__intern_b)) (p:=p).
Qed.
Definition edge raw child binders := let '(tag,a,b) := raw in
  (tag = 3 /\ (child = Z.to_nat a \/ child = Z.to_nat b) /\ binders = 0%nat) \/
  (tag = 4 /\ child = Z.to_nat a /\ binders = 1%nat).
Lemma edge_children raw child binders : edge raw child binders -> children raw child /\ (binders <= 1)%nat.
Proof. destruct raw as [[tag a] b]. intros [[Ht [Hchild ->]]|[Ht [Hchild ->]]]; split; [left|lia|right|lia]; tauto. Qed.
Inductive path (s : Machine) (root base : nat) : nat -> nat -> Prop :=
| path_root : path s root base root base
| path_child parent depth child binders : path s root base parent depth ->
    edge (tuple_at s parent) child binders -> path s root base child (depth+binders)%nat.
Theorem path_reachable s count root base node depth : ordered s count -> (root < count)%nat ->
  path s root base node depth -> RenameMemoBounds.reachable root base node depth.
Proof.
  intros Hordered Hroot Hpath. induction Hpath as [|parent depth child binders Hpath IH Hedge].
  - constructor.
  - destruct (edge_children _ _ _ Hedge) as [Hchild Hbinders].
    pose proof (RenameMemoBounds.reachable_bounds root base parent depth IH) as Hparent.
    apply RenameMemoBounds.reachable_child with (parent:=parent); try assumption.
    apply Hordered; [lia|exact Hchild].
Qed.
Theorem path_bounds s count root base node depth : ordered s count -> (root < count)%nat ->
  path s root base node depth -> (node <= root /\ base <= depth <= base+root)%nat.
Proof. intros Hordered Hroot Hpath. apply RenameMemoBounds.reachable_bounds. now apply path_reachable with (s:=s) (count:=count). Qed.
End FormulaTopology.
