From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts HashScan InternTail.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module HashTableInvariant.
Import IndexExecution HashScanExecution InternTailExecution.
Definition tuple_at (s : Machine) i := List.nth i (memory s arraydef_0__formulas) (0,0,0).
Definition head_at (s : Machine) b := List.nth b (memory s arraydef_0__formulaBuckets) 0.
(* The bucket function is arbitrary. Colliding tuples need not be equal. *)
Definition indexed (s : Machine) n (bucket_of : Z * Z * Z -> nat) :=
  table_valid s n /\
  (forall b, (b < length (memory s arraydef_0__formulaBuckets))%nat ->
    0 <= head_at s b <= Z.of_nat n) /\
  forall i, (i < n)%nat ->
    (bucket_of (tuple_at s i) < length (memory s arraydef_0__formulaBuckets))%nat /\
    in_chain s (Z.to_nat (head_at s (bucket_of (tuple_at s i)))) i.

Lemma append_head_same s n bucket tuple :
  (bucket < length (memory s arraydef_0__formulaBuckets))%nat ->
  head_at (append_state s n bucket tuple) bucket = Z.of_nat (S n).
Proof. intro H. unfold head_at. rewrite append_buckets.
  now apply OverflowExecution.nth_insert_same. Qed.
Lemma append_head_other s n bucket tuple b : b <> bucket ->
  head_at (append_state s n bucket tuple) b = head_at s b.
Proof. intro H. unfold head_at. rewrite append_buckets.
  now apply ArrayFacts.nth_insert_other. Qed.
Lemma append_bucket_length s n bucket tuple :
  length (memory (append_state s n bucket tuple) arraydef_0__formulaBuckets) =
  length (memory s arraydef_0__formulaBuckets).
Proof. rewrite append_buckets. apply length_insert. Qed.

Theorem append_indexed s n tuple bucket_of :
  indexed s n bucket_of ->
  (bucket_of tuple < length (memory s arraydef_0__formulaBuckets))%nat ->
  indexed (append_state s n (bucket_of tuple) tuple) (S n) bucket_of.
Proof.
  intros [Htable [Hheads Hindexed]] Hbucket.
  pose proof (Hheads (bucket_of tuple) Hbucket) as Hhead.
  split; [now apply append_table_valid|]. split.
  - intros b Hb. rewrite append_bucket_length in Hb.
    destruct (Nat.eq_dec b (bucket_of tuple)) as [->|Hne].
    + rewrite append_head_same by exact Hbucket. lia.
    + rewrite append_head_other by exact Hne. specialize (Hheads b Hb). lia.
  - intros i Hi. unfold tuple_at.
    destruct (Nat.eq_dec i n) as [->|Hne].
    + rewrite append_formula_new. split; [now rewrite append_bucket_length|].
      rewrite append_head_same by exact Hbucket. rewrite Nat2Z.id. constructor.
    + rewrite append_formula_previous by (unfold table_valid in Htable; lia).
      destruct (Hindexed i ltac:(lia)) as [Hrange Hchain].
      split; [now rewrite append_bucket_length|].
      destruct (Nat.eq_dec (bucket_of (tuple_at s i)) (bucket_of tuple)) as [Heq|Hneq].
      * change (in_chain (append_state s n (bucket_of tuple) tuple)
          (Z.to_nat (head_at (append_state s n (bucket_of tuple) tuple)
            (bucket_of (tuple_at s i)))) i).
        rewrite Heq, append_head_same by exact Hbucket. rewrite Nat2Z.id.
        apply chain_tail. rewrite append_link_new.
        apply append_chain_previous; [exact Htable| |now rewrite <- Heq].
        change (Z.to_nat (head_at s (bucket_of tuple)) <= n)%nat.
        pose proof (Z2Nat.id (head_at s (bucket_of tuple)) ltac:(lia)). lia.
      * change (in_chain (append_state s n (bucket_of tuple) tuple)
          (Z.to_nat (head_at (append_state s n (bucket_of tuple) tuple)
            (bucket_of (tuple_at s i)))) i).
        rewrite append_head_other by exact Hneq.
        apply append_chain_previous; [exact Htable| |exact Hchain].
        pose proof (Hheads _ Hrange) as Hbound.
        pose proof (Z2Nat.id (head_at s (bucket_of (tuple_at s i))) ltac:(lia)). lia.
Qed.

(* Completeness of lookup gives freshness without any collision assumption. *)
Theorem scan_miss_absent f n bucket_of final :
  indexed (machine f) n bucket_of -> Z.of_nat n <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_current = Z.of_nat (Z.to_nat (head_at (machine f) (bucket_of (sought f)))) ->
  (bucket_of (sought f) < length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal (loop n scan_body) f = Some (tt,final) ->
  nums final vardef_0__intern_found = 0 ->
  forall i, (i < n)%nat -> tuple_at (machine f) i <> sought f.
Proof.
  intros [Htable [Hheads Hindexed]] Hlimit Hmeta Hpointer Hbucket Hrun Hmiss i Hi Heq.
  destruct (Hindexed i Hi) as [Hrange Hchain]. rewrite Heq in Hchain.
  pose proof (Hheads _ Hbucket) as Hhead.
  assert (Hbound : (Z.to_nat (head_at (machine f) (bucket_of (sought f))) <= n)%nat).
  { pose proof (Z2Nat.id (head_at (machine f) (bucket_of (sought f))) ltac:(lia)). lia. }
  destruct (scan_loop_complete n f n _ i Htable Hlimit Hmeta Hpointer Hbound Hbound Hchain Heq)
    as [other [Hrun' Hfound]].
  rewrite Hrun in Hrun'. injection Hrun' as <-. congruence.
Qed.

Definition unique (s : Machine) n :=
  forall i j, (i < n)%nat -> (j < n)%nat -> tuple_at s i = tuple_at s j -> i = j.
Lemma append_unique s n bucket tuple : table_valid s n -> unique s n ->
  (forall i, (i < n)%nat -> tuple_at s i <> tuple) ->
  unique (append_state s n bucket tuple) (S n).
Proof.
  intros [Hformulas _] Hunique Hfresh i j Hi Hj Heq.
  unfold tuple_at in Heq.
  destruct (Nat.eq_dec i n) as [->|Hine], (Nat.eq_dec j n) as [->|Hjne].
  - reflexivity.
  - rewrite append_formula_new, append_formula_previous in Heq by lia.
    exfalso. apply (Hfresh j ltac:(lia)). now symmetry.
  - rewrite append_formula_new, append_formula_previous in Heq by lia.
    exfalso. now apply (Hfresh i ltac:(lia)).
  - rewrite !append_formula_previous in Heq by lia. apply Hunique; [lia|lia|exact Heq].
Qed.

Theorem canonical_lookup f n bucket_of index :
  indexed (machine f) n bucket_of -> unique (machine f) n -> Z.of_nat n <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_current = Z.of_nat (Z.to_nat (head_at (machine f) (bucket_of (sought f)))) ->
  nums f vardef_0__intern_found = 0 -> (index < n)%nat -> tuple_at (machine f) index = sought f ->
  exists final, execLocal (loop n scan_body) f = Some (tt,final) /\
    preserves_storage f final /\ nums final vardef_0__intern_found = 1 /\
    List.nth 0 (memory (machine final) arraydef_0__meta) 0 = Z.of_nat index.
Proof.
  intros [Htable [Hheads Hindexed]] Hunique Hlimit Hmeta Hpointer Hfound Hi Htuple.
  destruct (Hindexed index Hi) as [Hbucket Hchain]. rewrite Htuple in Hchain, Hbucket.
  pose proof (Hheads _ Hbucket) as Hhead.
  assert (Hbound : (Z.to_nat (head_at (machine f) (bucket_of (sought f))) <= n)%nat).
  { pose proof (Z2Nat.id (head_at (machine f) (bucket_of (sought f))) ltac:(lia)). lia. }
  destruct (scan_lookup_complete f n _ index Htable Hlimit Hmeta Hpointer Hbound Hfound Hchain Htuple)
    as [final [j [Hrun [Hstorage [Hj [Hflag [Hresult Htuplej]]]]]]].
  change (tuple_at (machine f) j = sought f) in Htuplej.
  assert (j = index) as -> by (apply Hunique; [exact Hj|exact Hi|now rewrite Htuple, Htuplej]).
  exists final. split; [exact Hrun|]. split; [exact Hstorage|]. split; assumption.
Qed.
End HashTableInvariant.
