From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash HashScan InternTail HashTable Rehash Rebuild ScanFrame InternCore.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module InternInvariant.
Import IndexExecution SipHashExecution InternTailExecution HashTableInvariant RehashExecution RebuildExecution.
Definition table (s : Machine) n := ready s n /\ meta_value s 1 = Z.of_nat n /\
  meta_value s 20 <= maximum /\
  length (memory s arraydef_0__formulaBuckets) = Z.to_nat (meta_value s 20) /\
  Z.of_nat n <= meta_value s 20 /\ indexed s n (keyed_bucket s) /\ unique s n.
Definition stable (s t : Machine) :=
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState -> memory t name = memory s name) /\
  length (memory t arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  length (memory t arraydef_0__sipState) = length (memory s arraydef_0__sipState) /\
  (forall i, i <> 0%nat -> i <> 21%nat -> i <> 28%nat -> meta_value t i = meta_value s i) /\
  stdin t = stdin s /\ stdout t = stdout s.
Lemma stable_refl s : stable s s.
Proof. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. Qed.
Lemma stable_trans s t u : stable s t -> stable t u -> stable s u.
Proof.
  intros [Ha [Hm [Hs [Hc [Hi Ho]]]]] [Ha' [Hm' [Hs' [Hc' [Hi' Ho']]]]].
  split; [intros; now rewrite Ha', Ha by assumption|]. split; [congruence|]. split; [congruence|].
  split; [intros; now rewrite Hc', Hc by assumption|]. split; congruence.
Qed.
Lemma stable_key s t : stable s t -> forall tuple, keyed_bucket t tuple = keyed_bucket s tuple.
Proof. intros [_ [_ [_ [Hcells _]]]] tuple. unfold keyed_bucket. destruct tuple as [[x y] z]. now rewrite !Hcells by lia. Qed.
Lemma stable_table s t n : stable s t -> table s n -> table t n.
Proof.
  intros Hstable [Hready [Hcount [Hlimit [Hbucket [Hload [Hindexed Hunique]]]]]].
  destruct Hstable as [Harray [Hmeta [Hsip [Hcells [Hin Hout]]]]].
  destruct Hready as [Hm [Hs [Hp [Hcap [Hfs [Hls Hn]]]]]].
  split.
  - unfold ready. rewrite Hmeta, Hsip, !Hcells by lia.
    rewrite !Harray by discriminate. repeat split; assumption.
  - rewrite Hcells by lia. split; [exact Hcount|]. rewrite Hcells by lia.
    split; [exact Hlimit|]. rewrite Harray by discriminate. split; [exact Hbucket|].
    split; [exact Hload|]. split.
    + apply (indexed_bucket_ext _ _ (keyed_bucket s)); [intro tuple; symmetry; now apply stable_key|].
      apply (indexed_preserved s); try assumption; now apply Harray.
    + unfold unique, tuple_at in *. intros i j Hi Hj Heq. rewrite Harray in Heq by discriminate. now apply Hunique.
Qed.
Definition hash_tuple (s : Machine) (tuple : Z * Z * Z) := let '(x,y,z) := tuple in hash_state s x y z.
Lemma hash_stable s tuple : stable s (hash_tuple s tuple).
Proof.
  destruct tuple as [[x y] z]. unfold hash_tuple. split; [intros; now apply hash_preserves_array|].
  split; [apply hash_meta_length|]. split.
  - unfold hash_state. rewrite !store_meta_other by discriminate. apply hash_work_length.
  - split; [intros; now apply hash_preserves_meta|]. apply hash_io.
Qed.
Lemma hash_bucket_value s tuple :
  (28 < length (memory s arraydef_0__meta))%nat -> (0 < length (memory s arraydef_0__sipState))%nat ->
  0 < meta_value s 20 ->
  meta_value (hash_tuple s tuple) 21 = Z.of_nat (keyed_bucket s tuple).
Proof.
  intros Hm Hs Hp. destruct tuple as [[x y] z]. unfold hash_tuple, keyed_bucket.
  rewrite hash_bucket by assumption. rewrite Z2Nat.id; [reflexivity|]. pose proof (Z.mod_pos_bound (siphash24 (meta_value s 26) (meta_value s 27) x y z) _ Hp). lia.
Qed.
Lemma bucket_bound s n tuple : ready s n ->
  (keyed_bucket s tuple < length (memory s arraydef_0__formulaBuckets))%nat.
Proof.
  intros [_ [_ [Hp [Hcap _]]]]. unfold keyed_bucket. destruct tuple as [[x y] z].
  pose proof (Z.mod_pos_bound (siphash24 (meta_value s 26) (meta_value s 27) x y z) _ Hp) as Hbounds.
  pose proof (Z2Nat.id (siphash24 (meta_value s 26) (meta_value s 27) x y z mod meta_value s 20) ltac:(lia)). lia.
Qed.
Lemma scan_stable f g : HashScanExecution.preserves_storage f g -> ScanFrameExecution.preserved f g ->
  stable (machine f) (machine g).
Proof.
  intros [Harray [Hcells [Hin Hout]]] [Hlength _].
  split; [intros; now apply Harray|]. split; [exact Hlength|].
  split; [now rewrite Harray by discriminate|]. split; [intros; now apply Hcells|]. split; assumption.
Qed.
Lemma append_meta_other s n b tuple i : i <> 0%nat -> i <> 1%nat ->
  meta_value (append_state s n b tuple) i = meta_value s i.
Proof.
  intros H0 H1. unfold meta_value. rewrite append_meta. now rewrite !ArrayFacts.nth_insert_other by assumption.
Qed.
Lemma append_key s n b tuple value : keyed_bucket (append_state s n b tuple) value = keyed_bucket s value.
Proof. unfold keyed_bucket. destruct value as [[x y] z]. now rewrite !append_meta_other by lia. Qed.
Lemma append_count s n b tuple : (1 < length (memory s arraydef_0__meta))%nat ->
  meta_value (append_state s n b tuple) 1 = Z.of_nat (S n).
Proof. intro H. unfold meta_value. rewrite append_meta. apply OverflowExecution.nth_insert_same.
  now rewrite length_insert. Qed.
Lemma append_result s n b tuple : (1 < length (memory s arraydef_0__meta))%nat ->
  meta_value (append_state s n b tuple) 0 = Z.of_nat n.
Proof. intro H. unfold meta_value. rewrite append_meta, ArrayFacts.nth_insert_other by lia.
  apply OverflowExecution.nth_insert_same. lia. Qed.
Lemma append_table s n tuple : table s n -> Z.of_nat n < meta_value s 20 ->
  (forall i, (i < n)%nat -> tuple_at s i <> tuple) ->
  table (append_state s n (keyed_bucket s tuple) tuple) (S n).
Proof.
  intros [Hready [Hcount [Hlimit [Hbucket [Hload [Hindexed Hunique]]]]]] Hstrict Hfresh.
  destruct Hready as [Hm [Hs [Hp [Hcap [Hfs [Hls Hn]]]]]].
  split.
  - unfold ready. split; [rewrite append_meta, !length_insert; exact Hm|].
    split; [now rewrite append_other by discriminate|].
    rewrite append_meta_other by lia. split; [exact Hp|].
    split; [rewrite append_bucket_length; exact Hcap|].
    split; [rewrite append_formulas, length_insert, growList_length; lia|].
    split; [rewrite append_links, length_insert, growList_length; lia|lia].
  - split; [apply append_count; lia|]. rewrite append_meta_other by lia.
    split; [exact Hlimit|]. split; [now rewrite append_bucket_length|].
    split; [lia|]. split.
    + apply (indexed_bucket_ext _ _ (keyed_bucket s)); [intro value; symmetry; apply append_key|].
      apply append_indexed; [exact Hindexed|]. apply (bucket_bound _ n). unfold ready. repeat split; assumption.
    + apply append_unique; [exact (proj1 Hindexed)|exact Hunique|exact Hfresh].
Qed.
End InternInvariant.
