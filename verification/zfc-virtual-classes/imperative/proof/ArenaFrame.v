From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash InternTail TokenByte HashTable Rehash Rebuild InternInvariant Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ArenaFrame.
Import IndexExecution SipHashExecution HashTableInvariant RehashExecution RebuildExecution InternInvariant NativeRepresentation.
Definition storage (s t : Machine) :=
  length (memory t arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__token -> memory t name = memory s name) /\
  meta_value t 1 = meta_value s 1 /\ meta_value t 20 = meta_value s 20 /\
  meta_value t 26 = meta_value s 26 /\ meta_value t 27 = meta_value s 27.
Lemma storage_refl s : storage s s.
Proof. repeat split; reflexivity. Qed.
Lemma storage_trans s t u : storage s t -> storage t u -> storage s u.
Proof.
  intros [Hm [Ha [H1 [H20 [H26 H27]]]]] [Hm' [Ha' [H1' [H20' [H26' H27']]]]].
  split; [congruence|]. split; [intros; now rewrite Ha', Ha by assumption|]. repeat split; congruence.
Qed.
Lemma indexed_ext s n a b : (forall tuple, a tuple = b tuple) -> indexed s n a -> indexed s n b.
Proof. intros Hab [Htable [Hhead Hentries]]. split; [exact Htable|]. split; [exact Hhead|].
  intros i Hi. specialize (Hentries i Hi). now rewrite Hab in Hentries. Qed.
Theorem storage_table s t n : storage s t -> table s n -> table t n.
Proof.
  intros [Hm [Ha [H1 [H20 [H26 H27]]]]] [Hready [Hcount [Hword [Hlength [Hload [Hindexed Hunique]]]]]].
  assert (Hsip : memory t arraydef_0__sipState = memory s arraydef_0__sipState) by (apply Ha; discriminate).
  assert (Hformulas : memory t arraydef_0__formulas = memory s arraydef_0__formulas) by (apply Ha; discriminate).
  assert (Hlinks : memory t arraydef_0__formulaLinks = memory s arraydef_0__formulaLinks) by (apply Ha; discriminate).
  assert (Hbuckets : memory t arraydef_0__formulaBuckets = memory s arraydef_0__formulaBuckets) by (apply Ha; discriminate).
  split.
  - unfold ready in *. now rewrite Hm, Hsip, H20, Hformulas, Hlinks, Hbuckets.
  - split; [now rewrite H1|]. split; [now rewrite H20|]. split; [now rewrite Hbuckets, H20|]. split; [now rewrite H20|]. split.
    + apply (indexed_ext t n (keyed_bucket s)).
      * intros [[x y] z]. unfold keyed_bucket. now rewrite H26, H27, H20.
      * now apply (indexed_preserved s).
    + unfold unique, tuple_at in *. now rewrite Hformulas.
Qed.
Theorem storage_arena s t meaning : storage s t -> canonical_arena s meaning -> canonical_arena t meaning.
Proof.
  intros Hstorage [Htable [Hrep [Hunique Hnormal]]]. pose proof Hstorage as [_ [Ha _]].
  assert (Hformula : memory t arraydef_0__formulas = memory s arraydef_0__formulas) by (apply Ha; discriminate).
  split; [now apply (storage_table s)|]. split.
  - unfold represents, tuple_at in *. now rewrite Hformula.
  - split; [exact Hunique|]. unfold normal_arena, tuple_at in *. now rewrite Hformula.
Qed.

Lemma storage_meta s slot value : slot <> 1%nat -> slot <> 20%nat -> slot <> 26%nat -> slot <> 27%nat ->
  storage s (store_meta s slot value).
Proof.
  intros H1 H20 H26 H27. split; [apply store_meta_length|]. split.
  - intros name Hm Ht. now apply store_meta_other.
  - repeat split; apply meta_store_other; congruence.
Qed.
Lemma storage_input s input : storage s (withInput s input).
Proof. repeat split; reflexivity. Qed.
Lemma storage_output s output : storage s (withOutput s output).
Proof. repeat split; reflexivity. Qed.
Lemma storage_token s size ch : storage s (TokenByteExecution.put_byte s size ch).
Proof.
  unfold TokenByteExecution.put_byte.
  apply (storage_trans s (withMemory s (modifyArray (memory s) arraydef_0__token size ch))).
  - split.
    + cbn [withMemory memory]. now rewrite InternTailExecution.modify_other by discriminate.
    + split.
      * intros name Hm Ht. cbn [withMemory memory]. now apply InternTailExecution.modify_other.
      * unfold meta_value. cbn [withMemory memory]. rewrite InternTailExecution.modify_other by discriminate. repeat split; reflexivity.
  - apply storage_meta; lia.
Qed.
Ltac storage_steps :=
  first [apply storage_refl
  |lazymatch goal with |- storage ?s (store_meta ?t ?slot ?value) =>
    apply (storage_trans s t (store_meta t slot value)); [storage_steps|apply storage_meta; lia] end
  |lazymatch goal with |- storage ?s (withInput ?t ?input) =>
    apply (storage_trans s t (withInput t input)); [storage_steps|apply storage_input] end
  |lazymatch goal with |- storage ?s (withOutput ?t ?output) =>
    apply (storage_trans s t (withOutput t output)); [storage_steps|apply storage_output] end
  |lazymatch goal with |- storage ?s (TokenByteExecution.put_byte ?t ?size ?ch) =>
    apply (storage_trans s t (TokenByteExecution.put_byte t size ch)); [storage_steps|apply storage_token] end].
End ArenaFrame.

