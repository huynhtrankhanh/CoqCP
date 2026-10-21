From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import SetTheory.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash InternTail TokenByte HashTable Rehash Rebuild InternInvariant Representation ReplyOK ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module FormulaProjection.
Import IndexExecution SipHashExecution HashTableInvariant RehashExecution RebuildExecution InternInvariant NativeRepresentation ReplyOK ArenaFrame.
Definition needed name := name = arraydef_0__sipState \/ name = arraydef_0__formulas \/
  name = arraydef_0__formulaLinks \/ name = arraydef_0__formulaBuckets.
Definition storage (s t : Machine) :=
  length (memory t arraydef_0__meta) = length (memory s arraydef_0__meta) /\
  (forall name, needed name -> memory t name = memory s name) /\
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
  assert (Hsip : memory t arraydef_0__sipState = memory s arraydef_0__sipState) by (apply Ha; unfold needed; tauto).
  assert (Hformulas : memory t arraydef_0__formulas = memory s arraydef_0__formulas) by (apply Ha; unfold needed; tauto).
  assert (Hlinks : memory t arraydef_0__formulaLinks = memory s arraydef_0__formulaLinks) by (apply Ha; unfold needed; tauto).
  assert (Hbuckets : memory t arraydef_0__formulaBuckets = memory s arraydef_0__formulaBuckets) by (apply Ha; unfold needed; tauto).
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
  assert (Hformula : memory t arraydef_0__formulas = memory s arraydef_0__formulas) by (apply Ha; unfold needed; tauto).
  split; [now apply (storage_table s)|]. split.
  - unfold represents, tuple_at in *. now rewrite Hformula.
  - split; [exact Hunique|]. unfold normal_arena, tuple_at in *. now rewrite Hformula.
Qed.

Lemma strong_storage s t : ArenaFrame.storage s t -> storage s t.
Proof.
  intros [Hm [Ha Hmetadata]]. split; [exact Hm|]. split; [|exact Hmetadata].
  intros name Hname. unfold needed in Hname. destruct Hname as [Heq|[Heq|[Heq|Heq]]]; subst name; apply Ha; discriminate.
Qed.
Lemma reply_storage s value : storage s (ReplyOKExecution.reply_state s value).
Proof.
  split; [now rewrite ReplyOKExecution.reply_other by discriminate|].
  split.
  - intros name Hname. apply ReplyOKExecution.reply_other.
    unfold needed in Hname. destruct Hname as [Heq|[Heq|[Heq|Heq]]]; subst name; discriminate.
  -
  unfold meta_value. rewrite ReplyOKExecution.reply_other by discriminate. repeat split; reflexivity.
Qed.
End FormulaProjection.
