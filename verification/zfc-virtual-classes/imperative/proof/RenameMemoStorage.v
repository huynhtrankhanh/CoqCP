From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashTable Rehash Rebuild InternInvariant Representation ArenaFrame
  RenameMemoInvariant HistoryRefinement ClassStorage NameRepresentation RenameFrames.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoStorage.
Import IndexExecution SipHashExecution HashTableInvariant RehashExecution RebuildExecution InternInvariant NativeRepresentation.
Local Opaque siphash24.
Theorem arena_table s t n : RenameMemoInvariant.storage_frame s t -> table s n -> table t n.
Proof.
  intros [Ha [Hm [Hl [Hs [Hi Ho]]]]] [Hready [Hcount [Hword [Hlength [Hload [Hindexed Hunique]]]]]].
  assert (Hformulas : memory t arraydef_0__formulas=memory s arraydef_0__formulas) by (apply Ha; discriminate).
  assert (Hlinks : memory t arraydef_0__formulaLinks=memory s arraydef_0__formulaLinks) by (apply Ha; discriminate).
  assert (Hbuckets : memory t arraydef_0__formulaBuckets=memory s arraydef_0__formulaBuckets) by (apply Ha; discriminate).
  assert (H1 : meta_value t 1=meta_value s 1) by (apply Hm; lia).
  assert (H20 : meta_value t 20=meta_value s 20) by (apply Hm; lia).
  assert (H26 : meta_value t 26=meta_value s 26) by (apply Hm; lia).
  assert (H27 : meta_value t 27=meta_value s 27) by (apply Hm; lia).
  split.
  - unfold ready in *. now rewrite Hl,Hs,H20,Hformulas,Hlinks,Hbuckets.
  - split; [now rewrite H1|]. split; [now rewrite H20|]. split; [now rewrite Hbuckets,H20|]. split; [now rewrite H20|]. split.
    + apply (ArenaFrame.indexed_ext t n (keyed_bucket s)).
      * intros [[x y] z]. unfold keyed_bucket. now rewrite H26,H27,H20.
      * now apply (indexed_preserved s).
    + unfold unique,tuple_at in *. now rewrite Hformulas.
Qed.
Theorem canonical_arena s t meaning : RenameMemoInvariant.storage_frame s t ->
  NativeRepresentation.canonical_arena s meaning -> NativeRepresentation.canonical_arena t meaning.
Proof.
  intros Hstorage [Htable [Hrep [Hunique Hnormal]]]. pose proof Hstorage as [Ha _].
  assert (Hformula : memory t arraydef_0__formulas=memory s arraydef_0__formulas) by (apply Ha; discriminate).
  split; [now apply (arena_table s)|]. split.
  - unfold represents,tuple_at in *. now rewrite Hformula.
  - split; [exact Hunique|]. unfold normal_arena,tuple_at in *. now rewrite Hformula.
Qed.
Theorem history s t logical : RenameMemoInvariant.storage_frame s t ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents t logical.
Proof.
  intros [Ha [Hm _]] [Hcount Hprefix]. unfold HistoryRefinement.represents.
  rewrite Hm by lia. rewrite Ha by discriminate. split; assumption.
Qed.
Theorem classes s t formulas entries : RenameMemoInvariant.storage_frame s t ->
  ClassStorage.represents s formulas entries -> ClassStorage.represents t formulas entries.
Proof.
  intros [Ha [Hm _]] [Hcount Hentries]. unfold ClassStorage.represents.
  rewrite Hm by lia. rewrite Ha by discriminate. split; assumption.
Qed.
Theorem names s t bindings : RenameMemoInvariant.storage_frame s t ->
  NameRepresentation.represents s bindings -> NameRepresentation.represents t bindings.
Proof.
  intros [Ha [Hm _]] Hnames. unfold NameRepresentation.represents in *.
  rewrite !Hm by lia. rewrite !Ha by discriminate. exact Hnames.
Qed.
Theorem popped_frames s t fs task stack : RenameMemoInvariant.storage_frame s t ->
  (10<length (memory s arraydef_0__meta))%nat -> meta_value t 10=Z.of_nat (length stack) ->
  RenameFrames.represents s fs (task::stack) -> RenameFrames.represents t fs stack.
Proof.
  intros [Ha _] Hmeta Hcount Hframes.
  apply RenameFrames.transport with (s:=store_meta s 10 (Z.of_nat (length stack))).
  - rewrite meta_store_same by exact Hmeta. exact Hcount.
  - rewrite store_meta_other by discriminate. apply Ha; discriminate.
  - now apply RenameFrames.pop with (task:=task).
Qed.
End RenameMemoStorage.
