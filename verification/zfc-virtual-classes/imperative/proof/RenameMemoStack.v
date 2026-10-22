From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Stack FrameReplace RenameMemoTable RenameMemoLookup RenameMemoInvariant.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoStack.
Import IndexExecution SipHashExecution.
Local Opaque hash_state siphash24.
Definition stack_frame s t :=
  (forall name, name<>arraydef_0__meta -> name<>arraydef_0__frames -> memory t name=memory s name) /\
  (forall cell, cell<>10%nat -> meta_value t cell=meta_value s cell) /\
  length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta) /\
  stdin t=stdin s /\ stdout t=stdout s.
Theorem transport s t count meaning : stack_frame s t -> RenameMemoInvariant.valid s count meaning ->
  RenameMemoInvariant.valid t count meaning.
Proof.
  intros [Ha [Hm [Hl [Hi Ho]]]] [Hmeta Hsip Hpositive Herror Hcapacity Hminimum Hword Hallocated Hlive Hload Hmeaning Hindexed].
  assert (Htable : RenameMemoLookup.table t=RenameMemoLookup.table s).
  { unfold RenameMemoLookup.table. now rewrite Ha by discriminate. }
  assert (Hhash : forall query, RenameMemoLookup.hash_start t query count=RenameMemoLookup.hash_start s query count).
  { intro query. unfold RenameMemoLookup.hash_start. now rewrite !Hm by lia. }
  constructor.
  - now rewrite Hl.
  - now rewrite Ha by discriminate.
  - now rewrite Hm by lia.
  - now rewrite Hm by lia.
  - now rewrite Hm by lia.
  - exact Hminimum.
  - exact Hword.
  - now rewrite Ha by discriminate.
  - now rewrite Hm,Htable by lia.
  - now rewrite Hm by lia.
  - now rewrite Htable.
  - intros index Hindex Hoccupied. rewrite Htable in Hoccupied |- *. rewrite Hhash. now apply Hindexed.
Qed.
Lemma write_frame s slot raw : stack_frame s (FrameReplace.write s slot raw).
Proof.
  split; [intros; now apply FrameReplace.write_other|]. split; [intros; apply FrameReplace.write_meta|].
  split; [now rewrite FrameReplace.write_other by discriminate|]. split; reflexivity.
Qed.
Lemma push_frame s count node depth : stack_frame s (StackExecution.push_state s count node depth).
Proof.
  split; [intros; now apply FrameReplace.push_other|]. split; [intros; now apply FrameReplace.push_meta_other|].
  split; [apply FrameReplace.push_meta_length|]. split; reflexivity.
Qed.
Theorem write_valid s slot raw count meaning : RenameMemoInvariant.valid s count meaning ->
  RenameMemoInvariant.valid (FrameReplace.write s slot raw) count meaning.
Proof. intro Hvalid. apply transport with (s:=s); [apply write_frame|exact Hvalid]. Qed.
Theorem push_valid s top node depth count meaning : RenameMemoInvariant.valid s count meaning ->
  RenameMemoInvariant.valid (StackExecution.push_state s top node depth) count meaning.
Proof. intro Hvalid. apply transport with (s:=s); [apply push_frame|exact Hvalid]. Qed.
End RenameMemoStack.
