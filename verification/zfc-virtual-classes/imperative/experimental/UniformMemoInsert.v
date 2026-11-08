From CoqCP Require Import Options.
From UniformMemoFixture Require Import UniformMemoChains.
From Stdlib Require Import Arith.PeanoNat Lia.
Module UniformMemoInsert.
Import UniformMemoChains.

Lemma put_old table count e i : (i < count)%nat -> put table count e i = table i.
Proof. intro Hi. unfold put. destruct (Nat.eq_dec i count); [lia|reflexivity]. Qed.

Lemma put_links_bounded table count e :
  links_bounded table count -> (next e <= count)%nat ->
  links_bounded (put table count e) (S count).
Proof.
  intros Hold Hnew i Hi. destruct (Nat.eq_dec i count) as [->|Hne].
  - unfold put. destruct (Nat.eq_dec count count); [lia|contradiction].
  - rewrite put_old by lia. specialize (Hold i ltac:(lia)). lia.
Qed.

Theorem put_preserves_path table count start target steps e :
  links_bounded table count -> (start <= count)%nat -> path table start target steps ->
  path (put table count e) start target steps.
Proof.
  intros Hlinks Hstart Hpath. induction Hpath as [i|i target steps Htail IH] in Hstart |- *.
  - constructor.
  - assert (Hi : (i < count)%nat) by lia.
    rewrite <- (put_old table count e i Hi) in IH.
    apply path_next. apply IH. rewrite put_old by lia. apply Hlinks. exact Hi.
Qed.

Corollary head_insert_preserves_path table count start target steps n d v :
  links_bounded table count -> (start <= count)%nat -> path table start target steps ->
  path (put table count (Entry n d v start)) (S count) target (S steps).
Proof.
  intros Hlinks Hstart Hpath. apply path_next. unfold put.
  destruct (Nat.eq_dec count count); [|contradiction]. cbn.
  eapply put_preserves_path; eassumption.
Qed.

Corollary head_insert_reachable table count start n d v :
  path (put table count (Entry n d v start)) (S count) count 0.
Proof. constructor. Qed.
Definition put_bucket (buckets : nat -> nat) chosen count :=
  fun bucket => if Nat.eq_dec bucket chosen then S count else buckets bucket.

Theorem head_insert_preserves_bucket_paths table buckets count chosen n d v bucket target steps :
  links_bounded table count -> (buckets bucket <= count)%nat ->
  path table (buckets bucket) target steps ->
  exists steps', path (put table count (Entry n d v (buckets chosen)))
    (put_bucket buckets chosen count bucket) target steps'.
Proof.
  intros Hlinks Hbound Hpath. unfold put_bucket.
  destruct (Nat.eq_dec bucket chosen) as [->|Hdifferent].
  - exists (S steps). eapply head_insert_preserves_path; eassumption.
  - exists steps. eapply put_preserves_path; eassumption.
Qed.

Theorem head_insert_bucket_reachable table buckets count chosen n d v :
  path (put table count (Entry n d v (buckets chosen)))
    (put_bucket buckets chosen count chosen) count 0.
Proof. unfold put_bucket. destruct (Nat.eq_dec chosen chosen); [constructor|contradiction]. Qed.
End UniformMemoInsert.
