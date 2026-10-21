From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash InternTail HashTable Rehash Rebuild Clear.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module RehashFullExecution.
Import IndexExecution SipHashExecution InternTailExecution HashTableInvariant RehashExecution RebuildExecution ClearExecution.
Definition grow_buckets (s : Machine) size :=
  withMemory s (growArrays (memory s) arraydef_0__formulaBuckets size 0).
Definition prepared (s : Machine) size :=
  store_meta (clear_many (grow_buckets s size) 0 size) 20 (Z.of_nat size).
Definition prepared_frame (f : Frame) size :=
  setMachine (setNum (setNum f vardef_0__rehashFormulas_size (meta_value (machine f) 20))
    vardef_0__rehashFormulas_size (Z.of_nat size)) (prepared (machine f) size).
Lemma grow_other s size name : name <> arraydef_0__formulaBuckets ->
  memory (grow_buckets s size) name = memory s name.
Proof. apply growArrays_other. Qed.
Lemma grow_length s size : length (memory (grow_buckets s size) arraydef_0__formulaBuckets) =
  Nat.max (length (memory s arraydef_0__formulaBuckets)) size.
Proof. unfold grow_buckets. cbn [memory withMemory]. rewrite growArrays_same. apply growList_length. Qed.
Lemma grow_meta s size i : meta_value (grow_buckets s size) i = meta_value s i.
Proof. unfold meta_value. now rewrite grow_other by discriminate. Qed.
Lemma clear_meta s start fuel i : meta_value (clear_many s start fuel) i = meta_value s i.
Proof. unfold meta_value. now rewrite clear_many_other by discriminate. Qed.
Lemma prepared_meta_other s size i : i <> 20%nat -> meta_value (prepared s size) i = meta_value s i.
Proof. intro H. unfold prepared. now rewrite meta_store_other, clear_meta, grow_meta. Qed.
Lemma prepared_meta_size s size : (20 < length (memory s arraydef_0__meta))%nat ->
  meta_value (prepared s size) 20 = Z.of_nat size.
Proof. intro H. unfold prepared. apply meta_store_same.
  rewrite clear_many_other, grow_other by discriminate. exact H. Qed.
Lemma prepared_meta_length s size : length (memory (prepared s size) arraydef_0__meta) =
  length (memory s arraydef_0__meta).
Proof. unfold prepared. rewrite store_meta_length, clear_many_other, grow_other by discriminate. reflexivity. Qed.
Lemma prepared_other s size name : name <> arraydef_0__meta -> name <> arraydef_0__formulaBuckets ->
  memory (prepared s size) name = memory s name.
Proof. intros. unfold prepared. now rewrite store_meta_other, clear_many_other, grow_other by assumption. Qed.
Lemma prepared_bucket_length s size :
  length (memory (prepared s size) arraydef_0__formulaBuckets) =
  Nat.max (length (memory s arraydef_0__formulaBuckets)) size.
Proof. unfold prepared. rewrite store_meta_other by discriminate. rewrite clear_many_length. apply grow_length. Qed.
Lemma prepared_empty s size h : (length (memory s arraydef_0__formulaBuckets) <= size)%nat ->
  indexed (prepared s size) 0 h.
Proof.
  intro Hlength. apply empty_indexed. intros b Hb.
  rewrite prepared_bucket_length in Hb. unfold head_at, prepared.
  rewrite store_meta_other by discriminate. fold (head_at (clear_many (grow_buckets s size) 0 size) b).
  apply clear_many_inside; [rewrite grow_length; lia|lia].
Qed.
Lemma prepared_ready s size count :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat -> (0 < size)%nat ->
  (count <= length (memory s arraydef_0__formulas))%nat ->
  (count <= length (memory s arraydef_0__formulaLinks))%nat -> Z.of_nat count <= maximum ->
  ready (prepared s size) count.
Proof.
  intros Hmeta Hsip Hsize Hformulas Hlinks Hlimit. unfold ready.
  split; [now rewrite prepared_meta_length|].
  split; [now rewrite prepared_other by discriminate|].
  rewrite prepared_meta_size by lia. split; [lia|].
  split; [rewrite prepared_bucket_length; lia|].
  split; [now rewrite prepared_other by discriminate|].
  split; [now rewrite prepared_other by discriminate|exact Hlimit].
Qed.
Lemma local_grow (f : Frame) size :
  execLocal (R := unit) (grow _ _ _ arraydef_0__formulaBuckets (Z.of_nat size) 0) f =
    Some (tt,setMachine f (grow_buckets (machine f) size)).
Proof. cbn [grow execLocal localStep step optionBind fst snd]. rewrite Nat2Z.id. reflexivity. Qed.

Section Preparation.
Variable clear_proc rebuild_proc : Z -> LocalAction unit.
Hypothesis clear_correct : forall f size,
  (size <= length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal (clear_proc (Z.of_nat size)) f = Some (tt,setMachine f (clear_many (machine f) 0 size)).

Theorem preparation_composition (f : Frame) size count :
  (20 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 20 = Z.of_nat size ->
  meta_value (machine f) 1 = Z.of_nat count ->
  Z.of_nat size <= 9223372036854775807 ->
  execLocal (body_with clear_proc rebuild_proc) f =
    optionBind (execLocal (rebuild_proc (Z.of_nat count)) (prepared_frame f (2*size)))
      (fun response => Some (tt,snd response)).
Proof.
  intros Hmeta Hsize Hcount Hlimit. destruct f as [s bs ns]. cbn [machine] in *.
  unfold body_with, multInt.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch |rewrite update_here
    |rewrite local_read_meta by
        (cbn [machine setMachine setNum];
         repeat first [rewrite grow_other by discriminate |rewrite clear_many_other by discriminate
           |rewrite store_meta_length]; lia)
    |rewrite local_put_meta by
        (cbn [machine setMachine setNum];
         repeat first [rewrite grow_other by discriminate |rewrite clear_many_other by discriminate]; lia)
    |rewrite local_grow
    |rewrite clear_correct by (cbn [machine setMachine setNum]; rewrite grow_length; lia)
    |rewrite grow_meta |rewrite clear_meta |rewrite meta_store_other by lia
    |rewrite Hsize |rewrite Hcount
    |progress replace (Z.to_nat 20) with 20%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.of_nat size * 2) with (Z.of_nat (2*size)) by lia
    |rewrite bool_decide_false by lia
    |match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum in *; lia) end
    |progress cbn [bind optionBind nums bools machine setNum setMachine fst snd multInt
        Imperative.update variableIndexEqualityDecidablevarsfuncdef_0__rehashFormulas
        varsfuncdef_0__rehashFormulas_rec]
  ].
  unfold prepared_frame, prepared. cbn [machine]. rewrite Hsize.
  cbv beta iota zeta delta [machine setMachine setNum bools nums].
  lazymatch goal with |- context [execLocal (rebuild_proc (Z.of_nat count)) ?f] =>
    destruct (execLocal (rebuild_proc (Z.of_nat count)) f) as [[[] final]|]; reflexivity
  end.
Qed.
End Preparation.
Lemma clearing_correct f size :
  (size <= length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal (clearing (Z.of_nat size)) f = Some (tt,setMachine f (clear_many (machine f) 0 size)).
Proof. intro H. rewrite clearing_is_loop, Nat2Z.id. now apply generated_clear_loop. Qed.

Definition rehashed (s t : Machine) size count :=
  ready t count /\ indexed t count (keyed_bucket t) /\
  length (memory t arraydef_0__formulaBuckets) = (2*size)%nat /\
  meta_value t 20 = Z.of_nat (2*size) /\
  (forall i, i <> 20%nat -> i <> 21%nat -> i <> 28%nat -> meta_value t i = meta_value s i) /\
  (forall name, name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
    name <> arraydef_0__formulaLinks -> name <> arraydef_0__formulaBuckets -> memory t name = memory s name) /\
  stdin t = stdin s /\ stdout t = stdout s.
Lemma prepared_io s size : stdin (prepared s size) = stdin s /\ stdout (prepared s size) = stdout s.
Proof. unfold prepared. change (stdin (clear_many (grow_buckets s size) 0 size) = stdin s /\
  stdout (clear_many (grow_buckets s size) 0 size) = stdout s).
  exact (clear_many_io (grow_buckets s size) 0 size). Qed.

Theorem generated_rehash_small s bs ns size count :
  (28 < length (memory s arraydef_0__meta))%nat ->
  (0 < length (memory s arraydef_0__sipState))%nat ->
  meta_value s 20 = Z.of_nat size -> (0 < size)%nat ->
  (length (memory s arraydef_0__formulaBuckets) <= 2*size)%nat ->
  meta_value s 1 = Z.of_nat count -> Z.of_nat size <= 9223372036854775807 ->
  (count <= length (memory s arraydef_0__formulas))%nat ->
  (count <= length (memory s arraydef_0__formulaLinks))%nat -> Z.of_nat count <= maximum ->
  exists final, exec (funcdef_0__rehashFormulas bs ns) s = Some (tt,final) /\ rehashed s final size count.
Proof.
  intros Hmeta Hsip Hsize Hpositive Hbucketlength Hcount Hlimit Hformulas Hlinks Hcountlimit.
  unfold funcdef_0__rehashFormulas. rewrite exec_eliminate, actual_body.
  rewrite (preparation_composition clearing rebuilding clearing_correct _ size count) by (cbn [machine]; try assumption; lia).
  rewrite rebuilding_is_loop, Nat2Z.id.
  set (f := prepared_frame {| machine := s; bools := bs; nums := ns |} (2*size)).
  assert (Hready0 : ready (machine f) count) by (apply prepared_ready; try assumption; lia).
  assert (Hempty : indexed (machine f) 0 (keyed_bucket (machine f))) by (apply prepared_empty; exact Hbucketlength).
  destruct (generated_rebuild_loop count f count 0 (keyed_bucket (machine f)) ltac:(lia) Hready0 Hempty ltac:(reflexivity))
    as [last [Hrun [Hready [Hindexed [Hkey Hformula]]]]].
  pose proof (generated_rebuild_preserved count f count 0 last ltac:(lia) Hready0 Hrun)
    as [Harrays [Hcells [Hin Hout]]].
  pose proof (generated_rebuild_lengths count f count 0 last ltac:(lia) Hready0 Hrun) as Hlengths.
  rewrite Hrun. cbn [optionBind fst snd]. exists (machine last). split; [reflexivity|].
  split; [exact Hready|]. split; [now apply (indexed_bucket_ext _ _ _ _ Hkey)|].
  split.
  - rewrite Hlengths. change (length (memory (prepared s (2*size)) arraydef_0__formulaBuckets) = (2*size)%nat).
    rewrite prepared_bucket_length. lia.
  - split.
    + rewrite Hcells by lia. exact (prepared_meta_size s (2*size) ltac:(lia)).
    + split.
      * intros i H20 H21 H28. rewrite Hcells by assumption. now apply prepared_meta_other.
      * split.
        -- intros name Hm Hs Hl Hb. rewrite Harrays by assumption. now apply prepared_other.
        -- destruct (prepared_io s (2*size)) as [Hin0 Hout0]. split; [now rewrite Hin|now rewrite Hout].
Qed.

Theorem generated_rehash_full s bs ns :
  (20 < length (memory s arraydef_0__meta))%nat ->
  9223372036854775807 < meta_value s 20 ->
  exec (funcdef_0__rehashFormulas bs ns) s = Some (tt,store_meta s 8 1).
Proof.
  intros Hmeta Hlimit. unfold funcdef_0__rehashFormulas. rewrite exec_eliminate.
  unfold funcdef_0__rehashFormulas_body.
  repeat first [rewrite execLocal_bind |rewrite local_read_meta by (cbn [machine setMachine setNum]; lia)
    |rewrite local_put_meta by (cbn [machine setMachine setNum]; lia)
    |rewrite local_get |rewrite local_set |rewrite local_done |rewrite get_dispatch |rewrite set_dispatch
    |rewrite update_here
    |progress replace (Z.to_nat 20) with 20%nat by reflexivity
    |rewrite bool_decide_true by lia
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  reflexivity.
Qed.

Theorem generated_checked_rehash s bs ns size count :
  ready s count -> meta_value s 20 = Z.of_nat size ->
  (length (memory s arraydef_0__formulaBuckets) <= 2*size)%nat ->
  meta_value s 1 = Z.of_nat count ->
  exists final, exec (funcdef_0__rehashFormulas bs ns) s = Some (tt,final) /\
    (meta_value final 8 = 0 -> rehashed s final size count) /\
    (9223372036854775807 < Z.of_nat size -> final = store_meta s 8 1).
Proof.
  intros Hready Hsize Hbucket Hcount.
  destruct Hready as [Hmeta [Hsip [Hpositive [Hcapacity [Hformulas [Hlinks Hcountlimit]]]]]].
  destruct (Z_le_dec (Z.of_nat size) 9223372036854775807) as [Hlimit|Hfull].
  - destruct (generated_rehash_small s bs ns size count Hmeta Hsip Hsize ltac:(lia) Hbucket Hcount
      Hlimit Hformulas Hlinks Hcountlimit) as [final [Hrun Hpost]].
    exists final. split; [exact Hrun|]. split; [intros; exact Hpost|lia].
  - exists (store_meta s 8 1). split.
    + apply generated_rehash_full; [lia|lia].
    + split; [|reflexivity]. rewrite meta_store_same by lia. discriminate.
Qed.
End RehashFullExecution.
