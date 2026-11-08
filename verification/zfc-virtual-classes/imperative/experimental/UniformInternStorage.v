From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternLoop UniformInternPrelude Index Overflow SipHash UniformInternHash.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformInternStorage.
Import UniformInternLoop UniformInternPrelude IndexExecution OverflowExecution SipHashExecution UniformInternHash.

(* Hashing preserves the interner's arrays; these lemmas connect post-hash
   assumptions in the hit proof to initial storage facts. *)
Definition hashed (f : Frame) := hash_state (machine f)
  (nums f vardef_0__uniformIntern_tag) (nums f vardef_0__uniformIntern_a)
  (nums f vardef_0__uniformIntern_b).
Definition post (f : Frame) := setMachine (initialized f) (hashed f).
Definition selected_bucket (f : Frame) size :=
  Z.to_nat (siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27)
    (nums f vardef_0__uniformIntern_tag) (nums f vardef_0__uniformIntern_a)
    (nums f vardef_0__uniformIntern_b) mod size).
Definition selected_pointer (f : Frame) size :=
  Z.to_nat (List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformBuckets) 0).

Lemma post_other f name : name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
  memory (machine (post f)) name = memory (machine f) name.
Proof. intros H1 H2. unfold post, hashed. cbn [machine setMachine]. now apply hash_preserves_array. Qed.
Lemma post_meta_length f :
  length (memory (machine (post f)) arraydef_0__meta) = length (memory (machine f) arraydef_0__meta).
Proof.
  unfold post, hashed. cbn [machine setMachine]. unfold hash_state.
  rewrite !store_meta_length, hash_work_other by discriminate. reflexivity.
Qed.
Lemma start_other f bucket pointer name : name <> arraydef_0__meta -> name <> arraydef_0__sipState ->
  memory (machine (scan_start (post f) bucket pointer)) name = memory (machine f) name.
Proof. intros H1 H2. unfold scan_start. cbn [machine setNum]. now apply post_other. Qed.
Lemma start_entries f bucket pointer count : entries_valid f count ->
  entries_valid (scan_start (post f) bucket pointer) count.
Proof.
  unfold entries_valid. intros [Hnodes [Hlinks Hbounded]].
  repeat rewrite start_other by discriminate. auto.
Qed.
Lemma start_none f bucket pointer : observed_result (scan_start (post f) bucket pointer) = None.
Proof.
  unfold observed_result, scan_start, post, initialized.
  cbn [nums setNum setMachine]. repeat rewrite update_other by discriminate.
  rewrite update_here, bool_decide_false by lia. reflexivity.
Qed.

Lemma start_sought f bucket pointer : sought (scan_start (post f) bucket pointer) = sought f.
Proof.
  unfold sought, scan_start, post, initialized. cbn [nums setNum setMachine].
  repeat rewrite update_other by discriminate. reflexivity.
Qed.
Lemma scan_index_ext f g fuel pointer :
  memory (machine f) arraydef_0__uniformNodes = memory (machine g) arraydef_0__uniformNodes ->
  memory (machine f) arraydef_0__uniformLinks = memory (machine g) arraydef_0__uniformLinks ->
  sought f = sought g -> scan_index f fuel pointer = scan_index g fuel pointer.
Proof.
  intros Hnodes Hlinks Hsought. induction fuel as [|fuel IH] in pointer |- *; [reflexivity|].
  destruct pointer as [|pointer]; [reflexivity|]. cbn [scan_index].
  rewrite Hnodes, Hlinks, Hsought. destruct (bool_decide
    (List.nth pointer (memory (machine g) arraydef_0__uniformNodes) (0,0,0) = sought g));
    [reflexivity|apply IH].
Qed.
Lemma start_scan f bucket pointer fuel idx :
  scan_index (scan_start (post f) bucket pointer) fuel idx = scan_index f fuel idx.
Proof.
  apply scan_index_ext; try apply start_sought; apply start_other; discriminate.
Qed.

(* Complete non-resizing hit starting from the original generated frame.
   This still assumes correct bucket indexing and bounded links; it does not
   cover insertion, resizing, or establishment of the table invariant. *)
Theorem hit_from_initial_storage (f : Frame) count size result :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (Z.of_nat count,size) ->
  0 < size -> Z.of_nat count <> size ->
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth 8 (memory (machine f) arraydef_0__meta) 0 = 0 ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  Z.of_nat (length (memory (machine f) arraydef_0__uniformBuckets)) = size ->
  0 <= List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformBuckets) 0 <= Z.of_nat count ->
  entries_valid f count -> Z.of_nat count <= maximum ->
  scan_index f count (selected_pointer f size) = Some result ->
  exists final, execLocal funcdef_0__uniformIntern_body f = Some (tt,final) /\
    observed_result final = Some result.
Proof.
  intros Hstate Hvalue Hsize Hcount Hmeta Hflag Hsip Hmod Hlength Hpointer Hentries Hlimit Hscan.
  assert (Hbucket : (selected_bucket f size < length (memory (machine f) arraydef_0__uniformBuckets))%nat).
  { unfold selected_bucket. pose proof (Z.mod_pos_bound
      (siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27)
        (nums f vardef_0__uniformIntern_tag) (nums f vardef_0__uniformIntern_a)
        (nums f vardef_0__uniformIntern_b)) size Hsize). apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia. lia. }
  assert (Hpointerval : Z.of_nat (selected_pointer f size) =
    List.nth (selected_bucket f size) (memory (machine f) arraydef_0__uniformBuckets) 0).
  { unfold selected_pointer. apply Z2Nat.id. lia. }
  assert (Hbound : (selected_pointer f size <= count)%nat).
  { apply Nat2Z.inj_le. rewrite Hpointerval. lia. }
  eapply (nonresizing_hit_verified_hash_modulo f (Z.of_nat count) size
    (selected_bucket f size) (selected_pointer f size) result); try eassumption.
  - lia.
  - change (28 < length (memory (machine (post f)) arraydef_0__meta))%nat.
    rewrite post_meta_length. exact Hmeta.
  - unfold selected_bucket. rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). reflexivity.
  - change (selected_bucket f size < length (memory (machine (post f)) arraydef_0__uniformBuckets))%nat.
    rewrite post_other by discriminate. exact Hbucket.
  - change (List.nth (selected_bucket f size) (memory (machine (post f)) arraydef_0__uniformBuckets) 0 = Z.of_nat (selected_pointer f size)).
    rewrite post_other by discriminate. symmetry. exact Hpointerval.
  - rewrite start_other by discriminate. exact Hstate.
  - rewrite start_other by discriminate. exact Hvalue.
  - rewrite Nat2Z.id. reflexivity.
  - apply start_entries. exact Hentries.
  - rewrite start_other by discriminate. lia.
  - apply start_none.
  - rewrite start_scan. exact Hscan.
Qed.

End UniformInternStorage.
