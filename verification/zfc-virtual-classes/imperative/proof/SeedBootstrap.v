From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From Trusted Require Import SetTheory Protocol.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Intern Observation HashTable InternInvariant Representation Bootstrap SeedInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module SeedBootstrapExecution.
Import SetTheory IndexExecution SipHashExecution HashTableInvariant NativeRepresentation.
Definition initial key0 key1 tail output : Machine :=
  {| memory := arrays _ environment1; stdin := Protocol.seed_bytes key0 key1 ++ tail; stdout := output |}.
Definition prepared key0 key1 tail output :=
  store_meta (SeedInputExecution.seed_result (initial key0 key1 tail output) key0 key1 tail) 20 1024.
Lemma initial_meta key0 key1 tail output :
  (27 < length (memory (initial key0 key1 tail output) arraydef_0__meta))%nat.
Proof. change (27 < 32)%nat. lia. Qed.
Lemma prepared_meta_length key0 key1 tail output :
  length (memory (prepared key0 key1 tail output) arraydef_0__meta) = 32%nat.
Proof. unfold prepared. rewrite store_meta_length, SeedInputExecution.seed_meta_length. reflexivity. Qed.
Lemma prepared_other key0 key1 tail output name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (prepared key0 key1 tail output) name = arrays _ environment1 name.
Proof. intros Hm Ht. unfold prepared. rewrite store_meta_other by exact Hm.
  apply SeedInputExecution.seed_other; assumption. Qed.
Lemma prepared_count key0 key1 tail output : meta_value (prepared key0 key1 tail output) 1 = 0.
Proof.
  unfold prepared. rewrite meta_store_other by lia.
  rewrite SeedInputExecution.seed_meta_other by (try apply initial_meta; lia). reflexivity.
Qed.
Lemma prepared_buckets key0 key1 tail output : meta_value (prepared key0 key1 tail output) 20 = 1024.
Proof. unfold prepared. apply meta_store_same. rewrite SeedInputExecution.seed_meta_length. change (20 < 32)%nat. lia. Qed.
Lemma prepared_no_error key0 key1 tail output : meta_value (prepared key0 key1 tail output) 8 = 0.
Proof.
  unfold prepared. rewrite meta_store_other by lia.
  rewrite SeedInputExecution.seed_meta_other by (try apply initial_meta; lia). reflexivity.
Qed.
Theorem parsed_empty_arena key0 key1 tail output : canonical_arena (prepared key0 key1 tail output) [].
Proof.
  apply BootstrapExecution.empty_arena, BootstrapExecution.empty_table.
  - rewrite prepared_meta_length. lia.
  - rewrite prepared_other by discriminate. change (0 < 1)%nat. lia.
  - apply prepared_count.
  - rewrite prepared_buckets. unfold maximum. lia.
  - rewrite prepared_buckets, prepared_other by discriminate. change (length (repeat 0%Z 1024) = 1024%nat). apply repeat_length.
  - intros b Hb. unfold head_at. rewrite prepared_other by discriminate. apply List.nth_repeat.
Qed.
Definition bootstrap_arguments : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _ => 0) vardef_0__intern_tag 0) vardef_0__intern_a 0) vardef_0__intern_b 0.
Theorem generated_parsed_bootstrap key0 key1 tail output :
  exists final, exec (funcdef_0__intern (fun _ => false) bootstrap_arguments) (prepared key0 key1 tail output) = Some (tt,final) /\
    canonical_arena final [falsity] /\ meta_value final 0 = 0 /\ meta_value final 8 = 0.
Proof.
  apply BootstrapExecution.generated_bootstrap_false_arguments; try reflexivity.
  - apply parsed_empty_arena.
  - apply prepared_no_error.
Qed.

Theorem generated_parsed_bootstrap_observed key0 key1 tail output observations :
  exists final, execObserved (funcdef_0__intern (fun _ => false) bootstrap_arguments)
      (prepared key0 key1 tail output,observations) = Some (tt,(final,observations)) /\
    canonical_arena final [falsity] /\ meta_value final 0 = 0 /\ meta_value final 8 = 0 /\
    stdin final = tail /\ stdout final = output.
Proof.
  destruct (BootstrapExecution.generated_bootstrap_false_framed (prepared key0 key1 tail output)
    (fun _ => false) bootstrap_arguments ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    (parsed_empty_arena key0 key1 tail output) (prepared_no_error key0 key1 tail output))
    as [final [Hrun [[Harrays [Hmeta [Hin Hout]]] [Harena [Hresult Hflag]]]]].
  exists final. split.
  - apply observed_plain; [apply InternalObservation.intern_nf|exact Hrun].
  - split; [exact Harena|]. split; [exact Hresult|]. split; [exact Hflag|]. split.
    + rewrite Hin. reflexivity.
    + rewrite Hout. unfold prepared. change
        (stdout (SeedInputExecution.seed_result (initial key0 key1 tail output) key0 key1 tail) = output).
      rewrite SeedInputExecution.seed_output. reflexivity.
Qed.
End SeedBootstrapExecution.

