From CoqCP Require Import Options Imperative Execution.
From UniformMemoFixture Require Import UniformMemoProgram UniformMemoLoop UniformMemoPrelude SipHash.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformMemoHash.
Import UniformMemoLoop UniformMemoPrelude SipHashExecution.

Lemma post_size (f : Frame) count size hashed :
  nums (setMachine (reset_frame f count size) hashed) vardef_0__uniformMemoGet_size = size.
Proof. unfold reset_frame. cbn [setMachine nums setNum]. apply update_here. Qed.

Lemma modulo_exec (f : Frame) size :
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__uniformMemoGet_size = size -> size <> 0 ->
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (numberLocalGet _ _ _ vardef_0__uniformMemoGet_size)) f =
  Some (meta_value (machine f) 28 mod size,f).
Proof.
  intros Hmeta Hsize Hnonzero. unfold modIntUnsigned.
  repeat rewrite execLocal_bind.
  rewrite local_read_meta by (cbn; exact Hmeta). cbn [optionBind].
  cbn [fst snd]. rewrite execLocal_bind, local_get. cbn [optionBind fst snd]. rewrite Hsize.
  case_decide; [contradiction|]. reflexivity.
Qed.

(* The prelude's helper-execution premise follows from the existing verified
   SipHash implementation in the extended experimental array environment. *)
Theorem hash_helper_exec (f : Frame) count size :
  (28 < length (memory (reset_machine f count size) arraydef_0__meta))%nat ->
  (0 < length (memory (reset_machine f count size) arraydef_0__sipState))%nat ->
  0 < meta_value (reset_machine f count size) 20 ->
  exec (funcdef_0__formulaHash (fun _ => false) (hash_args f)) (reset_machine f count size) =
    Some (tt, hash_state (reset_machine f count size) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth)).
Proof.
  intros Hmeta Hsip Hsize. rewrite generated_hash by assumption.
  unfold hash_args, Imperative.update. cbn.
  reflexivity.
Qed.

Theorem hash_helper_digest (f : Frame) count size :
  (28 < length (memory (reset_machine f count size) arraydef_0__meta))%nat ->
  (0 < length (memory (reset_machine f count size) arraydef_0__sipState))%nat ->
  0 < meta_value (reset_machine f count size) 20 ->
  let s := reset_machine f count size in
  let hashed := hash_state s 51 (nums f vardef_0__uniformMemoGet_node)
    (nums f vardef_0__uniformMemoGet_depth) in
  exec (funcdef_0__formulaHash (fun _ => false) (hash_args f)) s = Some (tt,hashed) /\
  meta_value hashed 28 = siphash24 (meta_value s 26) (meta_value s 27) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth).
Proof.
  intros Hmeta Hsip Hsize s hashed. split.
  - now apply hash_helper_exec.
  - now apply hash_result.
Qed.

Theorem verified_hash_modulo (f : Frame) count size :
  (28 < length (memory (reset_machine f count size) arraydef_0__meta))%nat ->
  (0 < length (memory (reset_machine f count size) arraydef_0__sipState))%nat ->
  size <> 0 ->
  let s := reset_machine f count size in
  let hashed := hash_state s 51 (nums f vardef_0__uniformMemoGet_node)
    (nums f vardef_0__uniformMemoGet_depth) in
  let post := setMachine (reset_frame f count size) hashed in
  (28 < length (memory (machine post) arraydef_0__meta))%nat ->
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (numberLocalGet _ _ _ vardef_0__uniformMemoGet_size)) post =
  Some (siphash24 (meta_value s 26) (meta_value s 27) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) mod size,post).
Proof.
  intros Hmeta Hsip Hsize s hashed post Hpost.
  rewrite (modulo_exec post size Hpost (post_size f count size hashed) Hsize).
  change (Some (meta_value hashed 28 mod size,post) =
    Some (siphash24 (meta_value s 26) (meta_value s 27) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) mod size,post)).
  unfold hashed. now rewrite hash_result by assumption.
Qed.

(* Full lookup refinement without a hash-termination premise. The bucket
   selection and post-hash array/word facts remain explicit hypotheses. *)
Theorem lookup_with_verified_hash (f : Frame) count size oldfound oldvalue bucket pointer found value :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,oldfound,oldvalue) ->
  size <> 0 ->
  (28 < length (memory (reset_machine f (Z.of_nat count) size) arraydef_0__meta))%nat ->
  (0 < length (memory (reset_machine f (Z.of_nat count) size) arraydef_0__sipState))%nat ->
  0 < meta_value (reset_machine f (Z.of_nat count) size) 20 ->
  let hashed := hash_state (reset_machine f (Z.of_nat count) size) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) in
  let post := setMachine (reset_frame f (Z.of_nat count) size) hashed in
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (numberLocalGet _ _ _ vardef_0__uniformMemoGet_size)) post = Some (Z.of_nat bucket,post) ->
  (bucket < length (memory (machine post) arraydef_0__uniformMemoBuckets))%nat ->
  List.nth bucket (memory (machine post) arraydef_0__uniformMemoBuckets) 0 = Z.of_nat pointer ->
  (0 < length (memory (machine post) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine post) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,found,value) ->
  let start := scan_start post bucket pointer in
  entries_valid start count -> Z.of_nat count <= maximum -> (pointer <= count)%nat ->
  observed_result start = None ->
  exists final, execLocal funcdef_0__uniformMemoGet_body f = Some (tt,final) /\
    observed_result final = scan_values start count pointer.
Proof.
  intros Hstate Hvalue Hsize Hmeta Hsip Hmodulus hashed post Hmod Hbucket Hpointer
    Hpost Hcount start Hvalid Hlimit Hbound Hnone.
  eapply lookup_refines_scan; try eassumption.
  apply hash_helper_exec; assumption.
Qed.

Theorem lookup_with_verified_hash_and_modulo (f : Frame) count size oldfound oldvalue bucket pointer found value :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,oldfound,oldvalue) ->
  size <> 0 ->
  (28 < length (memory (reset_machine f (Z.of_nat count) size) arraydef_0__meta))%nat ->
  (0 < length (memory (reset_machine f (Z.of_nat count) size) arraydef_0__sipState))%nat ->
  0 < meta_value (reset_machine f (Z.of_nat count) size) 20 ->
  let s := reset_machine f (Z.of_nat count) size in
  let hashed := hash_state s 51 (nums f vardef_0__uniformMemoGet_node)
    (nums f vardef_0__uniformMemoGet_depth) in
  let post := setMachine (reset_frame f (Z.of_nat count) size) hashed in
  (28 < length (memory (machine post) arraydef_0__meta))%nat ->
  siphash24 (meta_value s 26) (meta_value s 27) 51
    (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) mod size = Z.of_nat bucket ->
  (bucket < length (memory (machine post) arraydef_0__uniformMemoBuckets))%nat ->
  List.nth bucket (memory (machine post) arraydef_0__uniformMemoBuckets) 0 = Z.of_nat pointer ->
  (0 < length (memory (machine post) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine post) arraydef_0__uniformMemoState) (0,0,0,0) =
    (Z.of_nat count,size,found,value) ->
  let start := scan_start post bucket pointer in
  entries_valid start count -> Z.of_nat count <= maximum -> (pointer <= count)%nat ->
  observed_result start = None ->
  exists final, execLocal funcdef_0__uniformMemoGet_body f = Some (tt,final) /\
    observed_result final = scan_values start count pointer.
Proof.
  intros Hstate Hvalue Hsize Hmeta Hsip Hmodulus s hashed post Hpostmeta Hbucketvalue
    Hbucket Hpointer Hpost Hcount start Hvalid Hlimit Hbound Hnone.
  eapply lookup_with_verified_hash; try eassumption.
  pose proof (verified_hash_modulo f (Z.of_nat count) size Hmeta Hsip Hsize Hpostmeta) as Hmod.
  change (execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (numberLocalGet _ _ _ vardef_0__uniformMemoGet_size)) post =
    Some (siphash24 (meta_value s 26) (meta_value s 27) 51
      (nums f vardef_0__uniformMemoGet_node) (nums f vardef_0__uniformMemoGet_depth) mod size,post)) in Hmod.
  now rewrite Hbucketvalue in Hmod.
Qed.
End UniformMemoHash.
