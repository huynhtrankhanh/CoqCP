From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternLoop UniformInternHit UniformInternPrelude SipHash.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformInternHash.
Import UniformInternLoop UniformInternHit UniformInternPrelude SipHashExecution.

(* This discharges only the helper-execution premise of the interner hit
   theorem.  The generated IIL source and SipHash proof use the same actual
   formulaHash helper in this extended array environment. *)
Theorem hash_helper_exec (f : Frame) :
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  exec (funcdef_0__formulaHash (fun _ => false) (hash_args f)) (machine f) =
    Some (tt, hash_state (machine f) (nums f vardef_0__uniformIntern_tag)
      (nums f vardef_0__uniformIntern_a) (nums f vardef_0__uniformIntern_b)).
Proof.
  intros Hmeta Hsip Hsize. rewrite generated_hash by assumption.
  unfold hash_args, Imperative.update. cbn. reflexivity.
Qed.

Lemma read_meta28 (f : Frame) :
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__meta 28) f =
    Some (meta_value (machine f) 28,f).
Proof.
  destruct f. intro H. cbn [retrieve execLocal localStep step meta_value].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0). reflexivity.
Qed.

Lemma modulo_exec (f : Frame) count size :
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (count,size) ->
  size <> 0 ->
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (retrieve _ _ _ arraydef_0__uniformState 0 >>= fun xy => Done _ _ _ (snd xy))) f =
  Some (meta_value (machine f) 28 mod size,f).
Proof.
  intros Hmeta Hstate Hvalue Hsize. unfold modIntUnsigned.
  repeat rewrite execLocal_bind.
  rewrite read_meta28 by exact Hmeta. cbn [optionBind fst snd].
  repeat rewrite execLocal_bind. rewrite read_state by exact Hstate.
  cbn [optionBind fst snd]. rewrite Hvalue. cbn [fst snd].
  rewrite local_done. cbn [optionBind fst snd].
  case_decide; [contradiction|]. reflexivity.
Qed.

Theorem nonresizing_hit_verified_hash (f : Frame) count size bucket pointer result :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (count,size) ->
  size <> 0 -> count <> size ->
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth 8 (memory (machine f) arraydef_0__meta) 0 = 0 ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  let hashed := hash_state (machine f) (nums f vardef_0__uniformIntern_tag)
    (nums f vardef_0__uniformIntern_a) (nums f vardef_0__uniformIntern_b) in
  let post := setMachine (initialized f) hashed in
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (retrieve _ _ _ arraydef_0__uniformState 0 >>= fun xy => Done _ _ _ (snd xy))) post =
    Some (Z.of_nat bucket,post) ->
  (bucket < length (memory (machine post) arraydef_0__uniformBuckets))%nat ->
  List.nth bucket (memory (machine post) arraydef_0__uniformBuckets) 0 = Z.of_nat pointer ->
  let start := scan_start post bucket pointer in
  (0 < length (memory (machine start) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine start) arraydef_0__uniformState) (0,0) = (count,size) ->
  count = Z.of_nat (Z.to_nat count) ->
  entries_valid start (Z.to_nat count) -> count <= maximum ->
  (0 < length (memory (machine start) arraydef_0__meta))%nat ->
  (pointer <= Z.to_nat count)%nat -> observed_result start = None ->
  scan_index start (Z.to_nat count) pointer = Some result ->
  exists final, execLocal funcdef_0__uniformIntern_body f = Some (tt,final) /\
    observed_result final = Some result.
Proof.
  intros Hstate Hvalue Hsize Hcount Hmeta Hflag Hsip Hmodulus hashed post Hmod
    Hbucket Hpointer start Hpost Hpostvalue Hnat Hvalid Hlimit Hpostmeta Hbound Hnone Hscan.
  eapply nonresizing_hit; try eassumption; [lia|].
  now apply hash_helper_exec.
Qed.

Theorem nonresizing_hit_verified_hash_modulo (f : Frame) count size bucket pointer result :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (count,size) ->
  size <> 0 -> count <> size ->
  (28 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth 8 (memory (machine f) arraydef_0__meta) 0 = 0 ->
  (0 < length (memory (machine f) arraydef_0__sipState))%nat ->
  0 < meta_value (machine f) 20 ->
  let hashed := hash_state (machine f) (nums f vardef_0__uniformIntern_tag)
    (nums f vardef_0__uniformIntern_a) (nums f vardef_0__uniformIntern_b) in
  let post := setMachine (initialized f) hashed in
  (28 < length (memory (machine post) arraydef_0__meta))%nat ->
  (0 < length (memory (machine post) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine post) arraydef_0__uniformState) (0,0) = (count,size) ->
  siphash24 (meta_value (machine f) 26) (meta_value (machine f) 27)
    (nums f vardef_0__uniformIntern_tag) (nums f vardef_0__uniformIntern_a)
    (nums f vardef_0__uniformIntern_b) mod size = Z.of_nat bucket ->
  (bucket < length (memory (machine post) arraydef_0__uniformBuckets))%nat ->
  List.nth bucket (memory (machine post) arraydef_0__uniformBuckets) 0 = Z.of_nat pointer ->
  let start := scan_start post bucket pointer in
  (0 < length (memory (machine start) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine start) arraydef_0__uniformState) (0,0) = (count,size) ->
  count = Z.of_nat (Z.to_nat count) ->
  entries_valid start (Z.to_nat count) -> count <= maximum ->
  (0 < length (memory (machine start) arraydef_0__meta))%nat ->
  (pointer <= Z.to_nat count)%nat -> observed_result start = None ->
  scan_index start (Z.to_nat count) pointer = Some result ->
  exists final, execLocal funcdef_0__uniformIntern_body f = Some (tt,final) /\
    observed_result final = Some result.
Proof.
  intros Hstate Hvalue Hsize Hcount Hmeta Hflag Hsip Hmodulus hashed post
    Hpostmeta Hpoststate Hpostvalue Hbucketvalue Hbucket Hpointer start
    Hpost Hstartvalue Hnat Hvalid Hlimit Hpostmeta' Hbound Hnone Hscan.
  eapply nonresizing_hit_verified_hash; try eassumption.
  pose proof (modulo_exec post count size Hpostmeta Hpoststate Hpostvalue Hsize) as Hmod.
  change (execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (retrieve _ _ _ arraydef_0__uniformState 0 >>= fun xy => Done _ _ _ (snd xy))) post =
    Some (meta_value hashed 28 mod size,post)) in Hmod.
  unfold hashed in Hmod. rewrite hash_result in Hmod by assumption.
  now rewrite Hbucketvalue in Hmod.
Qed.
End UniformInternHash.
Print Assumptions UniformInternHash.nonresizing_hit_verified_hash_modulo.
