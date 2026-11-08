From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternLoop UniformInternHit.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformInternPrelude.
Import UniformInternLoop UniformInternHit.

(* Continuation selected from the generated code immediately after SipHash. *)
Definition after_hash : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformIntern_body in funcdef_0__uniformIntern_body in
  multimatch code with context [bind ?before ?next] =>
    lazymatch before with context [funcdef_0__formulaHash _ _] =>
      let tail := eval cbn beta in (next tt) in
      lazymatch tail with context [modIntUnsigned _ _] => exact tail end
    end
  end).

Definition scan_start (f : Frame) bucket pointer :=
  setNum (setNum f vardef_0__uniformIntern_bucket (Z.of_nat bucket))
    vardef_0__uniformIntern_current (Z.of_nat pointer).

Definition hash_args (f : Frame) : varsfuncdef_0__formulaHash -> Z :=
  update (update (update (fun _ => 0)
    vardef_0__formulaHash_tag (nums f vardef_0__uniformIntern_tag))
    vardef_0__formulaHash_a (nums f vardef_0__uniformIntern_a))
    vardef_0__formulaHash_b (nums f vardef_0__uniformIntern_b).
Definition initialized (f : Frame) := setNum f vardef_0__uniformIntern_found 0.

Lemma local_get (f : Frame) name :
  execLocal (R := Z) (numberLocalGet _ _ _ name) f = Some (nums f name,f).
Proof. reflexivity. Qed.
Lemma local_set (f : Frame) name value :
  execLocal (R := unit) (numberLocalSet _ _ _ name value) f = Some (tt,setNum f name value).
Proof. reflexivity. Qed.
Lemma get_dispatch {R} (f : Frame) name (next : Z -> LocalAction R) :
  execLocal (Dispatch _ _ _ (NumberLocalGet _ _ _ name) next) f = execLocal (next (nums f name)) f.
Proof. reflexivity. Qed.
Lemma set_dispatch {R} (f : Frame) name value (next : unit -> LocalAction R) :
  execLocal (Dispatch _ _ _ (NumberLocalSet _ _ _ name value) next) f = execLocal (next tt) (setNum f name value).
Proof. reflexivity. Qed.
Lemma update_here {A} (ns : varsfuncdef_0__uniformIntern -> A) name value : Imperative.update ns name value name = value.
Proof. unfold Imperative.update. case_decide; [reflexivity|congruence]. Qed.
Lemma update_other {A} (ns : varsfuncdef_0__uniformIntern -> A) name other value : name <> other -> Imperative.update ns name value other = ns other.
Proof. intro H. unfold Imperative.update. case_decide; [congruence|reflexivity]. Qed.
Lemma read_bucket (f : Frame) bucket :
  (bucket < length (memory (machine f) arraydef_0__uniformBuckets))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__uniformBuckets (Z.of_nat bucket)) f =
    Some (List.nth bucket (memory (machine f) arraydef_0__uniformBuckets) 0,f).
Proof.
  destruct f. intro H. cbn [retrieve execLocal localStep step]. rewrite Nat2Z.id.
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0). reflexivity.
Qed.

Lemma read_meta (f : Frame) :
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__meta 8) f =
    Some (List.nth 8 (memory (machine f) arraydef_0__meta) 0,f).
Proof.
  destruct f. intro H. cbn [retrieve execLocal localStep step].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0). reflexivity.
Qed.

Lemma finish_unit {A} (x : option (unit * A)) :
  optionBind x (fun p => Some (tt,snd p)) = x.
Proof. destruct x as [[[] a]|]; reflexivity. Qed.
Lemma finish_action (x : option (unit * Frame)) :
  optionBind x (fun p => execLocal (Done _ _ _ tt) (snd p)) = x.
Proof. destruct x as [[[] a]|]; reflexivity. Qed.

(* The non-resizing branch through its generated hash call.  The helper's
   successful execution is a premise until the existing SipHash proof is
   transported into this fixture. *)
Theorem hash_prelude (f : Frame) count size hashed :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (count,size) ->
  size <> 0 -> count <> size ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth 8 (memory (machine f) arraydef_0__meta) 0 = 0 ->
  exec (funcdef_0__formulaHash (fun _ => false) (hash_args f)) (machine f) = Some (tt,hashed) ->
  execLocal funcdef_0__uniformIntern_body f =
    execLocal after_hash (setMachine (initialized f) hashed).
Proof.
  intros Hstate Hvalue Hsize Hcount Hmeta Hflag Hhash.
  destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold funcdef_0__uniformIntern_body, after_hash, hash_args, initialized in *.
  cbn [machine nums] in Hhash.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch |rewrite execLocal_lift
    |rewrite read_state by (cbn [machine setNum setMachine]; lia)
    |rewrite read_meta by (cbn [machine setNum setMachine]; lia)
    |rewrite update_here |rewrite update_other by discriminate
    |rewrite Hvalue |rewrite Hflag |rewrite Hhash
    |rewrite bool_decide_false by (cbn [nums setNum]; assumption)
    |rewrite bool_decide_true by (cbn [nums setNum]; reflexivity)
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  repeat rewrite finish_action. repeat rewrite finish_unit.
  reflexivity.
Qed.

Theorem after_hash_to_scan (f : Frame) bucket pointer :
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (retrieve _ _ _ arraydef_0__uniformState 0 >>= fun xy => Done _ _ _ (snd xy))) f =
    Some (Z.of_nat bucket,f) ->
  (bucket < length (memory (machine f) arraydef_0__uniformBuckets))%nat ->
  List.nth bucket (memory (machine f) arraydef_0__uniformBuckets) 0 = Z.of_nat pointer ->
  execLocal after_hash f = execLocal scan_segment (scan_start f bucket pointer).
Proof.
  intros Hmod Hbound Hpointer. destruct f as [s bs ns]. cbn [machine] in *.
  unfold after_hash, scan_start.
  cbn [bind].
  repeat first [setoid_rewrite Hmod |rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch |rewrite update_here
    |rewrite update_other by discriminate
    |rewrite read_bucket by (cbn [machine setNum setMachine]; exact Hbound)
    |rewrite Hpointer |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  setoid_rewrite (read_bucket (setNum {| machine := s; bools := bs; nums := ns |}
    vardef_0__uniformIntern_bucket (Z.of_nat bucket)) bucket ltac:(cbn [machine setNum]; exact Hbound)).
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch |rewrite update_here
    |rewrite update_other by discriminate |rewrite Hpointer
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  unfold scan_segment.
  repeat first [rewrite execLocal_bind |rewrite local_done
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  reflexivity.
Qed.

(* From the generated post-hash continuation through the collision scan and
   hit return.  Hash execution, bucket placement and allocation invariants
   remain explicit hypotheses; this is not a complete interner theorem. *)
Theorem after_hash_hit (f : Frame) count size bucket pointer result :
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (retrieve _ _ _ arraydef_0__uniformState 0 >>= fun xy => Done _ _ _ (snd xy))) f =
    Some (Z.of_nat bucket,f) ->
  (bucket < length (memory (machine f) arraydef_0__uniformBuckets))%nat ->
  List.nth bucket (memory (machine f) arraydef_0__uniformBuckets) 0 = Z.of_nat pointer ->
  let start := scan_start f bucket pointer in
  (0 < length (memory (machine start) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine start) arraydef_0__uniformState) (0,0) = (Z.of_nat count,size) ->
  entries_valid start count -> Z.of_nat count <= maximum ->
  (0 < length (memory (machine start) arraydef_0__meta))%nat ->
  (pointer <= count)%nat -> observed_result start = None ->
  scan_index start count pointer = Some result ->
  exists final, execLocal after_hash f = Some (tt,final) /\ observed_result final = Some result.
Proof.
  intros Hmod Hbucket Hpointer start Hstate Hcount Hvalid Hlimit Hmeta Hbound Hnone Hscan.
  rewrite (after_hash_to_scan f bucket pointer Hmod Hbucket Hpointer).
  change (exists final, execLocal scan_segment start = Some (tt,final) /\ observed_result final = Some result).
  eapply generated_segment_hit; try eassumption.
  unfold start, scan_start. cbn [nums setNum]. apply update_here.
Qed.

(* Full generated interning hit, in the non-resizing branch.  The caller must
   supply successful hash/modulo executions and the hash table's validity;
   this theorem does not assert those premises or cover insertion/rehashing. *)
Theorem nonresizing_hit (f : Frame) count size hashed bucket pointer result :
  (0 < length (memory (machine f) arraydef_0__uniformState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformState) (0,0) = (count,size) ->
  size <> 0 -> count <> size ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth 8 (memory (machine f) arraydef_0__meta) 0 = 0 ->
  exec (funcdef_0__formulaHash (fun _ => false) (hash_args f)) (machine f) = Some (tt,hashed) ->
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
  intros Hstate Hvalue Hsize Hcount Hmeta Hflag Hhash post Hmod Hbucket Hpointer start
         Hpost Hpostvalue Hnat Hvalid Hlimit Hpostmeta Hbound Hnone Hscan.
  rewrite (hash_prelude f count size hashed Hstate Hvalue Hsize Hcount Hmeta Hflag Hhash).
  change (exists final, execLocal after_hash post = Some (tt,final) /\ observed_result final = Some result).
  eapply (after_hash_hit post (Z.to_nat count) size bucket pointer result); try eassumption.
  - now rewrite <- Hnat.
  - now rewrite <- Hnat.
Qed.
End UniformInternPrelude.
Print Assumptions UniformInternPrelude.nonresizing_hit.
