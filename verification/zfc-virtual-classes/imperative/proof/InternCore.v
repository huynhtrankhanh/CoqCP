From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash HashScan InternTail Rehash RehashFull.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module InternCoreExecution.
Import IndexExecution SipHashExecution HashScanExecution InternTailExecution.
Definition resize_function := (varsfuncdef_0__rehashFormulas -> bool) ->
  (varsfuncdef_0__rehashFormulas -> Z) -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition hash_function := RehashExecution.hash_function.
Definition body_with (resize : resize_function) (hash : hash_function) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__intern_body in funcdef_0__intern_body in
  let generalized := eval pattern funcdef_0__rehashFormulas,funcdef_0__formulaHash in code in
  lazymatch generalized with ?family _ _ => exact (family resize hash) end).
Definition after_resize (hash : hash_function) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__intern_body in funcdef_0__intern_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      let generalized := eval pattern funcdef_0__formulaHash in code in
      lazymatch generalized with ?family _ => exact (family hash) end
    end
  end).
Definition after_hash : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__intern_body in funcdef_0__intern_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind (bind _ ?branch) _ =>
        let code := eval cbn beta iota in (branch true) in
        lazymatch code with bind _ ?next => exact (next tt) end
      end
    end
  end).
Definition scan_callback (total : Z) : LocalAction unit := loop (Z.to_nat total) scan_body.
Definition after_hash_with (scan : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold after_hash in after_hash in
  let code := eval cbn beta in code in
  lazymatch code with bind _ ?next =>
    let tail := eval cbn beta in (next tt) in
    lazymatch tail with bind _ ?next =>
      let tail := eval cbn beta in (next tt) in
      lazymatch tail with bind (bind _ ?callback) _ =>
        let generalized := eval pattern callback in code in
        lazymatch generalized with ?family _ => exact (family scan) end
      end
    end
  end).
Lemma actual_body : funcdef_0__intern_body = body_with funcdef_0__rehashFormulas funcdef_0__formulaHash.
Proof. reflexivity. Qed.
Lemma actual_after_hash : after_hash = after_hash_with scan_callback.
Proof. reflexivity. Qed.
Definition scan_start (f : Frame) bucket pointer :=
  setNum (setNum f vardef_0__intern_bucket (Z.of_nat bucket)) vardef_0__intern_current (Z.of_nat pointer).
Definition query_arguments (f : Frame) := RehashExecution.hash_arguments
  (nums f vardef_0__intern_tag) (nums f vardef_0__intern_a) (nums f vardef_0__intern_b).

Lemma local_get (f : Frame) name : execLocal (R := Z) (numberLocalGet _ _ _ name) f = Some (nums f name,f).
Proof. reflexivity. Qed.
Lemma local_set (f : Frame) name value : execLocal (R := unit) (numberLocalSet _ _ _ name value) f = Some (tt,setNum f name value).
Proof. reflexivity. Qed.
Lemma local_done {R} (f : Frame) (value : R) : execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.
Lemma get_dispatch {R} (f : Frame) name (next : Z -> LocalAction R) :
  execLocal (Dispatch _ _ _ (NumberLocalGet _ _ _ name) next) f = execLocal (next (nums f name)) f.
Proof. reflexivity. Qed.
Lemma set_dispatch {R} (f : Frame) name value (next : unit -> LocalAction R) :
  execLocal (Dispatch _ _ _ (NumberLocalSet _ _ _ name value) next) f = execLocal (next tt) (setNum f name value).
Proof. reflexivity. Qed.
Lemma update_here {A} (ns : varsfuncdef_0__intern -> A) name value : Imperative.update ns name value name = value.
Proof. unfold Imperative.update. case_decide; [reflexivity|congruence]. Qed.
Lemma read_bucket (f : Frame) bucket :
  (bucket < length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal (R := Z) (retrieve _ _ _ arraydef_0__formulaBuckets (Z.of_nat bucket)) f =
    Some (List.nth bucket (memory (machine f) arraydef_0__formulaBuckets) 0,f).
Proof. destruct f. intro H. cbn [retrieve execLocal localStep step]. rewrite Nat2Z.id.
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0). reflexivity. Qed.

Section CollisionLoop.
Variable scan : Z -> LocalAction unit.
Theorem after_hash_composition (f : Frame) count bucket pointer :
  (21 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 21 = Z.of_nat bucket -> meta_value (machine f) 1 = Z.of_nat count ->
  (bucket < length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  List.nth bucket (memory (machine f) arraydef_0__formulaBuckets) 0 = Z.of_nat pointer ->
  execLocal (after_hash_with scan) f =
    optionBind (execLocal (scan (Z.of_nat count)) (scan_start f bucket pointer))
      (fun response => execLocal after_scan (snd response)).
Proof.
  intros Hmeta Hbucket Hcount Hbound Hpointer. destruct f as [s bs ns]. cbn [machine] in *.
  change (@List.nth (arrayType _ environment1 arraydef_0__formulaBuckets) bucket (memory s arraydef_0__formulaBuckets) 0 = Z.of_nat pointer) in Hpointer.
  unfold after_hash_with.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch |rewrite update_here
    |rewrite local_read_meta by (cbn [machine setMachine setNum]; lia)
    |rewrite read_bucket by (cbn [machine setMachine setNum]; exact Hbound)
    |rewrite Hbucket |rewrite Hcount |rewrite Hpointer
    |progress replace (Z.to_nat 21) with 21%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]]
  .
  unfold scan_start. cbv beta iota zeta delta [machine nums bools setNum setMachine]. reflexivity.
Qed.
End CollisionLoop.

Section Prelude.
Variables (resize : resize_function) (hash : hash_function).
Theorem skip_resize (f : Frame) :
  (20 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 1 <> meta_value (machine f) 20 ->
  execLocal (body_with resize hash) f = execLocal (after_resize hash) (setNum f vardef_0__intern_found 0).
Proof.
  intros Hmeta Hdifferent. unfold body_with, after_resize.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite local_read_meta by (cbn [machine setNum]; lia)
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 20) with 20%nat by reflexivity
    |rewrite bool_decide_false by (cbn [machine setNum]; exact Hdifferent)
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  reflexivity.
Qed.
Theorem run_resize (f : Frame) resized :
  (20 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 1 = meta_value (machine f) 20 ->
  exec (resize (fun _ => false) (fun _ => 0)) (machine f) = Some (tt,resized) ->
  execLocal (body_with resize hash) f =
    execLocal (after_resize hash) (setMachine (setNum f vardef_0__intern_found 0) resized).
Proof.
  intros Hmeta Hequal Hresize. unfold body_with, after_resize.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite local_read_meta by (cbn [machine setNum]; lia) |rewrite execLocal_lift
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 20) with 20%nat by reflexivity
    |rewrite bool_decide_true by (cbn [machine setNum]; exact Hequal)
    |rewrite Hresize
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  reflexivity.
Qed.
End Prelude.

Theorem after_resize_error hash (f : Frame) :
  (8 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 <> 0 ->
  execLocal (after_resize hash) f = Some (tt,f).
Proof.
  intros Hmeta Herror. unfold after_resize.
  repeat first [rewrite execLocal_bind |rewrite local_read_meta by (cbn [machine]; lia)
    |rewrite local_done |rewrite bool_decide_false by exact Herror
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress cbn [bind optionBind fst snd]]. reflexivity.
Qed.
Definition live_with (hash : hash_function) (post : LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold after_resize in (after_resize hash) in
  let code := eval cbn beta in code in
  let tail := eval unfold after_hash in after_hash in
  let tail := eval cbn beta in tail in
  let generalized := eval pattern tail in code in
  lazymatch generalized with ?family _ => exact (family post) end).
Lemma live_actual hash : after_resize hash = live_with hash after_hash.
Proof. reflexivity. Qed.
Section Live.
Variable hash : hash_function.
Variable post : LocalAction unit.
Theorem live_composition (f : Frame) hashed :
  (8 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  exec (hash (fun _ => false) (query_arguments f)) (machine f) = Some (tt,hashed) ->
  execLocal (live_with hash post) f = execLocal post (setMachine f hashed).
Proof.
  intros Hmeta Hflag Hhash. destruct f as [s bs ns]. cbn [machine] in *.
  unfold live_with, query_arguments, RehashExecution.hash_arguments in *.
  cbv beta iota zeta delta [nums] in Hhash.
  repeat first [rewrite execLocal_bind |rewrite local_read_meta by (cbn [machine]; lia)
    |rewrite local_get |rewrite local_set |rewrite local_done |rewrite execLocal_lift
    |rewrite Hhash |rewrite Hflag |rewrite bool_decide_true by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  destruct (execLocal post (setMachine {| machine := s; bools := bs; nums := ns |} hashed)) as [[[] final]|]; reflexivity.
Qed.
End Live.
Theorem after_resize_live hash (f : Frame) hashed :
  (8 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  exec (hash (fun _ => false) (query_arguments f)) (machine f) = Some (tt,hashed) ->
  execLocal (after_resize hash) f = execLocal after_hash (setMachine f hashed).
Proof. rewrite live_actual. apply live_composition. Qed.
End InternCoreExecution.
