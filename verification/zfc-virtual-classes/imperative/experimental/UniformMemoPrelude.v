From CoqCP Require Import Options Imperative Execution.
From UniformMemoFixture Require Import UniformMemoProgram UniformMemoLoop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module UniformMemoPrelude.
Import UniformMemoLoop.

(* The residual program immediately after the hash call in the nonzero-size
   branch. This is extracted from the generated Action, not a handwritten copy. *)
Definition after_hash : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformMemoGet_body in funcdef_0__uniformMemoGet_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind (bind _ ?branch) ?continuation =>
        let code := eval cbn beta iota in (branch false) in
        lazymatch code with bind _ ?next =>
          let rest := eval cbn beta in (next tt) in exact (bind rest continuation)
        end
      end
    end
  end).

Definition hash_args (f : Frame) : varsfuncdef_0__formulaHash -> Z :=
  update (update (update (fun _ => 0) vardef_0__formulaHash_tag 51)
    vardef_0__formulaHash_a (nums f vardef_0__uniformMemoGet_node))
    vardef_0__formulaHash_b (nums f vardef_0__uniformMemoGet_depth).
Definition reset_machine (f : Frame) count size :=
  withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__uniformMemoState 0 (count,size,0,0)).
Definition reset_frame (f : Frame) count size :=
  setMachine (setNum f vardef_0__uniformMemoGet_size size) (reset_machine f count size).

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

Lemma read_state (f : Frame) : (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__uniformMemoState 0) f =
    Some (List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0),f).
Proof.
  destruct f. intro H. cbn [retrieve execLocal localStep step].
  case_decide; [|lia]. rewrite nth_lt_default with (default := (0,0,0,0)). reflexivity.
Qed.
Lemma write_state (f : Frame) value : (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  execLocal (store _ _ _ arraydef_0__uniformMemoState 0 value) f =
    Some (tt,setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__uniformMemoState 0 value))).
Proof. destruct f. intro H. cbn [store execLocal localStep step]. case_decide; [reflexivity|lia]. Qed.
Lemma update_here {A} (ns : varsfuncdef_0__uniformMemoGet -> A) name value : Imperative.update ns name value name = value.
Proof. unfold Imperative.update. case_decide; [reflexivity|congruence]. Qed.
Lemma update_other {A} (ns : varsfuncdef_0__uniformMemoGet -> A) name other value : name <> other -> Imperative.update ns name value other = ns other.
Proof. intro H. unfold Imperative.update. case_decide; [congruence|reflexivity]. Qed.
Lemma finish_unit {A} (x : option (unit * A)) :
  optionBind x (fun p => Some (tt,snd p)) = x.
Proof. destruct x as [[[] a]|]; reflexivity. Qed.

(* This theorem assumes termination of the existing hash helper. It does not
   assert hash correctness or that the post-hash bucket lookup is in bounds. *)
Theorem hash_prelude (f : Frame) count size oldfound oldvalue hashed :
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,oldfound,oldvalue) ->
  size <> 0 ->
  exec (funcdef_0__formulaHash (fun _ => false) (hash_args f)) (reset_machine f count size) = Some (tt,hashed) ->
  execLocal funcdef_0__uniformMemoGet_body f = execLocal after_hash (setMachine (reset_frame f count size) hashed).
Proof.
  intros Hstate Hvalue Hsize Hhash. destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold funcdef_0__uniformMemoGet_body, after_hash, hash_args, reset_frame, reset_machine in *.
  cbn [machine nums] in Hhash.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch |rewrite execLocal_lift
    |rewrite read_state by (cbn [machine setNum setMachine]; lia)
    |rewrite (write_state (setNum {| machine := s; bools := bs; nums := ns |} vardef_0__uniformMemoGet_size size) (count,size,0,0)) by (cbn [machine setNum]; lia)
    |rewrite write_state by (cbn [machine setNum setMachine]; lia)
    |rewrite update_here
    |rewrite update_other by discriminate
    |rewrite Hvalue |rewrite Hhash
    |rewrite bool_decide_false by (cbn [nums setNum]; exact Hsize)
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  reflexivity.
Qed.

Definition scan_callback (total : Z) : LocalAction unit := loop (Z.to_nat total) scan_body.
Definition after_hash_with (scan : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold after_hash in after_hash in
  let code := eval cbn beta in code in
  let whole := code in
  lazymatch code with bind ?inner _ =>
  let code := inner in
  lazymatch code with bind _ ?next =>
    let tail := eval cbn beta in (next tt) in
    lazymatch tail with bind _ ?next =>
      let tail := eval cbn beta in (next tt) in
      lazymatch tail with bind (bind _ ?callback) _ =>
        let generalized := eval pattern callback in whole in
        lazymatch generalized with ?family _ => exact (family scan) end
      end
    end
  end end).
Lemma after_hash_actual : after_hash = after_hash_with scan_callback.
Proof. reflexivity. Qed.

Lemma read_bucket (f : Frame) bucket :
  (bucket < length (memory (machine f) arraydef_0__uniformMemoBuckets))%nat ->
  execLocal (retrieve _ _ _ arraydef_0__uniformMemoBuckets (Z.of_nat bucket)) f =
    Some (List.nth bucket (memory (machine f) arraydef_0__uniformMemoBuckets) 0,f).
Proof.
  destruct f. intro H. cbn [retrieve execLocal localStep step]. rewrite Nat2Z.id.
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0). reflexivity.
Qed.

Definition scan_start (f : Frame) bucket pointer :=
  setNum (setNum f vardef_0__uniformMemoGet_bucket (Z.of_nat bucket))
    vardef_0__uniformMemoGet_current (Z.of_nat pointer).

(* The modulo execution is a local primitive premise, independently of any
   collision scan. The stated array facts locate the scan's starting link. *)
Theorem after_hash_composition (scan : Z -> LocalAction unit) (f : Frame) count bucket pointer size found value :
  execLocal (modIntUnsigned (retrieve _ _ _ arraydef_0__meta 28)
    (numberLocalGet _ _ _ vardef_0__uniformMemoGet_size)) f = Some (Z.of_nat bucket,f) ->
  (bucket < length (memory (machine f) arraydef_0__uniformMemoBuckets))%nat ->
  List.nth bucket (memory (machine f) arraydef_0__uniformMemoBuckets) 0 = Z.of_nat pointer ->
  (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
  List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (Z.of_nat count,size,found,value) ->
  execLocal (after_hash_with scan) f = execLocal (scan (Z.of_nat count)) (scan_start f bucket pointer).
Proof.
  intros Hmod Hbound Hpointer Hstate Hcount. destruct f as [s bs ns]. cbn [machine] in *.
  unfold after_hash_with.
  repeat first [rewrite execLocal_bind |rewrite local_get |rewrite local_set |rewrite local_done
    |rewrite get_dispatch |rewrite set_dispatch
    |rewrite Hmod
    |rewrite read_bucket by (cbn [machine setNum setMachine]; exact Hbound)
    |rewrite read_state by (cbn [machine setNum setMachine]; exact Hstate)
    |rewrite Hpointer |rewrite Hcount
    |progress cbn [bind optionBind machine nums bools setNum setMachine fst snd]].
  unfold scan_start. cbn [machine nums bools setNum setMachine].
  destruct (execLocal (scan (Z.of_nat count))
    (setNum (setNum {| machine := s; bools := bs; nums := ns |} vardef_0__uniformMemoGet_bucket (Z.of_nat bucket))
      vardef_0__uniformMemoGet_current (Z.of_nat pointer))) as [[[] final]|]; reflexivity.
Qed.
End UniformMemoPrelude.
