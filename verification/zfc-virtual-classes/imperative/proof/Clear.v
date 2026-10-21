From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash InternTail HashTable Rehash Rebuild.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ClearExecution.
Import IndexExecution SipHashExecution InternTailExecution HashTableInvariant RehashExecution.

(* Take both loop callbacks from the generated procedure. Keeping the count
   argument bound here avoids assuming anything about its local variables. *)
Ltac rehash_callbacks code use :=
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind (bind _ ?branch) _ =>
      let code := eval cbn beta iota in (branch false) in
      lazymatch code with bind _ ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind _ ?next =>
          let code := eval cbn beta in (next tt) in
          lazymatch code with bind (bind _ ?clear) ?next =>
            let code := eval cbn beta in (next tt) in
            lazymatch code with bind _ ?next =>
              let code := eval cbn beta in (next tt) in
              lazymatch code with bind (bind _ ?rebuild) _ => use clear rebuild end
            end
          end
        end
      end
    end
  end.
Definition clearing (total : Z) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__rehashFormulas_body in funcdef_0__rehashFormulas_body in
  rehash_callbacks code ltac:(fun clear rebuild => exact (clear total))).
Definition rebuilding (total : Z) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__rehashFormulas_body in funcdef_0__rehashFormulas_body in
  rehash_callbacks code ltac:(fun clear rebuild => exact (rebuild total))).
Definition clear_body (total : Z) (remaining : nat) : LocalAction LoopOutcome := ltac:(
  let code := eval unfold clearing in (clearing total) in
  let code := eval cbn beta in code in
  lazymatch code with loop _ ?body => exact (body remaining) end).
Lemma clearing_is_loop total : clearing total = loop (Z.to_nat total) (clear_body total).
Proof. reflexivity. Qed.
Lemma rebuilding_is_loop total : rebuilding total =
  loop (Z.to_nat total) (relink_body funcdef_0__formulaHash total).
Proof. reflexivity. Qed.
Definition body_with (clear rebuild : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__rehashFormulas_body in funcdef_0__rehashFormulas_body in
  rehash_callbacks code ltac:(fun c r =>
    let generalized := eval pattern c,r in code in
    lazymatch generalized with ?family _ _ => exact (family clear rebuild) end)).
Lemma actual_body : funcdef_0__rehashFormulas_body = body_with clearing rebuilding.
Proof. reflexivity. Qed.

Definition clear_tick (s : Machine) i :=
  withMemory s (modifyArray (memory s) arraydef_0__formulaBuckets i 0).
Definition clear_frame (f : Frame) i := setMachine f (clear_tick (machine f) i).
Lemma tick_buckets s i : memory (clear_tick s i) arraydef_0__formulaBuckets =
  <[i := 0]> (memory s arraydef_0__formulaBuckets).
Proof. apply modify_same. Qed.
Lemma tick_length s i : length (memory (clear_tick s i) arraydef_0__formulaBuckets) =
  length (memory s arraydef_0__formulaBuckets).
Proof. rewrite tick_buckets. apply length_insert. Qed.
Lemma tick_other s i name : name <> arraydef_0__formulaBuckets ->
  memory (clear_tick s i) name = memory s name.
Proof. apply modify_other. Qed.

Theorem generated_clear_step f total remaining index :
  total - Z.of_nat remaining - 1 = Z.of_nat index ->
  (index < length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal (clear_body total remaining) f = Some (KeepGoing,clear_frame f index).
Proof.
  intros Hindex Hbound. unfold clear_body.
  repeat first [rewrite execLocal_bind |rewrite dropWithinLoop_1 |rewrite exec_drop_lift
    |rewrite local_done |rewrite Hindex |rewrite Nat2Z.id
    |rewrite local_write_array by (try rewrite Hindex; try rewrite Nat2Z.id; exact Hbound)
    |progress cbn [bind optionBind fst snd]].
  reflexivity.
Qed.
Fixpoint clear_many (s : Machine) start fuel : Machine := match fuel with
| O => s | S fuel => clear_many (clear_tick s start) (S start) fuel end.
Lemma clear_many_length s start fuel :
  length (memory (clear_many s start fuel) arraydef_0__formulaBuckets) =
  length (memory s arraydef_0__formulaBuckets).
Proof. induction fuel as [|fuel IH] in s, start |- *; cbn [clear_many]; [reflexivity|now rewrite IH, tick_length]. Qed.
Lemma clear_many_other s start fuel name : name <> arraydef_0__formulaBuckets ->
  memory (clear_many s start fuel) name = memory s name.
Proof. intro H. induction fuel as [|fuel IH] in s, start |- *; cbn [clear_many]; [reflexivity|now rewrite IH, tick_other]. Qed.
Lemma clear_many_io s start fuel : stdin (clear_many s start fuel) = stdin s /\
  stdout (clear_many s start fuel) = stdout s.
Proof. induction fuel as [|fuel IH] in s, start |- *; cbn [clear_many]; [split; reflexivity|exact (IH (clear_tick s start) (S start))]. Qed.
Lemma clear_many_outside s start fuel b :
  (b < start \/ start + fuel <= b)%nat ->
  head_at (clear_many s start fuel) b = head_at s b.
Proof.
  induction fuel as [|fuel IH] in s, start |- *; [reflexivity|]. intro H.
  cbn [clear_many]. rewrite IH by lia.
  unfold head_at. rewrite tick_buckets. apply ArrayFacts.nth_insert_other. lia.
Qed.
Lemma clear_many_inside s start fuel b :
  (start + fuel <= length (memory s arraydef_0__formulaBuckets))%nat ->
  (start <= b < start + fuel)%nat -> head_at (clear_many s start fuel) b = 0.
Proof.
  induction fuel as [|fuel IH] in s, start |- *; [lia|]. intros Hlength Hb. cbn [clear_many].
  destruct (Nat.eq_dec b start) as [->|Hne].
  - rewrite clear_many_outside by lia. unfold head_at. rewrite tick_buckets.
    apply OverflowExecution.nth_insert_same. lia.
  - apply IH; [rewrite tick_length; lia|lia].
Qed.
Theorem generated_clear_loop fuel (f : Frame) total start :
  total = Z.of_nat (start + fuel) ->
  (start + fuel <= length (memory (machine f) arraydef_0__formulaBuckets))%nat ->
  execLocal (loop fuel (clear_body total)) f =
    Some (tt,setMachine f (clear_many (machine f) start fuel)).
Proof.
  induction fuel as [|fuel IH] in f, start |- *.
  - intros. destruct f. reflexivity.
  - intros Htotal Hbound. rewrite loop_S, execLocal_bind.
    rewrite (generated_clear_step f total fuel start ltac:(lia) ltac:(lia)).
    cbn [optionBind fst snd]. rewrite (IH (clear_frame f start) (S start)).
    + destruct f. reflexivity.
    + lia.
    + cbn [clear_frame machine setMachine]. rewrite tick_length. lia.
Qed.
Lemma empty_indexed s bucket_of :
  (forall b, (b < length (memory s arraydef_0__formulaBuckets))%nat -> head_at s b = 0) ->
  indexed s 0 bucket_of.
Proof.
  intro Hempty. split.
  - split; [lia|]. split; [lia|]. intros; lia.
  - split; [intros b Hb; rewrite Hempty by exact Hb; lia|intros; lia].
Qed.
End ClearExecution.
