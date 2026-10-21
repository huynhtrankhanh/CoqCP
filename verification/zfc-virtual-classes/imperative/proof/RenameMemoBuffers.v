From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash Rehash
  RenameMemoTable ObservedLocal Observation LocalObservation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoBuffers.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__renameCacheGrow)
  withLocalVariablesReturnValue R.
Ltac callbacks code use :=
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
            lazymatch code with bind (bind _ ?rebuild) ?next =>
              let code := eval cbn beta in (next tt) in
              lazymatch code with bind (bind _ ?branch) _ =>
                let code := eval cbn beta iota in (branch true) in
                lazymatch code with bind _ ?next =>
                  let code := eval cbn beta in (next tt) in
                  lazymatch code with bind (bind _ ?copy) _ => use clear rebuild copy end
                end
              end
            end
          end
        end
      end
    end
  end.
Definition clearing (total : Z) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__renameCacheGrow_body in funcdef_0__renameCacheGrow_body in
  callbacks code ltac:(fun clear rebuild copy => exact (clear total))).
Definition rebuilding (total : Z) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__renameCacheGrow_body in funcdef_0__renameCacheGrow_body in
  callbacks code ltac:(fun clear rebuild copy => exact (rebuild total))).
Definition copying (total : Z) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__renameCacheGrow_body in funcdef_0__renameCacheGrow_body in
  callbacks code ltac:(fun clear rebuild copy => exact (copy total))).
Definition clear_body total : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold clearing in (clearing total) in
  let code := eval cbn beta in code in lazymatch code with loop _ ?body => exact body end).
Definition rebuild_body total : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold rebuilding in (rebuilding total) in
  let code := eval cbn beta in code in lazymatch code with loop _ ?body => exact body end).
Definition copy_body total : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold copying in (copying total) in
  let code := eval cbn beta in code in lazymatch code with loop _ ?body => exact body end).
Lemma clearing_is_loop total : clearing total = loop (Z.to_nat total) (clear_body total).
Proof. reflexivity. Qed.
Lemma rebuilding_is_loop total : rebuilding total = loop (Z.to_nat total) (rebuild_body total).
Proof. reflexivity. Qed.
Lemma copying_is_loop total : copying total = loop (Z.to_nat total) (copy_body total).
Proof. reflexivity. Qed.
Definition body_with (clear rebuild copy : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__renameCacheGrow_body in funcdef_0__renameCacheGrow_body in
  callbacks code ltac:(fun c r cp =>
    let generalized := eval pattern c,r,cp in code in
    lazymatch generalized with ?family _ _ _ => exact (family clear rebuild copy) end)).
Lemma actual_body : funcdef_0__renameCacheGrow_body = body_with clearing rebuilding copying.
Proof. reflexivity. Qed.
Definition scratch (s : Machine) index : RenameMemoTable.entry := List.nth index (memory s arraydef_0__renameMemoScratch) (0,0,0,0).
Definition write_scratch (s : Machine) index (e : RenameMemoTable.entry) :=
  withMemory s (modifyArray (memory s) arraydef_0__renameMemoScratch index e).
Definition write_memo (s : Machine) index (e : RenameMemoTable.entry) :=
  withMemory s (modifyArray (memory s) arraydef_0__renameMemo index e).
Lemma scratch_array s index e : memory (write_scratch s index e) arraydef_0__renameMemoScratch =
  <[index := e]> (memory s arraydef_0__renameMemoScratch).
Proof. reflexivity. Qed.
Lemma memo_array s index e : memory (write_memo s index e) arraydef_0__renameMemo =
  <[index := e]> (memory s arraydef_0__renameMemo).
Proof. reflexivity. Qed.
Lemma scratch_other s index e name : name <> arraydef_0__renameMemoScratch -> memory (write_scratch s index e) name = memory s name.
Proof. destruct name; intro Hname; try congruence; reflexivity. Qed.
Lemma memo_other s index e name : name <> arraydef_0__renameMemo -> memory (write_memo s index e) name = memory s name.
Proof. destruct name; intro Hname; try congruence; reflexivity. Qed.
Lemma scratch_length s index e : length (memory (write_scratch s index e) arraydef_0__renameMemoScratch) = length (memory s arraydef_0__renameMemoScratch).
Proof. rewrite scratch_array. apply length_insert. Qed.
Lemma memo_length s index e : length (memory (write_memo s index e) arraydef_0__renameMemo) = length (memory s arraydef_0__renameMemo).
Proof. rewrite memo_array. apply length_insert. Qed.
Lemma scratch_at_same s index e : (index < length (memory s arraydef_0__renameMemoScratch))%nat -> scratch (write_scratch s index e) index = e.
Proof. intro Hindex. unfold scratch. rewrite scratch_array. now apply OverflowExecution.nth_insert_same. Qed.
Lemma scratch_at_other s index e other : other <> index -> scratch (write_scratch s index e) other = scratch s other.
Proof. intro Hother. unfold scratch. rewrite scratch_array. now apply ArrayFacts.nth_insert_other. Qed.
Lemma local_read_array (f : Frame) name slot (default : arrayType _ environment1 name) :
  (Z.to_nat slot < length (memory (machine f) name))%nat ->
  execLocal (retrieve _ _ _ name slot) f = Some (List.nth (Z.to_nat slot) (memory (machine f) name) default,f).
Proof. destruct f. intro H. cbn [retrieve execLocal localStep step]. case_decide; [|lia].
  rewrite nth_lt_default with (default:=default). reflexivity. Qed.
Lemma local_write_array (f : Frame) name slot value :
  (Z.to_nat slot < length (memory (machine f) name))%nat ->
  execLocal (R:=unit) (store _ _ _ name slot value) f =
    Some (tt,setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) name (Z.to_nat slot) value))).
Proof. intro H. cbn [store execLocal localStep step]. case_decide; [reflexivity|lia]. Qed.
Lemma local_done {R} (value : R) (f : Frame) : execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.
Theorem generated_clear_step (f : Frame) total remaining index : total - Z.of_nat remaining - 1 = Z.of_nat index ->
  (index < length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  execLocal (clear_body total remaining) f = Some (KeepGoing,setMachine f (write_scratch (machine f) index (0,0,0,0))).
Proof.
  intros Hindex Hbound. unfold clear_body.
  repeat first [rewrite execLocal_bind |rewrite dropWithinLoop_1 |rewrite exec_drop_lift
    |rewrite local_done |rewrite Hindex |rewrite Nat2Z.id
    |rewrite local_write_array by (try rewrite Hindex; try rewrite Nat2Z.id; exact Hbound)
    |progress cbn [bind optionBind fst snd]]. reflexivity.
Qed.
Fixpoint clear_many (s : Machine) start fuel := match fuel with
  | O=>s |S rest=>clear_many (write_scratch s start (0,0,0,0)) (S start) rest end.
Lemma clear_many_length s start fuel : length (memory (clear_many s start fuel) arraydef_0__renameMemoScratch) = length (memory s arraydef_0__renameMemoScratch).
Proof. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. cbn [clear_many]. now rewrite IH,scratch_length. Qed.
Lemma clear_many_other s start fuel name : name <> arraydef_0__renameMemoScratch -> memory (clear_many s start fuel) name = memory s name.
Proof. intro Hname. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. cbn [clear_many]. now rewrite IH,scratch_other by exact Hname. Qed.
Lemma clear_many_outside s start fuel index : (index < start \/ start+fuel <= index)%nat ->
  scratch (clear_many s start fuel) index = scratch s index.
Proof. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. intros Hindex. cbn [clear_many]. rewrite IH by lia. now apply scratch_at_other; lia. Qed.
Lemma clear_many_inside s start fuel index : (start+fuel <= length (memory s arraydef_0__renameMemoScratch))%nat ->
  (start <= index < start+fuel)%nat -> scratch (clear_many s start fuel) index = (0,0,0,0).
Proof.
  induction fuel as [|fuel IH] in s,start|-*; [lia|]. intros Hcapacity Hindex. cbn [clear_many].
  destruct (Nat.eq_dec index start) as [->|Hother].
  - rewrite clear_many_outside by lia. apply scratch_at_same. lia.
  - apply IH; [rewrite scratch_length; lia|lia].
Qed.
Theorem generated_clear_loop fuel (f : Frame) total start : total = Z.of_nat (start+fuel) ->
  (start+fuel <= length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  execLocal (loop fuel (clear_body total)) f = Some (tt,setMachine f (clear_many (machine f) start fuel)).
Proof.
  induction fuel as [|fuel IH] in f,start|-*.
  - intros. destruct f. reflexivity.
  - intros Htotal Hbound. rewrite loop_S,execLocal_bind.
    rewrite (generated_clear_step f total fuel start ltac:(lia) ltac:(lia)). cbn [optionBind fst snd].
    rewrite IH with (start:=S start) by (cbn [machine setMachine]; rewrite ?scratch_length; lia). destruct f. reflexivity.
Qed.
Theorem generated_copy_step (f : Frame) total remaining index : total - Z.of_nat remaining - 1 = Z.of_nat index ->
  (index < length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  (index < length (memory (machine f) arraydef_0__renameMemo))%nat ->
  execLocal (copy_body total remaining) f = Some (KeepGoing,setMachine f (write_memo (machine f) index (scratch (machine f) index))).
Proof.
  intros Hindex Hscratch Hmemo. unfold copy_body.
  repeat first [rewrite execLocal_bind |rewrite dropWithinLoop_1 |rewrite exec_drop_lift
    |rewrite local_done |rewrite Hindex |rewrite Nat2Z.id
    |match goal with |- context [@execLocal ?I ?T ?EI ?V ?EV ?R
        (retrieve _ _ _ arraydef_0__renameMemoScratch ?slot) ?frame] =>
      let expression := constr:(@execLocal I T EI V EV R (retrieve _ _ _ arraydef_0__renameMemoScratch slot) frame) in
      let Hread := fresh "Hread" in
      assert (Hread : expression = Some (List.nth (Z.to_nat slot) (memory (machine frame) arraydef_0__renameMemoScratch) (0,0,0,0),frame)) by
        exact (local_read_array frame arraydef_0__renameMemoScratch slot (0,0,0,0) ltac:(rewrite Nat2Z.id; exact Hscratch));
      rewrite Hread; clear Hread end
    |rewrite local_write_array by (try rewrite Hindex; try rewrite Nat2Z.id; exact Hmemo)
    |progress cbn [bind optionBind fst snd]].
  unfold scratch. destruct (List.nth index (memory (machine f) arraydef_0__renameMemoScratch) (0,0,0,0)) as [[[a b] c] d]. reflexivity.
Qed.
Fixpoint copy_many (s : Machine) start fuel := match fuel with
  |O=>s |S rest=>copy_many (write_memo s start (scratch s start)) (S start) rest end.
Lemma copy_many_length s start fuel : length (memory (copy_many s start fuel) arraydef_0__renameMemo) = length (memory s arraydef_0__renameMemo).
Proof. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. cbn [copy_many]. now rewrite IH,memo_length. Qed.
Lemma copy_many_other s start fuel name : name <> arraydef_0__renameMemo -> memory (copy_many s start fuel) name = memory s name.
Proof. intro Hname. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. cbn [copy_many]. now rewrite IH,memo_other by exact Hname. Qed.
Lemma copy_many_scratch s start fuel index : scratch (copy_many s start fuel) index = scratch s index.
Proof. unfold scratch. now rewrite copy_many_other by discriminate. Qed.
Lemma copy_many_outside s start fuel index : (index < start \/ start+fuel <= index)%nat ->
  List.nth index (memory (copy_many s start fuel) arraydef_0__renameMemo) (0,0,0,0) = List.nth index (memory s arraydef_0__renameMemo) (0,0,0,0).
Proof. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. intros Hindex. cbn [copy_many]. rewrite IH by lia. rewrite memo_array. apply ArrayFacts.nth_insert_other. lia. Qed.
Lemma copy_many_inside s start fuel index : (start+fuel <= length (memory s arraydef_0__renameMemo))%nat ->
  (start <= index < start+fuel)%nat ->
  List.nth index (memory (copy_many s start fuel) arraydef_0__renameMemo) (0,0,0,0) = scratch s index.
Proof.
  induction fuel as [|fuel IH] in s,start|-*; [lia|]. intros Hcapacity Hindex. cbn [copy_many].
  destruct (Nat.eq_dec index start) as [->|Hother].
  - rewrite copy_many_outside by lia. rewrite memo_array. apply OverflowExecution.nth_insert_same. lia.
  - rewrite IH by (rewrite ?memo_length; lia). unfold scratch. now rewrite memo_other by discriminate.
Qed.
Theorem generated_copy_loop fuel (f : Frame) total start : total = Z.of_nat (start+fuel) ->
  (start+fuel <= length (memory (machine f) arraydef_0__renameMemoScratch))%nat ->
  (start+fuel <= length (memory (machine f) arraydef_0__renameMemo))%nat ->
  execLocal (loop fuel (copy_body total)) f = Some (tt,setMachine f (copy_many (machine f) start fuel)).
Proof.
  induction fuel as [|fuel IH] in f,start|-*.
  - intros. destruct f. reflexivity.
  - intros Htotal Hscratch Hmemo. rewrite loop_S,execLocal_bind.
    rewrite (generated_copy_step f total fuel start ltac:(lia) ltac:(lia) ltac:(lia)). cbn [optionBind fst snd].
    rewrite IH with (start:=S start) by (cbn [machine setMachine]; rewrite ?memo_length,?memo_other by discriminate; lia).
    destruct f. reflexivity.
Qed.
End RenameMemoBuffers.
