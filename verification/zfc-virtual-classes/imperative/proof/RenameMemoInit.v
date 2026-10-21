From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow SipHash ArrayFacts RenameMemoTable RenameMemoLookup RenameMemoPlacement RenameMemoCapacity
  RenameMemoBuffers RenameMemoResize RenameMemoRebuildLoop ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoInit.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename) withLocalVariablesReturnValue R.
Ltac after_commands depth code := lazymatch depth with
  | O => code
  | S ?depth => lazymatch code with bind _ ?next =>
      let rest:=eval cbn beta in (next tt) in after_commands depth rest end
  end.
Definition clearing : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__rename_body in funcdef_0__rename_body in
  let code:=after_commands 4%nat code in lazymatch code with bind ?first _=>exact first end).
Definition clear_body total : nat->LocalAction LoopOutcome := ltac:(
  let code:=eval unfold clearing in clearing in
  lazymatch code with bind _ ?next=>let code:=eval cbn beta in (next total) in
    lazymatch code with loop _ ?body=>exact body end end).
Lemma clearing_is_loop : clearing=loop 16 (clear_body 16).
Proof. reflexivity. Qed.
Definition continuation : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__rename_body in funcdef_0__rename_body in
  let rest:=after_commands 5%nat code in exact rest).
Definition body_with (work : LocalAction unit) : LocalAction unit := ltac:(
  let code:=eval unfold funcdef_0__rename_body in funcdef_0__rename_body in
  let actual:=eval unfold continuation in continuation in
  let family:=eval pattern actual in code in lazymatch family with ?family _=>exact (family work) end).
Lemma body_actual : funcdef_0__rename_body=body_with continuation.
Proof. reflexivity. Qed.
Fixpoint clear_many (s : Machine) start fuel := match fuel with
  | O=>s |S rest=>clear_many (RenameMemoBuffers.write_memo s start (0,0,0,0)) (S start) rest end.
Lemma clear_length s start fuel : length (memory (clear_many s start fuel) arraydef_0__renameMemo)=length (memory s arraydef_0__renameMemo).
Proof. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. cbn [clear_many]. now rewrite IH,RenameMemoBuffers.memo_length. Qed.
Lemma clear_other s start fuel name : name<>arraydef_0__renameMemo -> memory (clear_many s start fuel) name=memory s name.
Proof. intro Hname. induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. cbn [clear_many]. now rewrite IH,RenameMemoBuffers.memo_other by exact Hname. Qed.
Lemma clear_outside s start fuel index : (index<start \/ start+fuel<=index)%nat ->
  RenameMemoLookup.table (clear_many s start fuel) index=RenameMemoLookup.table s index.
Proof.
  induction fuel as [|fuel IH] in s,start|-*; [reflexivity|]. intro Hindex. cbn [clear_many]. rewrite IH by lia.
  unfold RenameMemoLookup.table. rewrite RenameMemoBuffers.memo_array. apply ArrayFacts.nth_insert_other. lia.
Qed.
Lemma clear_inside s start fuel index : (start+fuel<=length (memory s arraydef_0__renameMemo))%nat ->
  (start<=index<start+fuel)%nat -> RenameMemoLookup.table (clear_many s start fuel) index=(0,0,0,0).
Proof.
  induction fuel as [|fuel IH] in s,start|-*; [lia|]. intros Hcapacity Hindex. cbn [clear_many].
  destruct (Nat.eq_dec index start) as [->|Hother].
  - rewrite clear_outside by lia. unfold RenameMemoLookup.table. rewrite RenameMemoBuffers.memo_array.
    apply OverflowExecution.nth_insert_same.
    eapply Nat.lt_le_trans; [|exact Hcapacity]. lia.
  - apply IH; [rewrite RenameMemoBuffers.memo_length; lia|lia].
Qed.
Lemma clear_io s start fuel : stdin (clear_many s start fuel)=stdin s /\ stdout (clear_many s start fuel)=stdout s.
Proof. induction fuel as [|fuel IH] in s,start|-*; [split; reflexivity|]. cbn [clear_many]. exact (IH (RenameMemoBuffers.write_memo s start (0,0,0,0)) (S start)). Qed.
Theorem generated_clear_step (f : Frame) total remaining index observations : total-Z.of_nat remaining-1=Z.of_nat index ->
  (index<length (memory (machine f) arraydef_0__renameMemo))%nat ->
  execLocalObserved (clear_body total remaining) (f,observations)=
    Some (KeepGoing,(setMachine f (RenameMemoBuffers.write_memo (machine f) index (0,0,0,0)),observations)).
Proof.
  intros Hindex Hbound. unfold clear_body.
  repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc |progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine]; rewrite Hindex,Nat2Z.id; exact Hbound)
    |progress rewrite Hindex |progress rewrite Nat2Z.id
    |progress cbn [dropWithinLoop Action_rect bind]]. reflexivity.
Qed.
Theorem generated_clear_loop fuel (f : Frame) total start observations : total=Z.of_nat (start+fuel) ->
  (start+fuel<=length (memory (machine f) arraydef_0__renameMemo))%nat ->
  execLocalObserved (loop fuel (clear_body total)) (f,observations)=Some (tt,(setMachine f (clear_many (machine f) start fuel),observations)).
Proof.
  induction fuel as [|fuel IH] in f,start|-*.
  - intros. destruct f. reflexivity.
  - intros Htotal Hbound. rewrite loop_S,local_bind.
    rewrite (generated_clear_step f total fuel start observations ltac:(lia) ltac:(lia)). cbn [optionBind fst snd].
    rewrite IH with (start:=S start) by (cbn [machine setMachine]; rewrite ?RenameMemoBuffers.memo_length; lia).
    destruct f. reflexivity.
Qed.
Definition setup s:=RenameMemoResize.memo_grown (store_meta (store_meta (store_meta s 10 0) 29 16) 30 0) 16.
Definition initialized s:=clear_many (setup s) 0 16.
Theorem generated_prefix (work : LocalAction unit) (f : Frame) observations :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (body_with work) (f,observations)=execLocalObserved work (setMachine f (initialized (machine f)),observations).
Proof.
  intros Hmeta.
  assert (Hclear : execLocalObserved clearing (setMachine f (setup (machine f)),observations)=
    Some (tt,(setMachine f (initialized (machine f)),observations))).
  { destruct f as [s bs ns]. rewrite clearing_is_loop.
    exact (generated_clear_loop 16 {|machine:=setup s;bools:=bs;nums:=ns|} 16 0 observations eq_refl
      (RenameMemoResize.memo_capacity (store_meta (store_meta (store_meta s 10 0) 29 16) 30 0) 16)). }
  destruct f as [s bs ns]. unfold body_with. cbn [machine] in *.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine]; repeat rewrite store_meta_length;
       eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta])
    |match goal with |- context [execLocalObserved (loop ?fuel ?body) ?state] =>
       let expression:=constr:(execLocalObserved (loop fuel body) state) in
       assert (Hrun : expression=Some (tt,(setMachine {|machine:=s;bools:=bs;nums:=ns|} (initialized s),observations))) by exact Hclear;
       rewrite Hrun; clear Hrun end
    |progress cbn [machine setMachine]].
  reflexivity.
Qed.
Lemma initialized_other s name : name<>arraydef_0__meta -> name<>arraydef_0__renameMemo ->
  memory (initialized s) name=memory s name.
Proof.
  intros Hmeta Hmemo. unfold initialized,setup. rewrite clear_other by exact Hmemo.
  rewrite RenameMemoResize.memo_grown_other by exact Hmemo. now rewrite !store_meta_other by exact Hmeta.
Qed.
Lemma initialized_meta_length s : length (memory (initialized s) arraydef_0__meta)=length (memory s arraydef_0__meta).
Proof.
  unfold initialized,setup. rewrite clear_other,RenameMemoResize.memo_grown_other by discriminate.
  now rewrite !store_meta_length.
Qed.
Lemma initialized_meta s cell : meta_value (initialized s) cell=
  meta_value (store_meta (store_meta (store_meta s 10 0) 29 16) 30 0) cell.
Proof.
  unfold meta_value,initialized,setup. now rewrite clear_other,RenameMemoResize.memo_grown_other by discriminate.
Qed.
Lemma initialized_meta_other s cell : cell<>10%nat -> cell<>29%nat -> cell<>30%nat ->
  meta_value (initialized s) cell=meta_value s cell.
Proof. intros. rewrite initialized_meta. now rewrite !meta_store_other by assumption. Qed.
Lemma initialized_stack s : (31<length (memory s arraydef_0__meta))%nat -> meta_value (initialized s) 10=0.
Proof. intro Hmeta. rewrite initialized_meta,!meta_store_other by lia. apply meta_store_same. lia. Qed.
Lemma initialized_size s : (31<length (memory s arraydef_0__meta))%nat -> meta_value (initialized s) 29=16.
Proof. intro Hmeta. rewrite initialized_meta,meta_store_other by lia. apply meta_store_same. rewrite store_meta_length. lia. Qed.
Lemma initialized_count s : (31<length (memory s arraydef_0__meta))%nat -> meta_value (initialized s) 30=0.
Proof. intro Hmeta. rewrite initialized_meta. apply meta_store_same. rewrite !store_meta_length. lia. Qed.
Lemma initialized_capacity s : (16<=length (memory (initialized s) arraydef_0__renameMemo))%nat.
Proof. unfold initialized. rewrite clear_length. apply RenameMemoResize.memo_capacity. Qed.
Lemma initialized_empty s index : (index<16)%nat -> RenameMemoLookup.table (initialized s) index=(0,0,0,0).
Proof. intro Hindex. unfold initialized. apply clear_inside; [apply RenameMemoResize.memo_capacity|lia]. Qed.
Lemma initialized_live s : RenameMemoCapacity.live (RenameMemoLookup.table (initialized s)) 16=0%nat.
Proof. apply RenameMemoRebuildLoop.empty_live. intros index Hindex. now rewrite initialized_empty by exact Hindex. Qed.
Lemma initialized_meaning s meaning : RenameMemoTable.represents (RenameMemoLookup.table (initialized s)) 16 meaning.
Proof. intros index Hindex Hoccupied. rewrite initialized_empty in Hoccupied by exact Hindex. contradiction. Qed.
Lemma initialized_indexed s : RenameMemoLookup.indexed (initialized s) 16.
Proof. intros index Hindex Hoccupied. rewrite initialized_empty in Hoccupied by exact Hindex. contradiction. Qed.
Lemma initialized_io s : stdin (initialized s)=stdin s /\ stdout (initialized s)=stdout s.
Proof. unfold initialized. exact (clear_io (setup s) 0 16). Qed.
Record postcondition s t meaning : Prop := {
  post_stack : meta_value t 10=0;
  post_size : meta_value t 29=16;
  post_capacity : (16<=length (memory t arraydef_0__renameMemo))%nat;
  post_empty : forall index, (index<16)%nat -> RenameMemoLookup.table t index=(0,0,0,0);
  post_live : meta_value t 30=Z.of_nat (RenameMemoCapacity.live (RenameMemoLookup.table t) 16);
  post_meaning : RenameMemoTable.represents (RenameMemoLookup.table t) 16 meaning;
  post_indexed : RenameMemoLookup.indexed t 16;
  post_arrays : forall name, name<>arraydef_0__meta -> name<>arraydef_0__renameMemo -> memory t name=memory s name;
  post_metadata : forall cell, cell<>10%nat -> cell<>29%nat -> cell<>30%nat -> meta_value t cell=meta_value s cell;
  post_metadata_length : length (memory t arraydef_0__meta)=length (memory s arraydef_0__meta);
  post_io : stdin t=stdin s /\ stdout t=stdout s
}.
Theorem initialized_invariant s meaning : (31<length (memory s arraydef_0__meta))%nat -> postcondition s (initialized s) meaning.
Proof.
  intro Hmeta. constructor.
  - now apply initialized_stack.
  - now apply initialized_size.
  - apply initialized_capacity.
  - apply initialized_empty.
  - rewrite initialized_count by exact Hmeta. now rewrite initialized_live.
  - apply initialized_meaning.
  - apply initialized_indexed.
  - apply initialized_other.
  - apply initialized_meta_other.
  - apply initialized_meta_length.
  - apply initialized_io.
Qed.
Theorem generated_initial_invariant (f : Frame) observations meaning :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved funcdef_0__rename_body (f,observations)=
    execLocalObserved continuation (setMachine f (initialized (machine f)),observations) /\
  postcondition (machine f) (initialized (machine f)) meaning.
Proof. intro Hmeta. split; [rewrite body_actual; now apply generated_prefix|now apply initialized_invariant]. Qed.
End RenameMemoInit.
