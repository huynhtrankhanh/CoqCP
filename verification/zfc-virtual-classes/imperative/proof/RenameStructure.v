From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Stack Observation ObservedLocal NativePrimitives.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameStructure.
Import IndexExecution SipHashExecution ObservedLocal.
Local Opaque loop.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename) withLocalVariablesReturnValue R.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__rename.
Ltac parts use :=
  let code := eval unfold funcdef_0__rename_body in funcdef_0__rename_body in
  lazymatch code with bind _ ?after_clear =>
    let code := eval cbn beta in (after_clear tt) in
    lazymatch code with bind _ ?after_push =>
      let code := eval cbn beta in (after_push tt) in
      lazymatch code with bind ?traversal ?after => use traversal after end
    end
  end.
Definition traversal : LocalAction unit := ltac:(parts ltac:(fun work after => exact work)).
Definition finish : LocalAction unit := ltac:(parts ltac:(fun work after => exact (after tt))).
Ltac descend_loops levels code use :=
  lazymatch levels with
  | O => use code
  | S ?levels =>
      match code with context [loop ?count ?body] =>
        let next := eval cbn beta iota zeta delta [bind] in (body 0%nat) in descend_loops levels next use
      end
  end.
Definition iteration : LocalAction LoopOutcome := ltac:(
  let code := eval unfold traversal in traversal in
  let code := eval cbn beta iota zeta delta [bind] in code in
  descend_loops 8%nat code ltac:(fun selected => exact selected)).
Definition body_with (work : LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__rename_body in funcdef_0__rename_body in
  let work_actual := eval unfold traversal in traversal in
  let family := eval pattern work_actual in code in
  lazymatch family with ?family _ => exact (family work) end).
Local Opaque loop.
Lemma actual_body : funcdef_0__rename_body = body_with traversal.
Proof. reflexivity. Qed.
Definition pushed (f : Frame) := StackExecution.push_state (store_meta (machine f) 10 0) 0
  (nums f vardef_0__rename_node) (nums f vardef_0__rename_initialDepth).
Local Opaque funcdef_0__push.
Theorem generated_prefix (work : LocalAction unit) (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (body_with work) (f,observations) =
    execLocalObserved (work >>= fun _ => finish) (setMachine f (pushed f),observations).
Proof.
  intros Hmeta.
  set (cleared := store_meta (machine f) 10 0).
  set (args := update (update (fun _ => 0) vardef_0__push_node (nums f vardef_0__rename_node))
    vardef_0__push_depth (nums f vardef_0__rename_initialDepth)).
  assert (Hpush : execObserved (funcdef_0__push (fun _ => false) args) (cleared,observations) = Some (tt,(pushed f,observations))).
  { apply observed_plain; [apply InternalObservation.push_nf|].
    apply StackExecution.generated_push.
    - unfold cleared. now rewrite store_meta_length.
    - change (meta_value cleared 10 = 0). unfold cleared. now apply meta_store_same.
    - unfold maximum. cbn. lia. }
  unfold body_with. destruct f as [s bs ns]. cbn [machine nums] in *. unfold finish.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hmeta)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__push ?bp ?np) ?state] =>
      let expression := constr:(@execObserved I T EI R (funcdef_0__push bp np) state) in
      let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(pushed {|machine:=s; bools:=bs; nums:=ns|},observations))) by exact Hpush;
      rewrite Hrun; clear Hrun end
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
Theorem generated_finish_empty (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 10 = 0 ->
  execLocalObserved finish (f,observations) = Some (tt,(f,observations)).
Proof.
  intros Hmeta Hempty. unfold finish.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hmeta)
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress rewrite Hempty |progress rewrite bool_decide_true by reflexivity
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
Theorem generated_finish_exhausted (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 10 <> 0 ->
  execLocalObserved finish (f,observations) = Some (tt,(setMachine f (store_meta (machine f) 8 1),observations)).
Proof.
  intros Hmeta Hnonempty. unfold finish.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; first [exact Hmeta | eapply Nat.le_lt_trans with (m := 10%nat); [cbn; lia|exact Hmeta]])
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress rewrite bool_decide_true by exact Hnonempty
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
End RenameStructure.
