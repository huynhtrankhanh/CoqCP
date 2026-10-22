From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoBounds RenameMemoWork RenameMemoSchedule
  RenameMemoInit RenameMemoControl ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoLoop.
Import IndexExecution SipHashExecution RenameMemoInit ObservedLocal.
(* The only conditional premise is a single native scheduler step.  The finite
   generated loop, its stopping branch, and sufficient checked fuel are proved
   here; the premise does not postulate a complete run. *)
Section Composition.
Context (graph : nat->RenameMemoWork.shape) (root base : nat)
  (related : Frame->RenameMemoSchedule.state->Prop).
Hypothesis graph_older : RenameMemoWork.older graph.
Hypothesis ready : forall f model, related f model ->
  (10<length (memory (machine f) arraydef_0__meta))%nat /\
  (RenameMemoSchedule.stack model=[] -> meta_value (machine f) 10=0).
Hypothesis advance : forall steps f model,
  RenameMemoSchedule.reached graph root base steps model ->
  related f model -> RenameMemoSchedule.stack model<>[] ->
  forall observations, exists after next,
    execLocalObserved RenameMemoControl.iteration (f,observations)=Some (KeepGoing,(after,observations)) /\
    RenameMemoSchedule.move graph model next /\ related after next.
Theorem finite fuel steps f model :
  (fuel+steps=RenameMemoBounds.fuel root)%nat ->
  RenameMemoSchedule.reached graph root base steps model -> related f model ->
  forall observations, exists final finished final_steps,
    execLocalObserved (loop fuel RenameMemoControl.iteration_at) (f,observations)=Some (tt,(final,observations)) /\
    related final finished /\ RenameMemoSchedule.stack finished=[] /\
    RenameMemoSchedule.reached graph root base final_steps finished /\ (steps<=final_steps)%nat.
Proof.
  induction fuel as [|fuel IH] in steps,f,model |- *; intros Hbudget Hreach Hrelated observations.
  - destruct (RenameMemoSchedule.polynomial_trace _ _ _ _ _ graph_older Hreach) as [_ [Hstrict _]]. lia.
  - destruct (RenameMemoSchedule.stack model) as [|task tail] eqn:Hempty.
    + exists f,model,steps. split.
      * rewrite loop_S,local_bind,RenameMemoControl.iteration_uniform.
        destruct (ready f model Hrelated) as [Hmeta Hzero].
        rewrite (RenameMemoControl.generated_iteration_empty f observations Hmeta (Hzero Hempty)). reflexivity.
      * split; [exact Hrelated|]. split; [exact Hempty|]. split; [exact Hreach|lia].
    + assert (Hnonempty : RenameMemoSchedule.stack model<>[]) by congruence.
      destruct (advance steps f model Hreach Hrelated Hnonempty observations) as [after [next [Hrun [Hmove Hnext]]]].
      assert (Hreach_next : RenameMemoSchedule.reached graph root base (S steps) next).
      { now apply RenameMemoSchedule.reached_step with (before:=model). }
      destruct (IH (S steps) after next ltac:(lia) Hreach_next Hnext observations)
        as [final [finished [final_steps [Hloop [Hfinal [Hfinished_empty [Hfinished Hsteps]]]]]]].
      exists final,finished,final_steps. split.
      * rewrite loop_S,local_bind,RenameMemoControl.iteration_uniform,Hrun. exact Hloop.
      * split; [exact Hfinal|]. split; [exact Hfinished_empty|]. split; [exact Hfinished|lia].
Qed.
Theorem initial f : related f (RenameMemoSchedule.config [] [] [RenameMemoSchedule.visit root base] 0 0) ->
  forall observations, exists final finished final_steps,
    execLocalObserved (loop (RenameMemoBounds.fuel root) RenameMemoControl.iteration_at) (f,observations)=Some (tt,(final,observations)) /\
    related final finished /\ RenameMemoSchedule.stack finished=[] /\
    RenameMemoSchedule.reached graph root base final_steps finished.
Proof.
  intros Hrelated observations.
  destruct (finite (RenameMemoBounds.fuel root) 0 f _ ltac:(lia) (RenameMemoSchedule.reached_initial graph root base) Hrelated observations)
    as [final [finished [final_steps [Hrun [Hfinal [Hempty [Hreach Hsteps]]]]]]].
  exists final,finished,final_steps. repeat split; assumption.
Qed.
Theorem body f :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__rename_node=Z.of_nat root -> Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  related (RenameMemoControl.prepared (setMachine f (RenameMemoInit.initialized (machine f))) root)
    (RenameMemoSchedule.config [] [] [RenameMemoSchedule.visit root base] 0 0) ->
  forall observations, exists final finished final_steps,
    execLocalObserved funcdef_0__rename_body (f,observations)=Some (tt,(final,observations)) /\
    related final finished /\ RenameMemoSchedule.stack finished=[] /\
    RenameMemoSchedule.reached graph root base final_steps finished.
Proof.
  intros Hmeta Hnode Hfuel Hrelated observations.
  destruct (initial _ Hrelated observations) as [final [finished [final_steps [Hrun [Hfinal [Hempty Hreach]]]]]].
  exists final,finished,final_steps. split.
  - rewrite RenameMemoControl.generated_initialized_preparation with (root:=root) by assumption.
    transitivity (optionBind (Some (tt,(final,observations)))
      (fun response=>execLocalObserved RenameMemoControl.finish (snd response))).
    + exact (f_equal (fun result=>optionBind result (fun response=>execLocalObserved RenameMemoControl.finish (snd response))) Hrun).
    + cbn [optionBind fst snd].
      destruct (ready final finished Hfinal) as [Hfinalmeta Hzero].
      exact (RenameMemoControl.generated_finish_empty final observations Hfinalmeta (Hzero Hempty)).
  - repeat split; assumption.
Qed.
Theorem generated s bs ns :
  (31<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__rename_node=Z.of_nat root -> Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  related (RenameMemoControl.prepared
    (setMachine {|machine:=s;bools:=bs;nums:=ns|} (RenameMemoInit.initialized s)) root)
    (RenameMemoSchedule.config [] [] [RenameMemoSchedule.visit root base] 0 0) ->
  forall observations, exists final finished final_steps,
    execObserved (funcdef_0__rename bs ns) (s,observations)=Some (tt,(machine final,observations)) /\
    related final finished /\ RenameMemoSchedule.stack finished=[] /\
    RenameMemoSchedule.reached graph root base final_steps finished.
Proof.
  intros Hmeta Hnode Hfuel Hrelated observations.
  destruct (body {|machine:=s;bools:=bs;nums:=ns|} Hmeta Hnode Hfuel Hrelated observations)
    as [final [finished [final_steps [Hrun [Hfinal [Hempty Hreach]]]]]].
  exists final,finished,final_steps. split.
  - unfold funcdef_0__rename. rewrite ObservedLocal.eliminate_correct,Hrun. reflexivity.
  - repeat split; assumption.
Qed.
End Composition.
End RenameMemoLoop.
