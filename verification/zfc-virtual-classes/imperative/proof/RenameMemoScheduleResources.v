From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Stack RenameStack RenameFrames RenameMemoInvariant RenameMemoBounds RenameMemoWork
  RenameMemoSchedule RenameMemoResourceBounds RenameMemoDomain RenameMemoIndexBounds RenameMemoState
  RenameMemoInit RenameMemoControl RenameMemoStack.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoScheduleResources.
Import IndexExecution SipHashExecution.
(* These are quantitative representation facts about a partial native run.
   They contain neither an execution nor its desired semantic conclusion. *)
Record accounting s (fs : list SetTheory.formula) (tasks : list RenameStack.frame)
  (model : RenameMemoSchedule.state) initial_length : Prop := {
  live_account : meta_value s 30<=Z.of_nat (length (RenameMemoSchedule.completed model));
  arena_account : (length fs+length (RenameMemoSchedule.active (RenameMemoSchedule.stack model))
    <=initial_length+length (RenameMemoSchedule.visited model))%nat;
  stack_account : length tasks=length (RenameMemoSchedule.stack model)
}.
Theorem initial s fs source base root : meta_value s 30=0 ->
  accounting s fs [RenameStack.visit source base]
    (RenameMemoSchedule.config [] [] [RenameMemoSchedule.visit root base] 0 0) (length fs).
Proof.
  intro Hlive. constructor; cbn [RenameMemoSchedule.completed RenameMemoSchedule.active RenameMemoSchedule.stack
    RenameMemoSchedule.visited length]; [rewrite Hlive; lia|lia|reflexivity].
Qed.
Theorem prepared (f : RenameMemoInit.Frame) fs source base root :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  accounting (machine (RenameMemoControl.prepared
    (setMachine f (RenameMemoInit.initialized (machine f))) root)) fs [RenameStack.visit source base]
    (RenameMemoSchedule.config [] [] [RenameMemoSchedule.visit root base] 0 0) (length fs).
Proof.
  intro Hmeta. apply initial.
  change (meta_value (StackExecution.push_state (RenameMemoInit.initialized (machine f)) 0
    (Z.of_nat root) (nums f vardef_0__rename_initialDepth)) 30=0).
  pose proof (RenameMemoStack.push_frame (RenameMemoInit.initialized (machine f)) 0
    (Z.of_nat root) (nums f vardef_0__rename_initialDepth)) as [_ [Hmetadata _]].
  rewrite Hmetadata by lia. now apply RenameMemoInit.initialized_count.
Qed.
Theorem ready s fs rho count tasks value target model initial_length :
  RenameMemoState.represents s fs rho count tasks value target ->
  accounting s fs tasks model initial_length ->
  (10<length (memory s arraydef_0__meta))%nat /\
  (RenameMemoSchedule.stack model=[] -> meta_value s 10=0).
Proof.
  intros Hstate Haccount. split.
  - pose proof (RenameMemoInvariant.metadata_ready _ _ _ (RenameMemoState.cache _ _ _ _ _ _ _ Hstate)). lia.
  - intro Hempty. destruct (RenameMemoState.frames _ _ _ _ _ _ _ Hstate) as [Hcount _].
    rewrite Hcount,(stack_account _ _ _ _ _ Haccount),Hempty. reflexivity.
Qed.
Theorem arena_bound s fs tasks model initial_length root base :
  accounting s fs tasks model initial_length -> RenameMemoSchedule.invariant root base model ->
  Z.of_nat initial_length+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  Z.of_nat (length fs)<=RenameMemoResourceBounds.doubling_limit.
Proof.
  intros Haccount Hmodel Hroom. eapply (RenameMemoResourceBounds.arena_room initial_length
    (length (RenameMemoSchedule.visited model)) (length (RenameMemoSchedule.active (RenameMemoSchedule.stack model))) (length fs) root).
  - exact (arena_account _ _ _ _ _ Haccount).
  - exact (RenameMemoSchedule.fresh_bound root base model Hmodel).
  - exact Hroom.
Qed.
Theorem live_bound s fs tasks model initial_length root base :
  accounting s fs tasks model initial_length -> RenameMemoSchedule.invariant root base model ->
  meta_value s 30<=Z.of_nat (S root*S root).
Proof.
  intros Haccount Hmodel. destruct (RenameMemoSchedule.accounting_bound root base model Hmodel) as [_ Hputs].
  pose proof (live_account _ _ _ _ _ Haccount). lia.
Qed.
Theorem resources s fs tasks model initial_length graph root base steps m shift arg count bound ceiling :
  accounting s fs tasks model initial_length -> RenameMemoWork.older graph ->
  RenameMemoSchedule.reached graph root base steps model ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  Z.of_nat initial_length+Z.of_nat (S root*S root)<=RenameMemoResourceBounds.doubling_limit ->
  word (Z.of_nat shift) -> word (Z.of_nat arg) -> RenameMemoDomain.source_domain bound ceiling tasks ->
  Z.of_nat bound+Z.of_nat (RenameMemoIndexBounds.increment m shift arg)<=maximum ->
  Z.of_nat ceiling<=maximum -> RenameMemoState.resources s fs m shift arg count tasks.
Proof.
  intros Haccount Hgraph Hreach Hfuel Hroom Hshift Harg Hdomain Hindices Hceiling.
  pose proof (RenameMemoSchedule.reached_invariant _ _ _ _ _ Hgraph Hreach) as Hmodel.
  apply RenameMemoDomain.resources with (root:=root) (bound:=bound) (ceiling:=ceiling); try assumption.
  - exact (arena_bound _ _ _ _ _ _ _ Haccount Hmodel Hroom).
  - rewrite (stack_account _ _ _ _ _ Haccount). now apply RenameMemoSchedule.stack_bound with (base:=base).
  - exact (live_bound _ _ _ _ _ _ _ Haccount Hmodel).
Qed.
End RenameMemoScheduleResources.
