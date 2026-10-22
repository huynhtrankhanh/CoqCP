From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index Lift RenameStack RenameMemoState.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Module RenameMemoIndexBounds.
Import IndexExecution IndexSemantics.
Definition increment m shift arg := match m with
  | shift_mode=>shift | instantiate_mode=>arg | separation_mode=>1
  | replacement_left_mode | replacement_right_mode=>2 | replacement_image_mode=>1
  | predicate_mode=>Nat.max shift arg end.
Theorem renaming_bound m shift arg index : renaming m shift arg index<=index+increment m shift arg.
Proof.
  destruct m; destruct index as [|[|index]];
    cbn [renaming increment SetTheory.instantiate SetTheory.sep_rename SetTheory.repl_left SetTheory.repl_right SetTheory.repl_image];
    try lia; pose proof (Nat.le_max_l shift arg); pose proof (Nat.le_max_r shift arg); lia.
Qed.
Theorem binder_bound depth m shift arg index :
  under_binders depth (renaming m shift arg) index<=index+increment m shift arg.
Proof.
  induction depth as [|depth IH] in index |- *; [apply renaming_bound|].
  destruct index as [|index]; cbn [under_binders SetTheory.up]; [lia|]. pose proof (IH index). lia.
Qed.
Fixpoint formula_bound bound p : Prop := match p with
  | SetTheory.falsity=>True
  | SetTheory.equal i j | SetTheory.member i j=>i<=bound /\ j<=bound
  | SetTheory.implies p q=>formula_bound bound p /\ formula_bound bound q
  | SetTheory.all p=>formula_bound bound p end.
Definition source task := match task with
  | RenameStack.visit p _=>p
  | RenameStack.left_done p q _ | RenameStack.right_done p q _ _=>SetTheory.implies p q
  | RenameStack.body_done p _=>SetTheory.all p end.
Definition stack_bound bound stack := Forall (fun task=>formula_bound bound (source task)) stack.
Theorem atom_words bound m shift arg source depth : formula_bound bound source ->
  (Z.of_nat bound+Z.of_nat (increment m shift arg)<=maximum)%Z ->
  (match source with SetTheory.all _=>False | _=>True end) ->
  RenameMemoState.atomic_bounds m shift arg source depth.
Proof.
  destruct source as [|i j|i j|p q|p]; cbn [formula_bound RenameMemoState.atomic_bounds]; try tauto.
  all: intros [Hi Hj] Hroom _; pose proof (binder_bound depth m shift arg i); pose proof (binder_bound depth m shift arg j);
    unfold word; repeat split; lia.
Qed.
End RenameMemoIndexBounds.
