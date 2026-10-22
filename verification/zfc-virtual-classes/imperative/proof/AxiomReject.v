From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Representation
  RenameMemoControl RenameStorage.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomReject.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom.
Definition result s := store_meta s 13 0.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
(* The dispatcher has exactly the eighteen object-language axiom selectors
   listed in the protocol. A selector outside that range cannot set success. *)
Theorem generated_body (f : Frame) observations :
  (13 < length (memory (machine f) arraydef_0__meta))%nat ->
  (nums f vardef_0__axiom_tag < 0 \/ 18 <= nums f vardef_0__axiom_tag) ->
  execLocalObserved funcdef_0__axiom_body (f,observations) =
    Some (tt,(setMachine f (result (machine f)),observations)).
Proof.
  intros Hmeta Htag. destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold funcdef_0__axiom_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hmeta)
    |match goal with |- context [bool_decide ?P] => progress rewrite (bool_decide_false P) by lia end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
  ]. reflexivity.
Qed.
Theorem generated s bs ns observations :
  (13 < length (memory s arraydef_0__meta))%nat ->
  (ns vardef_0__axiom_tag < 0 \/ 18 <= ns vardef_0__axiom_tag) ->
  execObserved (funcdef_0__axiom bs ns) (s,observations) = Some (tt,(result s,observations)).
Proof.
  intros Hmeta Htag. unfold funcdef_0__axiom. rewrite ObservedLocal.eliminate_correct.
  pose proof (generated_body {|machine:=s;bools:=bs;nums:=ns|} observations Hmeta Htag) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
Theorem rejected_flag s : (13 < length (memory s arraydef_0__meta))%nat -> meta_value (result s) 13 = 0.
Proof. intro Hmeta. unfold result. now apply meta_store_same. Qed.
Theorem preserves s fs : NativeRepresentation.canonical_arena s fs ->
  NativeRepresentation.canonical_arena (result s) fs /\ meta_value (result s) 8 = meta_value s 8.
Proof.
  intro Harena. split.
  - apply (ArenaFrame.storage_arena s); [unfold result; apply ArenaFrame.storage_meta; lia|exact Harena].
  - unfold result. apply meta_store_other. lia.
Qed.
End AxiomReject.
