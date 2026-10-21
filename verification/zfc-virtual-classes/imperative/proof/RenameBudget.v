From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal RenameStructure.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers list.

(* Reduce the actual eight nested native loops to the remaining obligation:
   one active iteration must preserve its semantic invariant and decrease its
   pending-work rank by one. This does not assume a whole helper execution. *)
Module RenameBudget.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Section Progress.
Variable Ghost : Type.
Variable invariant : Frame -> Ghost -> Prop.
Variable rank : Ghost -> nat.
Hypothesis ready : forall f g, invariant f g ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat /\
  (meta_value (machine f) 10 = 0%Z <-> rank g = 0%nat) /\ meta_value (machine f) 8 = 0%Z.
Hypothesis advance : forall f g observations, invariant f g -> (0 < rank g)%nat ->
  exists final next, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    invariant final next /\ rank next = (rank g - 1)%nat.
Definition progresses (work : LocalAction unit) budget := forall f g observations, invariant f g ->
  exists final next, execLocalObserved work (f,observations) = Some (tt,(final,observations)) /\
    invariant final next /\ rank next = (rank g - budget)%nat.
Theorem iteration_loop_progress fuel : progresses (loop fuel (fun _ => iteration)) fuel.
Proof.
  induction fuel as [|fuel IH]; intros f g observations Hinv.
  - exists f, g. split; [reflexivity|]. split; [exact Hinv|lia].
  - destruct (ready f g Hinv) as [Hmeta [Hempty Herror]]. rewrite loop_S,local_bind.
    destruct (Nat.eq_dec (rank g) 0) as [Hzero|Hpositive].
    + rewrite (generated_iteration_empty f observations Hmeta (proj2 Hempty Hzero)).
      exists f, g. split; [reflexivity|]. split; [exact Hinv|lia].
    + destruct (advance f g observations Hinv ltac:(lia)) as [middle [middle_ghost [Hrun [Hmiddle Hrank]]]].
      rewrite Hrun. cbn [optionBind fst snd].
      destruct (IH middle middle_ghost observations Hmiddle) as [final [final_ghost [Hfinal [Hinvfinal Hrankfinal]]]].
      exists final, final_ghost. split; [exact Hfinal|]. split; [exact Hinvfinal|lia].
Qed.
Theorem layer_loop_progress work budget : progresses work budget -> forall fuel,
  progresses (loop fuel (fun _ => layer work)) (fuel * budget)%nat.
Proof.
  intros Hwork fuel. induction fuel as [|fuel IH]; intros f g observations Hinv.
  - exists f, g. split; [reflexivity|]. split; [exact Hinv|lia].
  - destruct (ready f g Hinv) as [Hmeta [Hempty Herror]]. rewrite loop_S,local_bind.
    destruct (Nat.eq_dec (rank g) 0) as [Hzero|Hpositive].
    + rewrite (generated_layer_empty work f observations Hmeta (proj2 Hempty Hzero)).
      exists f, g. split; [reflexivity|]. split; [exact Hinv|lia].
    + rewrite (generated_layer_active work f observations Hmeta ltac:(intros H; apply Hpositive; now apply Hempty) Herror).
      destruct (Hwork f g observations Hinv) as [middle [middle_ghost [Hrun [Hmiddle Hrank]]]].
      rewrite Hrun. cbn [optionBind fst snd].
      destruct (IH middle middle_ghost observations Hmiddle) as [final [final_ghost [Hfinal [Hinvfinal Hrankfinal]]]].
      exists final, final_ghost. split; [exact Hfinal|]. split; [exact Hinvfinal|]. cbn [Nat.mul]. lia.
Qed.
Theorem outer_layers_progress depth work budget : progresses work budget ->
  progresses (outer_layers depth work) (Nat.pow limit depth * budget)%nat.
Proof.
  intros Hwork. induction depth as [|depth IH]; [cbn [Nat.pow Nat.mul Nat.add outer_layers]; rewrite Nat.add_0_r; exact Hwork|].
  change (progresses (loop limit (fun _ => layer (outer_layers depth work))) (Nat.pow limit (S depth) * budget)%nat).
  replace (Nat.pow limit (S depth) * budget)%nat with (limit * (Nat.pow limit depth * budget))%nat by (cbn [Nat.pow]; nia).
  now apply layer_loop_progress.
Qed.
Theorem traversal_progress : progresses traversal (Nat.pow limit 8).
Proof.
  rewrite traversal_structure.
  replace (Nat.pow limit 8) with (Nat.pow limit 7 * limit)%nat by (rewrite (Nat.pow_succ_r' limit 7); nia).
  apply outer_layers_progress. apply iteration_loop_progress.
Qed.
Theorem traversal_complete f g observations : invariant f g -> (rank g <= Nat.pow limit 8)%nat ->
  exists final next, execLocalObserved traversal (f,observations) = Some (tt,(final,observations)) /\
    invariant final next /\ rank next = 0%nat /\ meta_value (machine final) 10 = 0%Z.
Proof.
  intros Hinv Hbudget. destruct (traversal_progress f g observations Hinv) as [final [next [Hrun [Hfinal Hrank]]]].
  assert (Hzero : rank next = 0%nat) by lia.
  exists final, next. split; [exact Hrun|]. split; [exact Hfinal|]. split; [exact Hzero|].
  apply (proj2 (proj1 (proj2 (ready final next Hfinal)))). exact Hzero.
Qed.
End Progress.
Theorem actual_work_budget : Z.of_nat (Nat.pow limit 8) = (2^256)%Z.
Proof.
  rewrite Nat2Z.inj_pow. unfold limit. rewrite Z2Nat.id by lia. vm_compute. reflexivity.
Qed.
End RenameBudget.
