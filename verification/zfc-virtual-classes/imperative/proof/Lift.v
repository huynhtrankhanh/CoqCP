From CoqCP Require Import Options SetTheory Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow.
From Stdlib Require Import Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers list.

Module IndexSemantics.
Import IndexExecution.
Definition renaming m shift arg : nat -> nat :=
  match m with
  | shift_mode => fun n => n + shift
  | instantiate_mode => SetTheory.instantiate arg
  | separation_mode => SetTheory.sep_rename
  | replacement_left_mode => SetTheory.repl_left
  | replacement_right_mode => SetTheory.repl_right
  | replacement_image_mode => SetTheory.repl_image
  | predicate_mode => fun n => match n with 0 => arg | S n => n + shift end
  end.

Fixpoint under_binders depth (rho : nat -> nat) :=
  match depth with 0 => rho | S depth => SetTheory.up (under_binders depth rho) end.
Theorem bound_index depth rho i : (i < depth)%nat -> under_binders depth rho i = i.
Proof.
  induction depth as [| depth IH] in i |- *; [lia |].
  destruct i as [|i]; cbn [under_binders SetTheory.up]; [reflexivity |].
  intro H. f_equal. apply IH. lia.
Qed.
Theorem free_index depth rho n :
  under_binders depth rho (depth + n) = (depth + rho n)%nat.
Proof.
  induction depth as [|depth IH]; cbn [under_binders SetTheory.up Nat.add]; [reflexivity |].
  now rewrite IH.
Qed.

Theorem free_index_semantics m n shift arg :
  IndexExecution.free_index m (Z.of_nat n) (Z.of_nat shift) (Z.of_nat arg) =
  Z.of_nat (renaming m shift arg n).
Proof.
  destruct m; destruct n as [|[|n]];
    cbn [renaming IndexExecution.free_index SetTheory.instantiate
      SetTheory.sep_rename SetTheory.repl_left SetTheory.repl_right SetTheory.repl_image].
  all: repeat first [rewrite bool_decide_true by lia | rewrite bool_decide_false by lia
    | rewrite Nat2Z.inj_add | rewrite Nat2Z.inj_succ].
  all: lia.
Qed.

Theorem index_semantics m i depth shift arg :
  renamed_index m (Z.of_nat i) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg) =
  Z.of_nat (under_binders depth (renaming m shift arg) i).
Proof.
  unfold renamed_index. destruct (Nat.lt_ge_cases i depth) as [Hbound | Hfree].
  - rewrite bool_decide_true by lia. rewrite bound_index by exact Hbound. reflexivity.
  - rewrite bool_decide_false by lia.
    replace i with (depth + (i - depth))%nat at 2 by lia.
    rewrite free_index.
    replace (Z.of_nat i - Z.of_nat depth)%Z with (Z.of_nat (i - depth))
      by (rewrite Nat2Z.inj_sub by lia; reflexivity).
    rewrite free_index_semantics, Nat2Z.inj_add. lia.
Qed.

Theorem generated_index_correct s m i depth shift arg :
  (8 < length (Execution.memory s arraydef_0__meta))%nat ->
  word (Z.of_nat i) -> word (Z.of_nat depth) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
  exists final,
    Execution.exec (funcdef_0__renameIndex (fun _ => false)
      (arguments (Z.of_nat i) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg))) s =
      Some (tt, final) /\
    result s final (Z.of_nat (under_binders depth (renaming m shift arg) i)).
Proof.
  rewrite <- index_semantics. apply index_execution.
Qed.

Theorem generated_checked_index s m i depth shift arg :
  (8 < length (Execution.memory s arraydef_0__meta))%nat ->
  word (Z.of_nat i) -> word (Z.of_nat depth) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  exists final,
    Execution.exec (funcdef_0__renameIndex (fun _ => false)
      (arguments (Z.of_nat i) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg))) s =
      Some (tt, final) /\
    (List.nth 8 (Execution.memory final arraydef_0__meta) 0%Z = 0%Z ->
      word (Z.of_nat (under_binders depth (renaming m shift arg) i)) /\
      result s final (Z.of_nat (under_binders depth (renaming m shift arg) i))) /\
    (~ word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
      List.nth 8 (Execution.memory final arraydef_0__meta) 0%Z = 1%Z).
Proof.
  rewrite <- index_semantics. apply OverflowExecution.checked_index.
Qed.
End IndexSemantics.
