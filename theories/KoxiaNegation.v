From CoqCP Require Import Options Imperative Execution KoxiaNTT KoxiaArrays KoxiaTables SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.

Fixpoint negatedValues count values size :=
  match count with O => values | S count =>
    swappedWork (negatedValues count values size) (S count) (size-S count) end.
Lemma negatedValues_length count values size : length (negatedValues count values size)=length values.
Proof. induction count as [|count IH]; cbn [negatedValues]; rewrite ?swappedWork_length,?IH; reflexivity. Qed.
Definition negatedIndex count size index :=
  bool_decide (((0<index<=count)%nat) \/ ((size-count<=index<size)%nat)).
Theorem negatedValues_lookup count values size index : (2*count<size<=length values)%nat ->
  nth index (negatedValues count values size) 0=
    if negatedIndex count size index then nth (size-index) values 0 else nth index values 0.
Proof.
  induction count as [|count IH] in index |- *.
  - intros room. cbn [negatedValues]. unfold negatedIndex. rewrite bool_decide_false by lia. reflexivity.
  - intros room. cbn [negatedValues]. rewrite nth_swappedWork by (rewrite negatedValues_length; lia).
    destruct (Nat.eq_dec index (S count)) as [left|notLeft].
    + subst index. rewrite Nat.eqb_refl,IH by lia. unfold negatedIndex.
      rewrite bool_decide_false by lia. rewrite bool_decide_true by lia. reflexivity.
    + rewrite (proj2 (Nat.eqb_neq _ _) notLeft).
      destruct (Nat.eq_dec index ((size-S count)%nat)) as [right|notRight].
      * subst index. rewrite Nat.eqb_refl,IH by lia. unfold negatedIndex.
        rewrite bool_decide_false by lia. rewrite bool_decide_true by lia.
        replace (size-(size-S count))%nat with (S count) by lia. reflexivity.
      * rewrite (proj2 (Nat.eqb_neq _ _) notRight),IH by lia.
        unfold negatedIndex. rewrite (bool_decide_ext
          (((0<index<=count)%nat) \/ ((size-count<=index<size)%nat))
          (((0<index<=S count)%nat) \/ ((size-S count<=index<size)%nat))) by lia. reflexivity.
Qed.
Theorem negatedValues_complete values size index : (0<size<=length values)%nat -> (index<size)%nat ->
  nth index (negatedValues ((size-1)/2) values size) 0=nth ((size-index) mod size) values 0.
Proof.
  intros room inside. pose proof (Nat.div_mod (size-1) 2 ltac:(lia)) as quotient.
  pose proof (Nat.mod_upper_bound (size-1) 2 ltac:(lia)) as remainder.
  rewrite negatedValues_lookup by lia. unfold negatedIndex.
  destruct (bool_decide (((0<index<=(size-1)/2)%nat) \/ ((size-(size-1)/2<=index<size)%nat))) eqn:processed.
  - apply bool_decide_eq_true in processed. rewrite Nat.mod_small by lia. reflexivity.
  - apply bool_decide_eq_false in processed.
    destruct (Nat.eq_dec index (0%nat)) as [zero|nonzero].
    + subst index. rewrite Nat.sub_0_r,Nat.mod_same by lia. reflexivity.
    + assert (middle : (size-index)%nat=index) by lia. rewrite middle,Nat.mod_small by exact inside. reflexivity.
Qed.
Lemma swappedWork_canonical values left right : tableCanonical values ->
  (left<length values)%nat -> (right<length values)%nat -> tableCanonical (swappedWork values left right).
Proof.
  intros canonical leftRoom rightRoom. unfold swappedWork,tableCanonical in *.
  apply Forall_insert; [|apply tableCanonical_nth; assumption].
  apply Forall_insert; [exact canonical|apply tableCanonical_nth; assumption].
Qed.
Lemma negatedValues_canonical count values size : (2*count<size<=length values)%nat ->
  tableCanonical values -> tableCanonical (negatedValues count values size).
Proof.
  induction count as [|count IH]; [intros; assumption|]. intros room canonical.
  cbn [negatedValues]. apply swappedWork_canonical.
  - apply IH; [lia|exact canonical].
  - rewrite negatedValues_length; lia.
  - rewrite negatedValues_length; lia.
Qed.
Fixpoint negateAction fuel total size tmp : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue Z :=
  match fuel with
  | O => Done _ _ _ tmp
  | S fuel => let left := (S (total-fuel-1))%nat in
    nttSwap (Z.of_nat left) (Z.of_nat (size-left)) tmp >>= fun saved => negateAction fuel total size saved
  end.
Theorem negateAction_execution fuel count total size tmp state values :
  (count+fuel=total)%nat -> (2*total<size<=length values)%nat ->
  exists saved, exec (negateAction fuel total size tmp) (withWork state (negatedValues count values size))=
    Some (saved,withWork state (negatedValues total values size)).
Proof.
  induction fuel as [|fuel IH] in count,tmp |- *.
  - intros countFuel room. assert (count=total) by lia. subst count. eexists. reflexivity.
  - intros countFuel room. cbn [negateAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,nttSwap_execution by (rewrite negatedValues_length; lia).
    rewrite bool_decide_true by lia. cbn [optionBind fst snd].
    apply (IH (S count)); [lia|exact room].
Qed.
