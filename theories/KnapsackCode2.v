From stdpp Require Import numbers list.
From CoqCP Require Import Options Imperative Knapsack KnapsackCode.
From Generated Require Import Knapsack.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Logic.FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma nthGenerateData (items : list (nat * nat)) (limit x : nat) : nth (8 * length items + x) (generateData items limit) (0%Z) = nth x (to32 limit) 0%Z.
Proof.
  unfold generateData. rewrite nth_lookup lookup_app_r.
  { rewrite serializeWeightsLength. lia. }
  rewrite lookup_app_r.
  { rewrite serializeWeightsLength serializeValuesLength. lia. }
  rewrite -nth_lookup serializeWeightsLength serializeValuesLength (ltac:(lia) : (8 * length items + x - 4 * length items - 4 * length items = x)%nat). reflexivity.
Qed.

Lemma nthGenerateData2 (items : list (nat * nat)) (limit x : nat) p : nth_lt (generateData items limit) (8 * length items + x) p = nth x (to32 limit) 0%Z.
Proof.
  rewrite (nth_lt_default _ _ _ 0%Z) nthGenerateData. reflexivity.
Qed.

Lemma extractAnswerEq (items : list (nat * nat)) (notNil : items <> []) (limit : nat) (hp : ((limit + 1%nat) * (length items + 1%nat) <= 1000000%nat)%nat) (a32 : forall x, (fst (nth x items (0%nat,0%nat)) < 2^32)%nat) (b32 : forall x, (snd (nth x items (0%nat,0%nat)) < 2^32)%nat) : extractAnswer (start items limit) = Z.of_nat (knapsack items limit).
Proof.
  unfold start, invokeContract, state at 1. case_decide as uu; [| easy].
  fold state.
  unfold funcdef_0__main at 2. unfold divIntUnsigned, subInt at 1. rewrite !leftIdentity. unfold getCommunicationSize. rewrite pushDispatch2 unfoldInvoke_S_GetCommunicationSize pushDispatch unfoldInvoke_S_Store. case_decide as wk; [| simpl in wk; lia].
  assert (sh : Z.of_nat 1000000 = 1000000%Z). { 
    unfold Init.Nat.of_num_uint, Init.Nat.of_uint, Init.Nat.of_uint_acc, Init.Nat.tail_mul.
    rewrite !Nat.tail_addmul_spec. lia. }
  assert (hv : Z.of_nat (length items) <= 999999).
  { lia. }
  assert (hl : Z.of_nat (limit) <= 999999). { lia. }
  assert (ea : (λ _0 : arrayIndex0,
  match decide (_0 = arraydef_0__n) with
  | left _1 =>
      eq_rect_r
        (λ _2 : arrayIndex0, list (arrayType arrayIndex0 environment0 _2))
        (<[Z.to_nat 0:=coerceInt
                         (Z.of_nat (length (generateData items limit)) - 4) 64
                       `div` 8]> (arrays arrayIndex0 environment0 arraydef_0__n))
        _1
  | right _ => arrays arrayIndex0 environment0 _0
  end )= λ _0 : arrayIndex0,
  match _0 with
  | arraydef_0__n => [Z.of_nat (length items)]
  | arraydef_0__dp => repeat 0%Z 1000000
  | arraydef_0__message => [0%Z]
  end).
  { apply functional_extensionality_dep. intro j.
    destruct j. { easy. } { easy. }
    simpl. rewrite dataLength. unfold coerceInt.
    rewrite Z.mod_small. { lia. }
    rewrite (ltac:(lia) : (Z.of_nat (8 * length items + 4) - 4) = (Z.of_nat (length items) * 8)%Z) Z.div_mul. { clear. easy. } { clear. easy. } } rewrite ea. clear ea.
  rewrite eliminateLift. unfold funcdef_0__getlimit. rewrite !leftIdentity.
  unfold addInt, multInt at 1. unfold addInt, multInt at 1. unfold addInt, multInt at 1. unfold addInt, multInt at 1. unfold addInt, multInt at 1. unfold addInt, multInt at 1. unfold addInt, multInt at 1. unfold addInt, multInt at 1. rewrite !leftIdentity.
  (* first byte *)
  (* use this as a model for subsequent bytes *)
  unfold retrieve at 1. rewrite -!bindAssoc pushDispatch bindDispatch.
  rewrite unfoldInvoke_S_Retrieve. case_decide as tr; [| simpl in tr; lia].
  rewrite (ltac:(simpl; unfold coerceInt; rewrite Z.mod_small; lia) : coerceInt (8 * nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tr) 64 = (8 * Z.of_nat (length items))%Z) !leftIdentity.
  unfold readByte. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte. clear tr.
  case_decide as tr; [| rewrite dataLength in tr; lia].
  rewrite (ltac:(lia) : Z.to_nat (8 * Z.of_nat (length items)) = (8 * length items + 0))%nat nthGenerateData.
  assert (st : coerceInt (nth 0 (to32 limit) 0) 32 = Z.of_nat (limit / (2^24))).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 0 [a; b; c; d] e = a) Z.mod_small.
  { constructor. { lia. }
    destruct (decide (limit = 0%nat)) as [pp | pp].
    { rewrite pp. easy. }
    assert (jj : (limit `div` 2 ^ 24 < limit)%nat).
    { apply Nat.div_lt. { lia. }
      apply Nat.pow_gt_1; clear; lia. }
    lia. } reflexivity. } rewrite st !leftIdentity.
Admitted.