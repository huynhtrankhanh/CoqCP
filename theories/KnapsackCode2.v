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

Lemma nthGenerateDataWeight (items : list (nat * nat)) (limit x index : nat) (hx : (x < 4)%nat) (hIndex : (index < length items)%nat) : nth (4 * index + x) (generateData items limit) (0%Z) = nth x (to32 (fst (nth index items (0%nat,0%nat)))) 0%Z.
Proof.
  unfold generateData. rewrite nth_lookup lookup_app_l.
  { rewrite serializeWeightsLength. lia. }
  rewrite -nth_lookup. clear limit.
  revert index hIndex. induction items as [| head tail IH]. { easy. }
  intro n.
  destruct head as [weight value].
  rewrite (ltac:(simpl; reflexivity) : length ((weight, value) :: tail) = (1 + length tail)%nat) (ltac:(clear; easy) : serializeWeights ((weight, value) :: tail) = to32 weight ++ serializeWeights tail).
  destruct n as [| n].
  - intro j. rewrite (ltac:(clear; lia) : (4 * 0 + x = x)%nat).
    rewrite nth_lookup lookup_app_l. { unfold to32. rewrite (ltac:(easy) : forall a b c d, (length [a; b; c; d] = 4)%nat). exact hx. }
    rewrite (ltac:(easy) : (nth 0 ((weight, value) :: tail) (0%nat, 0%nat)).1 = weight). rewrite -nth_lookup. reflexivity.
  - intro j. rewrite (ltac:(lia) : (4 * S n + x = 4 + (4 * n + x))%nat).
    rewrite !nth_lookup lookup_app_r.
    { unfold to32. rewrite (ltac:(easy) : forall a b c d, (length [a; b; c; d] = 4)%nat). lia. }
    rewrite (ltac:(unfold to32; rewrite (ltac:(easy) : forall a b c d, (length [a; b; c; d] = 4)%nat); lia) : (4 + (4 * n + x) - length (to32 weight))%nat = (4 * n + x)%nat) (ltac:(easy) : ((weight, value) :: tail) !! S n = tail !! n) -!nth_lookup. apply IH. lia.
Qed.

Lemma readWeight (items : list (nat * nat)) (hl : Z.of_nat (length items) < 2^32) (limit : nat) (a32 : forall x, (fst (nth x items (0%nat,0%nat)) < 2^32)%nat) (b32 : forall x, (snd (nth x items (0%nat,0%nat)) < 2^32)%nat) whatever index (hZ : 0 <= index) (hIndex : (Z.to_nat index < length items)%nat) cont whatever2 whatever3 ol ju : invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__message => ol | arraydef_0__dp => ju | arraydef_0__n => [Z.of_nat (length items)] end) whatever (funcdef_0__getweight whatever2 (fun=> index) whatever3 >>= cont) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__message => [Z.of_nat (fst (nth (Z.to_nat index) items (0%nat,0%nat)))] | arraydef_0__dp => ju | arraydef_0__n => [Z.of_nat (length items)] end) whatever (cont tt).
Proof.
  unfold funcdef_0__getweight.
  unfold addInt, multInt. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  rewrite dataLength (ltac:(unfold coerceInt; rewrite Z.mod_small; lia) : (coerceInt (4 * index) 64 = 4 * index)%Z).

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
  clear tr.
  (* next byte *)
  unfold retrieve at 1. rewrite -!bindAssoc pushDispatch bindDispatch.
  rewrite unfoldInvoke_S_Retrieve. case_decide as tr; [| simpl in tr; lia].
  rewrite (ltac:(simpl; unfold coerceInt; rewrite Z.mod_small; lia) : coerceInt (8 * nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tr) 64 = (8 * Z.of_nat (length items))%Z) !leftIdentity.
  unfold readByte. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte. clear tr.
  rewrite (ltac:(simpl; unfold coerceInt; rewrite Z.mod_small; lia) : coerceInt (8 * Z.of_nat (length items) + 1) 64 = (8 * Z.of_nat (length items) + 1)%Z) !leftIdentity.
  case_decide as tr; [| rewrite dataLength in tr; lia].
  unfold retrieve at 1. rewrite -!bindAssoc pushDispatch bindDispatch.
  rewrite unfoldInvoke_S_Retrieve. clear tr. case_decide as tr; [| simpl in tr; lia].
  rewrite (ltac:(simpl; unfold coerceInt; rewrite Z.mod_small; lia) : coerceInt (8 * nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tr) 64 = (8 * Z.of_nat (length items))%Z) !leftIdentity.
  rewrite (ltac:(lia) : Z.to_nat (8 * Z.of_nat (length items) + 1) = (8 * length items) + 1)%nat nthGenerateData.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte. clear tr.
  case_decide as tr; [| simpl in tr; rewrite (ltac:(simpl; unfold coerceInt; rewrite Z.mod_small; lia) : coerceInt (8 * Z.of_nat (length items) + 2) 64 = (8 * Z.of_nat (length items) + 2)%Z) dataLength in tr; lia]. clear st.
  assert (st : coerceInt (nth 1 (to32 limit) 0) 32 = Z.of_nat (limit / (2^16) mod 256)).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 1 [a; b; c; d] e = b) Z.mod_small.
  { constructor. { lia. }
    rewrite Nat2Z.inj_mod.
    pose proof (proj2 (Z.mod_pos_bound (Z.of_nat (limit `div` 2 ^ 16)) (Z.of_nat 256) ltac:(easy))).
    lia. } reflexivity. } rewrite st !leftIdentity.
  unfold retrieve at 1. rewrite -!bindAssoc pushDispatch bindDispatch.
  rewrite unfoldInvoke_S_Retrieve. clear tr. case_decide as tr; [| simpl in tr; lia].
  rewrite !leftIdentity.
  assert (uw : coerceInt
  (coerceInt
     (8 * nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tr) 64 +
   3) 64 = (8 * Z.of_nat (length items) + 3)%Z).
  { unfold coerceInt. rewrite Z.mod_small; rewrite Z.mod_small; simpl; lia. } clear uw.
  rewrite -!bindAssoc pushDispatch bindDispatch.
  rewrite unfoldInvoke_S_ReadByte.
  case_decide as jj; [| simpl in jj; unfold coerceInt in jj; rewrite dataLength in jj; rewrite !Z.mod_small in jj; lia].
  rewrite !leftIdentity (ltac:(easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tr = Z.of_nat (length items)).
  clear st. assert (st : coerceInt (nth 2 (to32 limit) 0) 32 = Z.of_nat ((limit / (2^8)) mod 256)).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 2 [a; b; c; d] e = c) Z.mod_small.
  { constructor. { lia. }
    rewrite Nat2Z.inj_mod.
    pose proof (proj2 (Z.mod_pos_bound (Z.of_nat (limit `div` 2 ^ 8)) (Z.of_nat 256) ltac:(easy))).
    lia. } reflexivity. }
  assert (j1 : Z.to_nat (coerceInt (8 * Z.of_nat (length items) + 2) 64) = (8 * length items + 2)%nat).
  { unfold coerceInt. rewrite Z.mod_small; lia. } rewrite j1. clear j1.
  rewrite nthGenerateData st. clear st.
  assert (j1 : Z.to_nat (coerceInt (coerceInt (8 * Z.of_nat (length items)) 64 + 3) 64) = (8 * length items + 3)%nat).
  { unfold coerceInt. rewrite Z.mod_small; rewrite Z.mod_small; lia. } rewrite j1. clear j1.
  rewrite nthGenerateData.
  assert (st : coerceInt (nth 3 (to32 limit) 0) 32 = Z.of_nat (limit mod 256)).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 3 [a; b; c; d] e = d) Z.mod_small.
  { constructor. { lia. }
    rewrite Nat2Z.inj_mod.
    pose proof (proj2 (Z.mod_pos_bound (Z.of_nat limit) (Z.of_nat 256) ltac:(easy))).
    lia. } reflexivity. } rewrite st. clear st.
  assert (s1 : coerceInt (Z.land (1 ≪ 24) (Z.ones 64)) 32 = 2^24).
  { clear. easy. } rewrite s1. clear s1.
  rewrite (ltac:(clear; easy) : coerceInt (Z.land (1 ≪ 8) (Z.ones 64)) 32 = 2^8).
  rewrite (ltac:(clear; easy) : coerceInt (Z.land (1 ≪ 16) (Z.ones 64)) 32 = 2^16).
  assert (ut : (coerceInt
  (coerceInt
     (coerceInt
        (coerceInt (Z.of_nat (limit `div` 2 ^ 24) * 2 ^ 24) 32 +
         coerceInt (Z.of_nat ((limit `div` 2 ^ 16) `mod` 256) * 2 ^ 16)
           32) 32 +
      coerceInt (Z.of_nat ((limit `div` 2 ^ 8) `mod` 256) * 2 ^ 8) 32) 32 +
   Z.of_nat (limit `mod` 256)) 32) = Z.of_nat limit).
  { unfold coerceInt.
    rewrite !Nat2Z.inj_mod; (try rewrite !Nat2Z.inj_div).
    rewrite (ltac:(easy) : Z.of_nat 256 = 256).
    rewrite (ltac:(rewrite Nat2Z.inj_pow; clear; easy) : Z.of_nat (2 ^ 24) = 2^24) (ltac:(rewrite Nat2Z.inj_pow; clear; easy) : Z.of_nat (2 ^ 16) = 2^16).
    pose proof Z.div_le_mono _ _ (2 ^ 24) ltac:(clear; easy) hl as j1. simpl in j1. rewrite (ltac:(clear; easy) : 999999 `div` 2 ^ 24 = 0) in j1.
    pose proof Z.div_le_mono _ _ (2 ^ 16) ltac:(clear; easy) hl as j2. simpl in j2. rewrite (ltac:(clear; easy) : 999999 `div` 2 ^ 16 = 15) in j2.
    pose proof Z.div_le_mono _ _ (2 ^ 8) ltac:(clear; easy) hl as j3. simpl in j3. rewrite (ltac:(clear; easy) : 999999 `div` 2 ^ 8 = 3906) in j3.
    pose proof Z.mod_pos_bound (Z.of_nat limit `div` 2 ^ 24) 256 ltac:(clear; easy) as [y1 z1].
    pose proof Z.mod_pos_bound (Z.of_nat limit `div` 2 ^ 16) 256 ltac:(clear; easy) as [y2 z2].
    pose proof Z.mod_pos_bound (Z.of_nat limit `div` 2 ^ 8) 256 ltac:(clear; easy) as [y3 z3].
    pose proof Z.mod_pos_bound (Z.of_nat limit `div` 256) 256 ltac:(clear; easy) as [y4 z4].
    pose proof Z.mod_pos_bound (Z.of_nat limit) 256 ltac:(clear; easy) as [y5 z5].
    pose proof Z.div_le_mono _ _ (2 ^ 24) ltac:(clear; easy) (Zle_0_nat limit) as i1. simpl in i1. rewrite (ltac:(clear; easy) : 0 `div` 2 ^ 24 = 0) in i1.
    pose proof Z.div_le_mono _ _ (2 ^ 16) ltac:(clear; easy) (Zle_0_nat limit) as i2. simpl in i2. rewrite (ltac:(clear; easy) : 0 `div` 2 ^ 16 = 0) in i2.
    pose proof Z.div_le_mono _ _ (2 ^ 8) ltac:(clear; easy) (Zle_0_nat limit) as i3. simpl in i3. rewrite (ltac:(clear; easy) : 0 `div` 2 ^ 8 = 0) in i3.
    pose proof Z.div_le_mono _ _ 256 ltac:(clear; easy) (Zle_0_nat limit) as i4. simpl in i4. rewrite (ltac:(clear; easy) : 0 `div` 256 = 0) in i4.
    rewrite !(Z.mod_small _ (2^32)); try constructor; try lia.
    pose proof Z.div_mod (Z.of_nat limit) 256 ltac:(clear;easy) as ut.
    pose proof Z.div_mod (Z.of_nat limit `div` 256) 256 ltac:(clear;easy) as uy. rewrite (Z.div_div _ _ _) in uy. {clear;easy. }{clear;easy. } 
    pose proof Z.div_mod (Z.of_nat limit `div` (256*256)) 256 ltac:(clear;easy) as u8. rewrite (Z.div_div _ _ _) in u8. {clear;easy. }{clear;easy. } 
    pose proof Z.div_mod (Z.of_nat limit `div` (256*256*256)) 256 ltac:(clear;easy) as u7. rewrite (Z.div_div _ _ _) in u7. {clear;easy. }{clear;easy. } 

    assert (yu : Z.of_nat limit `mod` 2 ^ 24 = Z.of_nat limit).
    { rewrite Z.mod_small; lia. }
    rewrite -> (ltac:(clear;easy) : (2^8)%Z=(256)%Z) in *.
    rewrite -> (ltac:(clear;easy) : (2^16)%Z=(256*256)%Z) in *.
    rewrite -> (ltac:(clear;easy) : (2^24)%Z=(256*256*256)%Z) in *. lia. }
  rewrite ut. clear tr jj ut.
  unfold store. rewrite pushDispatch2 bindDispatch unfoldInvoke_S_Store.
  case_decide as ei; [| simpl in ei; lia].
  remember (λ _0 : arrayIndex0, _) as sel eqn:hel.
  assert (iu : sel = (fun x => match x with | arraydef_0__dp => repeat 0 1000000 | arraydef_0__message => [Z.of_nat limit] | arraydef_0__n => [Z.of_nat (length items)] end)).
  { rewrite hel. apply functional_extensionality_dep. intro u.
    destruct u; clear; easy. }
  rewrite iu. clear sel hel iu ei.
  rewrite !leftIdentity pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve. case_decide as i8; [| simpl in i8; lia].
  assert (up : (coerceInt
                (nth_lt [Z.of_nat limit] (Z.to_nat 0) i8) 64) = Z.of_nat limit).
  { unfold coerceInt. simpl. rewrite Z.mod_small; lia. }
  rewrite up. clear up. rewrite !leftIdentity pushNumberSet2 pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve. case_decide as yb; [| simpl in yb; lia]. clear i8.
  rewrite (ltac:(easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) yb = Z.of_nat (length items)) !leftIdentity.
  assert (ue : (Z.to_nat
  (coerceInt (Z.of_nat (length items) + 1) 64)) = (length items + 1)%nat).
  { unfold coerceInt. rewrite Z.mod_small; lia. }
  rewrite ue. clear ue.
Admitted.