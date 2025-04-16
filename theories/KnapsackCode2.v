From stdpp Require Import numbers list.
From CoqCP Require Import Options Imperative Knapsack KnapsackCode ListsEqual.
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

Lemma nthGenerateDataValue (items : list (nat * nat)) (limit x index : nat) (hx : (x < 4)%nat) (hIndex : (index < length items)%nat) : nth (4 * length items + 4 * index + x) (generateData items limit) (0%Z) = nth x (to32 (snd (nth index items (0%nat,0%nat)))) 0%Z.
Proof.
  unfold generateData. rewrite nth_lookup lookup_app_r.
  { rewrite serializeWeightsLength. lia. }
  rewrite lookup_app_l.
  { rewrite !serializeValuesLength !serializeWeightsLength. lia. }
  rewrite -nth_lookup. clear limit.
  rewrite !serializeWeightsLength (ltac:(lia) : (4 * length items + 4 * index + x - 4 * length items = 4 * index + x)%nat).
  revert index hIndex. induction items as [| head tail IH]. { easy. }
  intro n.
  destruct head as [weight value].
  rewrite (ltac:(simpl; reflexivity) : length ((weight, value) :: tail) = (1 + length tail)%nat) (ltac:(clear; easy) : serializeValues ((weight, value) :: tail) = to32 value ++ serializeValues tail).
  destruct n as [| n].
  - intro j. rewrite (ltac:(clear; lia) : (4 * 0 + x = x)%nat).
    rewrite nth_lookup lookup_app_l. { unfold to32. rewrite (ltac:(easy) : forall a b c d, (length [a; b; c; d] = 4)%nat). exact hx. }
    rewrite (ltac:(easy) : (nth 0 ((weight, value) :: tail) (0%nat, 0%nat)).2 = value). rewrite -nth_lookup. reflexivity.
  - intro j. rewrite (ltac:(lia) : (4 * S n + x = 4 + (4 * n + x))%nat).
    rewrite !nth_lookup lookup_app_r.
    { unfold to32. rewrite (ltac:(easy) : forall a b c d, (length [a; b; c; d] = 4)%nat). lia. }
    rewrite (ltac:(unfold to32; rewrite (ltac:(easy) : forall a b c d, (length [a; b; c; d] = 4)%nat); lia) : (4 + (4 * n + x) - length (to32 weight))%nat = (4 * n + x)%nat) (ltac:(easy) : ((weight, value) :: tail) !! S n = tail !! n) -!nth_lookup. apply IH. lia.
Qed.

Lemma assembly (x : nat) (hx : Z.of_nat x < 2^32) : (coerceInt
(coerceInt
   (coerceInt
      (coerceInt
         (coerceInt
            (nth 0%nat
               (to32 x) 0) 32 *
          coerceInt (Z.land (1 ≪ 24) (Z.ones 64)) 32)
         32 +
       coerceInt
         (coerceInt
            (nth 1%nat
               (to32 x) 0) 32 *
          coerceInt (Z.land (1 ≪ 16) (Z.ones 64)) 32)
         32) 32 +
    coerceInt
      (coerceInt
         (nth 2%nat
            (to32 x) 0) 32 *
       coerceInt (Z.land (1 ≪ 8) (Z.ones 64)) 32) 32)
   32 +
 coerceInt
   (nth 3%nat
      (to32 x)
      0) 32) 32) = Z.of_nat x.
Proof.
  assert (m1 : Z.of_nat (2^24) = 2^24). { rewrite Nat2Z.inj_pow; easy. }
  assert (m2 : Z.of_nat (2^16) = 2^16). { rewrite Nat2Z.inj_pow; easy. }
  assert (m3 : Z.of_nat (2^8) = 2^8). { rewrite Nat2Z.inj_pow; easy. }
  pose proof Z.div_le_mono (Z.of_nat x) (2^32 - 1) (2^24) ltac:(lia) ltac:(lia) as i1.
  pose proof Z.div_le_mono (Z.of_nat x) (2^32 - 1) (2^16) ltac:(lia) ltac:(lia) as i2.
  pose proof Z.div_le_mono (Z.of_nat x) (2^32 - 1) (2^8) ltac:(lia) ltac:(lia) as i3.
  pose proof Zle_0_nat x as j.
  pose proof Z.div_le_mono _ _ (2^24) ltac:(lia) j as j1.
  pose proof Z.div_le_mono _ _ (2^16) ltac:(lia) j as j2.
  pose proof Z.div_le_mono _ _ (2^8) ltac:(lia) j as j3.
  rewrite -> (ltac:(easy) : (2 ^ 32 - 1) `div` 2 ^ 24 = 2^8 - 1) in i1.
  rewrite -> (ltac:(clear; easy) : (2 ^ 32 - 1) `div` 2 ^ 16 = 2^16 - 1) in i2.
  rewrite -> (ltac:(clear; easy) : (2 ^ 32 - 1) `div` 2 ^ 8 = 2^24 - 1) in i3.
  rewrite -> (ltac:(clear; easy) : 0 `div` 2 ^ 24 = 0) in j1.
  rewrite -> (ltac:(clear; easy) : 0 `div` 2 ^ 16 = 0) in j2.
  rewrite -> (ltac:(clear; easy) : 0 `div` 2 ^ 8 = 0) in j3.
  assert (s1 : coerceInt (nth 0 (to32 x) 0) 32 = Z.of_nat x / (2^24)).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 0%nat [a;b;c;d] e = a). rewrite Z.mod_small Nat2Z.inj_div m1; lia. }
  assert (s2 : coerceInt (nth 1 (to32 x) 0) 32 = (Z.of_nat x / (2^16)) `mod` 256).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 1%nat [a;b;c;d] e = b). rewrite Z.mod_small Nat2Z.inj_mod Nat2Z.inj_div m2; [| clear; lia]. pose proof Z.mod_bound_pos (Z.of_nat x `div` 2 ^ 16) 256 ltac:(lia) ltac:(lia). lia. }
  assert (s3 : coerceInt (nth 2 (to32 x) 0) 32 = (Z.of_nat x / (2^8)) `mod` 256).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 2%nat [a;b;c;d] e = c). rewrite Z.mod_small Nat2Z.inj_mod Nat2Z.inj_div m3; [| clear; rewrite !(ltac:(easy) : 2^8 = 256); lia]. pose proof Z.mod_bound_pos (Z.of_nat x `div` 2 ^ 8) (2^8) ltac:(lia) ltac:(lia). lia. }
  assert (s4 : coerceInt (nth 3 (to32 x) 0) 32 = Z.of_nat x `mod` 256).
  { unfold coerceInt, to32. rewrite (ltac:(easy) : forall a b c d e, nth 3%nat [a;b;c;d] e = d). rewrite Z.mod_small Nat2Z.inj_mod; [| clear; lia]. pose proof Z.mod_bound_pos (Z.of_nat x) 256 ltac:(lia) ltac:(lia). lia. }
  rewrite s1 s2 s3 s4.
  assert (q1 : coerceInt (Z.land (1 ≪ 24) (Z.ones 64)) 32 = 2^24). { clear. easy. }
  assert (q2 : coerceInt (Z.land (1 ≪ 16) (Z.ones 64)) 32 = 2^16). { clear. easy. }
  assert (q3 : coerceInt (Z.land (1 ≪ 8) (Z.ones 64)) 32 = 2^8). { clear. easy. }
  rewrite q1 q2 q3.
  pose proof Z.mod_bound_pos (Z.of_nat x `div` 2 ^ 16) 256 ltac:(assumption) as u1.
  pose proof Z.mod_bound_pos (Z.of_nat x `div` 2 ^ 8) 256 ltac:(assumption) as u2.
  pose proof Z.mod_bound_pos (Z.of_nat x) 256 ltac:(assumption) as u3.
  assert (w1 : coerceInt (Z.of_nat x `div` 2 ^ 24 * 2 ^ 24) 32 = (Z.of_nat x `div` 2 ^ 24 * 2 ^ 24)%Z).
  { unfold coerceInt. rewrite Z.mod_small; lia. }
  assert (w2 : coerceInt ((Z.of_nat x `div` 2 ^ 16) `mod` 256 * 2 ^ 16) 32 = ((Z.of_nat x `div` 2 ^ 16) `mod` 256 * 2 ^ 16)%Z).
  { unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. lia. }
  assert (w3 : coerceInt ((Z.of_nat x `div` 2 ^ 8) `mod` 256 * 2 ^ 8) 32 = ((Z.of_nat x `div` 2 ^ 8) `mod` 256 * 2 ^ 8)%Z).
  { unfold coerceInt. rewrite Z.mod_small; [| reflexivity]. lia. }
  rewrite w1 w2 w3.
  unfold coerceInt. rewrite !(Z.mod_small _ (2^32)); try lia.
  pose proof Z.div_mod (Z.of_nat x) 256 ltac:(clear; easy) as r1.
  pose proof Z.div_mod (Z.of_nat x / 256) 256 ltac:(clear; easy) as r2.
  pose proof Z.div_mod (Z.of_nat x / (256 * 256)) 256 ltac:(clear; easy) as r3.
  rewrite (Z.div_div (Z.of_nat x) 256 256 ltac:(clear; easy) ltac:(clear; easy)) in r2.
  rewrite (Z.div_div (Z.of_nat x) (256 * 256) 256 ltac:(clear; easy) ltac:(clear; easy)) in r3.
  rewrite !(ltac:(clear; easy) : 2^8 = 256) !(ltac:(clear; easy) : 2^16 = (256 * 256)%Z) !(ltac:(clear; easy) : 2^24 = (256 * 256 * 256)%Z). lia.
Qed.

Lemma readWeight (items : list (nat * nat)) (hl : Z.of_nat (length items) < 2^32) (limit : nat) (a32 : forall x, (fst (nth x items (0%nat,0%nat)) < 2^32)%nat) whatever index (hZ : 0 <= index) (hIndex : (Z.to_nat index < length items)%nat) cont whatever2 whatever3 ol ju : invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__message => [ol] | arraydef_0__dp => ju | arraydef_0__n => [Z.of_nat (length items)] end) whatever (funcdef_0__getweight whatever2 (fun=> index) whatever3 >>= cont) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__message => [Z.of_nat (fst (nth (Z.to_nat index) items (0%nat,0%nat)))] | arraydef_0__dp => ju | arraydef_0__n => [Z.of_nat (length items)] end) whatever (cont tt).
Proof.
  unfold funcdef_0__getweight.
  unfold addInt, multInt. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  rewrite dataLength (ltac:(unfold coerceInt; rewrite Z.mod_small; lia) : (coerceInt (4 * index) 64 = 4 * index)%Z) (ltac:(lia) : (Z.to_nat (4 * index) = 4 * Z.to_nat index + 0)%nat) nthGenerateDataWeight. { lia. } { lia. }
  case_decide as uw; [| lia]. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet !leftIdentity.
  rewrite (ltac:(unfold coerceInt; rewrite !Z.mod_small; lia) : coerceInt (coerceInt (4 * index) 64 + 1) 64 = (4 * index + 1)%Z).
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  case_decide as jk; [| rewrite dataLength in jk; lia].
  rewrite (ltac:(lia) : (Z.to_nat (4 * index + 1) = 4 * Z.to_nat index + 1)%nat) nthGenerateDataWeight. { lia. } { lia. }
  (* barrier *)
  rewrite !leftIdentity -!bindAssoc pushNumberGet !leftIdentity.
  rewrite (ltac:(unfold coerceInt; rewrite !Z.mod_small; lia) : coerceInt (coerceInt (4 * index) 64 + 2) 64 = (4 * index + 2)%Z).
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  clear jk; case_decide as jk; [| rewrite dataLength in jk; lia].
  rewrite (ltac:(lia) : (Z.to_nat (4 * index + 2) = 4 * Z.to_nat index + 2)%nat) nthGenerateDataWeight. { lia. } { lia. }
  (* barrier *)
  rewrite !leftIdentity -!bindAssoc pushNumberGet !leftIdentity.
  rewrite (ltac:(unfold coerceInt; rewrite !Z.mod_small; lia) : coerceInt (coerceInt (4 * index) 64 + 3) 64 = (4 * index + 3)%Z).
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  clear jk; case_decide as jk; [| rewrite dataLength in jk; lia].
  rewrite (ltac:(lia) : (Z.to_nat (4 * index + 3) = 4 * Z.to_nat index + 3)%nat) nthGenerateDataWeight. { lia. } { lia. }
  rewrite assembly.
  { pose proof a32 (Z.to_nat index).
    rewrite (ltac:(rewrite Nat2Z.inj_pow; easy) : 2^32 = Z.of_nat (2^32)). lia. }
  rewrite !leftIdentity pushDispatch2 bindDispatch unfoldInvoke_S_Store.
  case_decide as rr; [| simpl in rr; lia].
  remember (fun x : arrayIndex0 => _) as s1 eqn:h1.
  remember (fun x : arrayIndex0 => _) as s2 eqn:h2 in |- * at 1.
  assert (df : s1 = s2).
  { apply functional_extensionality_dep. intro y. subst s1 s2. destruct y; easy. }
  rewrite df. easy.
Qed.

Lemma readValue (items : list (nat * nat)) (hl : Z.of_nat (length items) < 2^32) (limit : nat) (a32 : forall x, (snd (nth x items (0%nat,0%nat)) < 2^32)%nat) whatever index (hZ : 0 <= index) (hIndex : (Z.to_nat index < length items)%nat) cont whatever2 whatever3 ol ju : invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__message => [ol] | arraydef_0__dp => ju | arraydef_0__n => [Z.of_nat (length items)] end) whatever (funcdef_0__getvalue whatever2 (fun=> index) whatever3 >>= cont) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__message => [Z.of_nat (snd (nth (Z.to_nat index) items (0%nat,0%nat)))] | arraydef_0__dp => ju | arraydef_0__n => [Z.of_nat (length items)] end) whatever (cont tt).
Proof.
  unfold funcdef_0__getvalue.
  unfold addInt, multInt. rewrite !leftIdentity.
  rewrite -!bindAssoc pushDispatch bindDispatch unfoldInvoke_S_Retrieve. case_decide as tu; [| simpl in tu; lia]. rewrite (ltac:(clear; easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tu = Z.of_nat (length items)). clear tu. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  rewrite dataLength (ltac:(unfold coerceInt; rewrite Z.mod_small; lia) : coerceInt (4 * Z.of_nat (length items)) 64 = (4 * Z.of_nat (length items))%Z) (ltac:(unfold coerceInt; rewrite Z.mod_small; lia) : (coerceInt (4 * index) 64 = 4 * index)%Z) (ltac:(unfold coerceInt; rewrite Z.mod_small; lia) : Z.to_nat (coerceInt (4 * Z.of_nat (length items) + 4 * index) 64) = (4 * length items + 4 * Z.to_nat index + 0)%nat) nthGenerateDataValue. { lia. } { lia. }
  case_decide as uw; [| lia]. rewrite !leftIdentity -!bindAssoc pushDispatch bindDispatch unfoldInvoke_S_Retrieve.
  case_decide as tu; [| simpl in tu; lia]. rewrite (ltac:(clear; easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tu = Z.of_nat (length items)). clear tu. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  assert (yu : (Z.to_nat
  (coerceInt
     (coerceInt
        (coerceInt (4 * Z.of_nat (length items)) 64 +
         coerceInt (4 * index) 64) 64 + 1) 64)) = (4 * length items + 4 * Z.to_nat index + 1)%nat).
  { unfold coerceInt. rewrite !Z.mod_small; lia. } rewrite yu. clear yu. rewrite nthGenerateDataValue. { lia. } { lia. }
  case_decide as tu; [| rewrite dataLength in tu; lia]. clear uw tu.
  rewrite !leftIdentity.
  rewrite -!bindAssoc pushDispatch bindDispatch unfoldInvoke_S_Retrieve. case_decide as tu; [| simpl in tu; lia]. rewrite (ltac:(clear; easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tu = Z.of_nat (length items)). clear tu. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  assert (yu : (Z.to_nat
  (coerceInt
     (coerceInt
        (coerceInt (4 * Z.of_nat (length items)) 64 + coerceInt (4 * index) 64)
        64 + 2) 64)) = (4 * length items + 4 * Z.to_nat index + 2)%nat).
  { unfold coerceInt. rewrite !Z.mod_small; lia. } rewrite yu. clear yu. case_decide as rt; [| rewrite dataLength in rt; lia].
  rewrite !leftIdentity.
  rewrite -!bindAssoc pushDispatch bindDispatch unfoldInvoke_S_Retrieve. case_decide as tu; [| simpl in tu; lia]. rewrite (ltac:(clear; easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) tu = Z.of_nat (length items)). clear tu. rewrite !leftIdentity.
  rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
  rewrite pushDispatch2 bindDispatch unfoldInvoke_S_ReadByte.
  assert (yu : (Z.to_nat
  (coerceInt
     (coerceInt
        (coerceInt (4 * Z.of_nat (length items)) 64 + coerceInt (4 * index) 64)
        64 + 3) 64)) = (4 * length items + 4 * Z.to_nat index + 3)%nat).
  { unfold coerceInt. rewrite !Z.mod_small; lia. } rewrite yu. clear yu.
  case_decide as yi; [| rewrite dataLength in yi; lia].
  rewrite !nthGenerateDataValue. { lia. } { lia. } { lia. } { lia. }
  (* BIG BARRIER *)
  rewrite assembly.
  { pose proof a32 (Z.to_nat index).
    rewrite (ltac:(rewrite Nat2Z.inj_pow; easy) : 2^32 = Z.of_nat (2^32)). lia. }
  rewrite !leftIdentity pushDispatch2 bindDispatch unfoldInvoke_S_Store.
  case_decide as rr; [| simpl in rr; lia].
  remember (fun x : arrayIndex0 => _) as s1 eqn:h1.
  remember (fun x : arrayIndex0 => _) as s2 eqn:h2 in |- * at 1.
  assert (df : s1 = s2).
  { apply functional_extensionality_dep. intro y. subst s1 s2. destruct y; easy. }
  rewrite df. easy.
Qed.

(* CAVEAT: the list of items has to be reversed to match the imperative implementation *)
Fixpoint fill (items : list (nat * nat)) (maxLimit : nat) (top : nat) :=
  match top with
  | O => []
  | S top =>
    fill items maxLimit top ++ [knapsack (drop (length items - top / (maxLimit + 1)) items) (top `mod` (maxLimit + 1))]
  end.

Lemma lengthFill (items : list (nat * nat)) (maxLimit : nat) (top : nat) : length (fill items maxLimit top) = top.
Proof.
  induction top as [| top IH].
  { easy. }
  simpl. rewrite app_length IH. simpl. lia.
Qed.

Lemma retrievalFact (items : list (nat * nat)) (maxLimit : nat) (top : nat) (index limit : nat) (hLimit : (limit <= maxLimit)%nat) (hsave : (index * (maxLimit + 1) + limit < top)%nat) : nth ((index * (maxLimit + 1) + limit)%nat) (fill items maxLimit top) 0%nat = knapsack (drop ((length items - index)%nat) items) limit.
Proof.
  remember (index * (maxLimit + 1) + limit)%nat as jw eqn:ol.
  assert (f1 : (jw `mod` (maxLimit + 1))%nat = limit).
  { subst jw. rewrite Nat.add_mod. { lia. }
    rewrite Nat.mod_mul. { lia. } rewrite Nat.add_0_l.
    rewrite Nat.mod_mod. { lia. } rewrite Nat.mod_small; lia. }
  assert (f2 : (jw `div` (maxLimit + 1))%nat = index).
  { subst jw. rewrite Nat.div_add_l. { lia. }
    rewrite Nat.div_small; lia. }
    subst limit index. clear ol hLimit.
  revert jw hsave. induction top as [| top IH]; intros jw hsave. { lia. }
  simpl.
  destruct (ltac:(lia) : (jw = top \/ jw < top)%nat) as [dj | dj].
  { subst jw. rewrite nth_lookup lookup_app_r. { rewrite lengthFill. lia. }
    rewrite lengthFill Nat.sub_diag. easy. }
  rewrite nth_lookup lookup_app_l. { rewrite lengthFill. lia. }
  rewrite -nth_lookup IH; lia.
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
  rewrite up. clear up. rewrite !leftIdentity pushNumberSet2 pushDispatch2 bindDispatch unfoldInvoke_S_Store.
  case_decide as ikv; [| simpl in ikv; lia]. rewrite !leftIdentity.
  remember (fun (x : arrayIndex0) => _) as eks eqn:ovk in |- * at 1.
  assert (iex : eks = (fun x => match x with | arraydef_0__message => [0%Z] | arraydef_0__dp => repeat 0 1000000%nat | arraydef_0__n => [Z.of_nat (length items)] end)).
  { subst eks. apply functional_extensionality_dep.
    intro u. destruct u; easy. }
  clear ovk. subst eks. rewrite pushDispatch2 unfoldInvoke_S_Retrieve.
  case_decide as yb; [| simpl in yb; lia]. clear i8.
  rewrite (ltac:(easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) yb = Z.of_nat (length items)) !leftIdentity.
  assert (ue : (Z.to_nat
  (coerceInt (Z.of_nat (length items) + 1) 64)) = (length items + 1)%nat).
  { unfold coerceInt. rewrite Z.mod_small; lia. }
  rewrite ue. clear ue.
  remember (loop _ _) as de eqn:ed.
  remember (length items + 1)%nat as na eqn:nb in ed at 1.
  assert (ub : (na <= length items + 1)%nat). { lia. }
  assert (ow : length items <> 0%nat).
  { intro sa. pose proof nil_length_inv _ sa as hw. exact (notNil hw). }
  assert (wu : forall cont jk, invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1))%nat) ++ repeat 0 (1000000 - (length items + 1 - na) * (limit + 1))%nat | arraydef_0__message => [0] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (de >>= cont)) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1) * (limit + 1))%nat) ++ repeat 0 (1000000 - (length items + 1) * (limit + 1))%nat | arraydef_0__message => [0] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (cont tt))).
  { intros cont jk.
    clear nb. subst de. induction na as [| na IH].
    { rewrite (ltac:(clear; simpl; reflexivity) : forall x, loop 0 x = _). rewrite leftIdentity. rewrite Nat.sub_0_r. reflexivity. }
    rewrite loop_S !leftIdentity.
    assert (ueo: (coerceInt (Z.of_nat (length items) + 1) 64 - Z.of_nat na - 1 = Z.of_nat (length items) - Z.of_nat na)).
    { unfold coerceInt. rewrite Z.mod_small; lia. }
    rewrite ueo.
    case_bool_decide as iem.
    { rewrite (ltac:(lia) : (length items + 1%nat - S na = 0)%nat).
      rewrite Nat.mul_0_l Nat.sub_0_r.
      rewrite !leftIdentity.
      rewrite (ltac:(clear;easy) : map Z.of_nat (fill (reverse items) limit 0) = []) app_nil_l.
      rewrite (ltac:(lia) : ((length items + 1 - na) * (limit + 1) = limit + 1)%nat) in IH.
      assert (uas : forall jd, (jd <= limit)%nat -> map Z.of_nat (fill (reverse items) limit (jd + 1)%nat) = repeat 0 (jd + 1)%nat).
      { clear. intros jd hd.
        induction jd as [| jd IH].
        { unfold fill. unfold map. simpl.
          rewrite Nat.div_0_l. { lia. }
          rewrite Nat.mod_0_l. { lia. }
          rewrite Nat.sub_0_r drop_all. easy. }
          simpl.
          rewrite Nat.div_small. { lia. }
          rewrite Nat.sub_0_r drop_all. simpl.
          rewrite map_app. rewrite IH. { lia. }
          simpl. rewrite (ltac:(clear;easy) : Z.of_nat 0 = 0).
          rewrite repeat_cons. reflexivity. }
        rewrite uas in IH. { clear. lia. }
        rewrite <- !repeat_app in IH.
        rewrite -> (ltac:(lia) : (limit + 1 + (1000000 - (limit + 1)) = 1000000)%nat) in IH.
        rewrite (IH ltac:(lia)).
        reflexivity. }
    rewrite !leftIdentity.
    rewrite -> dropWithinLoopLiftToWithinLoop.
    rewrite -!bindAssoc pushNumberGet2 !leftIdentity.
    assert (dat : (Z.to_nat
    (coerceInt
       (update (fun=> 0) vardef_0__main_limit 
          (Z.of_nat limit) vardef_0__main_limit + 1) 64)) = (limit + 1)%nat).
    { unfold coerceInt. rewrite Z.mod_small. { unfold update. simpl. lia. }
      unfold update. simpl. lia. }
    rewrite dat. clear dat.
    remember (loop (limit + 1) _) as dk eqn:ud in |- * at 1.
    remember (limit + 1)%nat as ej eqn:wg in ud at 1.
    assert (av : (ej <= limit + 1)%nat). { revert wg. clear. intro wg. lia. }
    assert (adv : forall cont msg jk, exists nmsg, invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - ej)%nat) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - ej))%nat | arraydef_0__message => [msg] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (dk >>= cont)) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1))%nat) ++ repeat 0 (1000000 - (length items + 1 - na) * (limit + 1))%nat | arraydef_0__message => [nmsg] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (cont tt))).
    { clear wg. intros cont1 msg1 jk1. revert msg1. subst dk. induction ej as [| ej ID].
      { rewrite !Nat.sub_0_r.
        rewrite (ltac:(simpl; reflexivity) : loop 0 _ = _).
        rewrite !leftIdentity. intro ad. exists ad. reflexivity. }
      rewrite loop_S.
      rewrite <- !bindAssoc.
      rewrite !leftIdentity.
      rewrite -> dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc, -> eliminateLift.
      pose proof ID ltac:(lia) (Z.of_nat (nth (length items - na - 1)%nat items (0%nat, 0%nat)).2) as [wit ID2].
      clear ID.
      exists wit.
      rewrite readWeight.
      { lia. } { tauto. }
      { unfold update. simpl. unfold coerceInt. rewrite Z.mod_small; lia. }
      { unfold update. simpl. unfold coerceInt. rewrite Z.mod_small; lia. }
      { exact (fun x => false). }
      { exact (fun x => []). }
      assert (qat : (Z.to_nat
      (update (fun=> 0) vardef_0__getweight_index
         (coerceInt
            (Z.of_nat (length items) - Z.of_nat na - 1) 64)
         vardef_0__getweight_index)) = (length items - na - 1)%nat).
      { unfold update. simpl. unfold coerceInt. rewrite Z.mod_small; lia. }
      rewrite qat. clear qat.
      rewrite dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc. rewrite pushDispatch. rewrite unfoldInvoke_S_Retrieve.
      case_decide as wla; [| simpl in wla; lia].
      rewrite (ltac:(simpl; reflexivity) : nth_lt [_] 0 _ = _).
      unfold coerceInt at 1. rewrite Z.mod_small.
      { constructor. { clear. lia. }
        pose proof a32 (length items - na - 1)%nat as bv.
        rewrite (ltac:(rewrite Znat.Z2Nat.inj_pow; [lia | lia | easy]) : (2^32)%nat = Z.to_nat (2^32)%Z) in bv.
        lia. }
      rewrite -> !leftIdentity.
      rewrite pushNumberSet2.
      rewrite dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc.
      rewrite eliminateLift.
      rewrite readValue.
      { lia. } { exact b32. } { unfold update. simpl. unfold coerceInt. rewrite Z.mod_small; lia. } { unfold update. simpl. unfold coerceInt. rewrite Z.mod_small; lia. } { exact (fun x => false). } { exact (fun x => []). }
      assert (qat : (Z.to_nat
      (update (fun=> 0) vardef_0__getweight_index
         (coerceInt
            (Z.of_nat (length items) - Z.of_nat na - 1) 64)
         vardef_0__getweight_index)) = (length items - na - 1)%nat).
      { unfold update. simpl. unfold coerceInt. rewrite Z.mod_small; lia. }
      rewrite qat. clear qat.
      rewrite dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc. rewrite pushDispatch. rewrite unfoldInvoke_S_Retrieve. clear wla.
      case_decide as wla; [| simpl in wla; lia].
      rewrite (ltac:(simpl; reflexivity) : nth_lt [_] 0 _ = _).
      unfold coerceInt at 1. rewrite Z.mod_small.
      { constructor. { clear. lia. }
        pose proof b32 (length items - na - 1)%nat as bv.
        rewrite (ltac:(rewrite Znat.Z2Nat.inj_pow; [lia | lia | easy]) : (2^32)%nat = Z.to_nat (2^32)%Z) in bv.
        lia. }
      rewrite -> !leftIdentity.
      rewrite pushNumberSet2.
      rewrite dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc.
      rewrite pushNumberGet2.
      case_bool_decide as wy; unfold coerceInt in wy; unfold update in wy; simpl in wy; rewrite Z.mod_small in wy; try lia; rewrite -> !leftIdentity, <- !bindAssoc, dropWithinLoopLiftToWithinLoop; unfold numberLocalGet at 1; rewrite <- !bindAssoc; rewrite pushNumberGet2 !leftIdentity.
      - rewrite pushNumberGet2.
        remember (coerceInt _ 64) as wmm eqn:iwd in |- *.
        unfold coerceInt in iwd. unfold update in iwd. simpl in iwd.
        pose proof (ltac:(clear; rewrite Z2Nat.inj_pow; easy) : Z.of_nat (2^32)%nat = (2^32)%Z).
        pose proof (ltac:(clear; rewrite Z2Nat.inj_pow; easy) : Z.of_nat (2^64)%nat = (2^64)%Z).
        rewrite !Z.mod_small in iwd; try lia.
        { constructor. { nia. } lia. }
        { constructor. { nia. } lia. }
        { constructor. { nia. } lia. }
        subst wmm. rewrite pushDispatch2 unfoldInvoke_S_Retrieve.
        case_decide as wjm; [| rewrite app_length repeat_length map_length lengthFill in wjm; nia].
        remember (coerceInt _ 64) as mvw eqn:ica in |- *.
        unfold coerceInt in ica. unfold update in ica. simpl in ica.
        rewrite !Z.mod_small in ica; try lia.
        { constructor. { nia. } lia. }
        { constructor. { nia. } lia. }
        { constructor. { nia. } lia. }
        subst mvw. remember (nth_lt _ _ _) as nw2 eqn:g3g.
        rewrite (nth_lt_default _ _ _ 0%Z) in g3g.
        rewrite -> nth_lookup, lookup_app_l, <- nth_lookup, (ltac:(clear; easy) : 0%Z = Z.of_nat (0%nat)), map_nth in g3g; [| rewrite -> map_length, lengthFill; nia].
        rewrite (ltac:(nia) : (Z.to_nat
        ((Z.of_nat (length items) - Z.of_nat na - 1) *
         (Z.of_nat limit + 1) +
         (Z.of_nat limit + 1 - Z.of_nat ej - 1))) = ((length items - na - 1) * (limit + 1) + (limit - ej))%nat) in g3g.
        rewrite retrievalFact in g3g. { lia. } { nia. }
        rewrite pushDispatch unfoldInvoke_S_Store.
        case_decide as wnv; [| rewrite app_length repeat_length map_length lengthFill in wnv; nia].
        remember (fun x => _) as wjv eqn:igm in |- *.
        assert (cfl : wjv = fun x => match x with | arraydef_0__dp => (<[Z.to_nat
        ((Z.of_nat (length items) - Z.of_nat na) * (Z.of_nat limit + 1) +
        (Z.of_nat limit + 1 - Z.of_nat ej - 1)):=nw2]>
        (map Z.of_nat
          (fill (reverse items) limit
            ((length items + 1 - na) * (limit + 1) - S ej)) ++
        repeat 0 (1000000 -
          ((length items + 1 - na) * (limit + 1) - S ej)))) | arraydef_0__message => [Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).2] | arraydef_0__n => [Z.of_nat (length items)] end).
        { apply functional_extensionality_dep. subst wjv. intro x.
          destruct x; easy. }
        subst wjv. rewrite cfl. clear cfl.
        remember (<[_ := _]> _) as ty eqn:iv in |- *.
        assert (il : ty = (map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - ej)) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - ej)))).
        { subst ty. remember (Init.Nat.of_num_uint _) as dw eqn:wd. apply list_eq. intro u.
          destruct (ltac:(lia) : (u < (length items + 1 - na) * (limit + 1) - S ej \/ u = (length items + 1 - na) * (limit + 1) - S ej \/ (length items + 1 - na) * (limit + 1) - S ej < u)%nat) as [c | [c | c]].
          - rewrite list_lookup_insert_ne. { lia. }
            rewrite lookup_app_l.
            { rewrite -> map_length, lengthFill. exact c. }
            rewrite lookup_app_l.
            { rewrite -> map_length, lengthFill. lia. }
            remember (_ !! _) as n1 eqn:y1 in |- *.
            remember (_ !! _) as n2 eqn:y2 in |- *.
            assert (stask : default (Z.of_nat 0%nat) n1 = default (Z.of_nat 0%nat) n2).
            { subst n1 n2. rewrite <- !nth_lookup. rewrite -> !map_nth.
              rewrite (ltac:(lia) : ((length items + 1 - na) * (limit + 1) - S ej = (length items - na) * (limit + 1) + (limit - ej))%nat).
              rewrite (ltac:(lia) : ((length items + 1 - na) * (limit + 1) - ej = S ((length items - na) * (limit + 1) + (limit - ej)))%nat).
              simpl.
              rewrite -> !nth_lookup, lookup_app_l. { reflexivity. }
              rewrite -> lengthFill. lia. }
            destruct n1 as [n1 |].
            + destruct n2 as [n2 |].
              * simpl in stask. rewrite stask. reflexivity.
              * symmetry in y2. pose proof lookup_ge_None_1 _ _ y2 as iw. rewrite -> map_length, lengthFill in iw. lia.
            + symmetry in y1. pose proof lookup_ge_None_1 _ _ y1 as iw. rewrite -> map_length, lengthFill in iw. lia.
          - remember (Z.to_nat _) as la eqn:gi in |- *.
            rewrite (ltac:(lia) : la = u). rewrite list_lookup_insert.
            { rewrite -> app_length, map_length, lengthFill, repeat_length. lia. }
            remember (_ !! _) as vn eqn:uj in |- *.
            assert (cq : default (Z.of_nat 0%nat) vn = nw2).
            { subst vn. rewrite -> lookup_app_l, <- nth_lookup, map_nth; [| rewrite -> map_length, lengthFill; nia]. subst nw2.
              rewrite (ltac:(nia) : u = ((length items - na) * (limit + 1) + (limit - ej))%nat).
              rewrite retrievalFact. { lia. } { lia. }
              pose proof take_drop_middle (reverse items) na as int.
              rewrite reverse_length.
              rewrite (ltac:(lia) : (length items - (length items - na) = na)%nat).
              rewrite (ltac:(lia) : (length items - (length items - na - 1) = na + 1)%nat).
              rewrite reverse_lookup in int. { lia. }
              pose proof int (nth (length items - na - 1) items (0%nat, 0%nat)) ltac:(rewrite nth_lookup; rewrite (ltac:(lia) : (length items - na - 1 = length items - S na)%nat); remember (_ !! _) as vmw eqn:ige; destruct vmw as [vmw |]; [easy |]; symmetry in ige; pose proof lookup_ge_None_1 _ _ ige; lia) as ni.
              rewrite -ni.
              rewrite -> drop_app_ge; [| rewrite take_length reverse_length; lia].
              rewrite -> take_length, -> reverse_length, (ltac:(lia) : (na - na `min` length items = 0)%nat), (ltac:(clear; easy) : forall x, drop 0 x = x).
              rewrite (ltac:(clear; intros a b cc; listsEqual) : forall a b c, a ++ b :: c = (a ++ [b]) ++ c).
              rewrite -> drop_app_ge; [| rewrite -> app_length, -> take_length, -> reverse_length, (ltac:(easy) : length [_] = 1%nat); lia].
              rewrite -> app_length, -> take_length, -> reverse_length, (ltac:(lia) : (na `min` length items = na)%nat), (ltac:(clear; easy) : forall a, length [a] = 1%nat), Nat.sub_diag, (ltac:(clear; easy) : forall x, drop 0 x = x).
              simpl.
              clear IH ID2.
              remember (nth (length items - na - 1) items (0%nat, 0%nat)) as eqd eqn:ugn.
              destruct eqd as [jgs amv].
              simpl in wy.
              case_decide as ywq; [| lia]. reflexivity. }
          destruct vn as [vn |]. { simpl in cq. rewrite cq. reflexivity. }
          symmetry in uj. pose proof lookup_ge_None_1 _ _ uj as ta.
          rewrite -> app_length, map_length, repeat_length, lengthFill in ta. nia.
        - rewrite (ltac:(lia) : Z.to_nat ((Z.of_nat (length items) - Z.of_nat na) * (Z.of_nat limit + 1) + (Z.of_nat limit + 1 - Z.of_nat ej - 1)) = ((length items + 1 - na) * (limit + 1) - S ej)%nat).
          rewrite insert_app_r_alt. { rewrite -> map_length, lengthFill. clear. lia. }
          rewrite -> map_length, lengthFill, Nat.sub_diag.
          rewrite -> insert_take_drop, (ltac:(clear; easy) : forall x, take 0 x = []), app_nil_l; [| rewrite repeat_length; lia].
          rewrite -> (ltac:(clear; intros x y z; listsEqual) : forall x y z, x ++ y :: z = (x ++ [y]) ++ z).
          rewrite -> !lookup_app_r.
          + rewrite -> !map_length, !lengthFill.
            remember (_ !! _) as lgv eqn:wkv in |- *.
            remember (_ !! _) as fmw eqn:igk in |- *.
            symmetry in wkv. symmetry in igk.
            destruct lgv as [lgv |]; [| pose proof lookup_ge_None_1 _ _ wkv as tjv; rewrite -> drop_length, repeat_length, app_length, (ltac:(clear; easy) : forall x, length [x] = 1%nat), map_length, lengthFill in tjv].
            * destruct fmw as [fmw |].
              { assert (jak : default 0 (Some lgv) = default 0 (Some fmw)).
                { rewrite <- wkv, <- igk, lookup_drop.
                  rewrite <- !nth_lookup, -> !nth_repeat. reflexivity. }
                simpl in jak. subst lgv. reflexivity. }
              { pose proof lookup_ge_None_1 _ _ igk as tjv.
                pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ wkv) as tyv.
                rewrite repeat_length in tjv. rewrite -> app_length, map_length, drop_length, repeat_length, lengthFill, (ltac:(clear; easy) : forall x, length [x] = 1%nat) in tyv.
                lia. }
            * destruct fmw as [fmw |].
              { pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ igk) as tyv.
                rewrite repeat_length in tyv. lia. }
              { reflexivity. }
          + rewrite -> !map_length, !lengthFill. lia.
          + rewrite -> app_length, !map_length, !lengthFill, (ltac:(clear; easy) : forall x, length [x] = 1%nat). lia. }
        rewrite il. rewrite dropWithinLoopLiftToWithinLoop pushNumberSet2 pushNumberSet2.
        remember (update _ _ _) as ye eqn:jq in |- *.
        remember (update _ _ _) as te eqn:jt in |- * at 3.
        assert (ad : te = ye).
        { subst ye te. apply functional_extensionality_dep. intro az. destruct az; clear; easy. }
        symmetry in ad. rewrite ad jt. clear ad jt jq te ye.
        rewrite ID2. reflexivity.
      - remember (coerceInt _ _) as tew eqn:mwd in |- * at 1.
        unfold coerceInt in mwd.
        unfold update in mwd. simpl in mwd.
        rewrite !Z.mod_small in mwd; try lia. { nia. } { nia. } { nia. }
        subst tew. rewrite bindDispatch pushDispatch2 unfoldInvoke_S_Retrieve. case_decide as gkw; [| rewrite -> app_length, map_length, repeat_length, lengthFill in gkw; lia].
        unfold subInt, multInt at 1. rewrite -> !leftIdentity.
        rewrite <- !bindAssoc. rewrite pushNumberGet2.
        rewrite -> !leftIdentity, <- !bindAssoc. rewrite pushNumberGet2.
        rewrite -> !leftIdentity. remember (coerceInt _ _) as qlf eqn:vmt in |- * at 1.
        unfold coerceInt, update in vmt. simpl in vmt.
        rewrite !Z.mod_small in vmt; try lia. { nia. } { nia. } { nia. } subst qlf.
        rewrite pushDispatch2 unfoldInvoke_S_Retrieve. case_decide as tds; [| rewrite -> app_length, map_length, repeat_length, lengthFill in tds; lia].
        rewrite pushNumberGet.
        assert (ptw : update
        (update (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit))
           vardef_0__main_weight
           (Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).1))
        vardef_0__main_value
        (Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).2)
        vardef_0__main_value = Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).2).
        { unfold update. simpl. reflexivity. }
        rewrite ptw. clear ptw.
        rewrite !(nth_lt_default _ _ _ (Z.of_nat 0%nat)).
        remember (bool_decide _) as bd eqn:hbd in |- * at 1.
        rewrite -> !nth_lookup, !lookup_app_l, <- !nth_lookup in hbd; [| rewrite <- nth_lookup, map_length, lengthFill; nia |rewrite -> map_length, lengthFill; nia].
        rewrite -> !map_nth in hbd.
        assert (wlx : (Z.to_nat
        ((Z.of_nat (length items) - Z.of_nat na - 1) * (Z.of_nat limit + 1) +
         (Z.of_nat limit + 1 - Z.of_nat ej - 1))) = ((length items - na - 1) * (limit + 1) + (limit - ej))%nat). { nia. }
        rewrite -> wlx, retrievalFact in hbd; [| lia | lia].
        assert (xmd : (Z.to_nat
        ((Z.of_nat (length items) - Z.of_nat na - 1) *
         (Z.of_nat limit + 1) +
         (Z.of_nat limit + 1 - Z.of_nat ej - 1 -
          Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).1))) = ((length items - na - 1) * (limit + 1) + (limit - ej - (nth (length items - na - 1) items (0%nat, 0%nat)).1))%nat). { nia. }
        rewrite xmd in hbd. rewrite retrievalFact in hbd.
        { lia. } { lia. }
        pose proof knapsackMax (drop (length (reverse items) - (length items - na - 1)) (reverse items)) (limit - ej - (nth (length items - na - 1) items (0%nat, 0%nat)).1) as ad.
        destruct ad as [[ae [af [ag ah]]] _].
        unfold coerceInt in hbd.
        assert (dsk : (forall a b, a `sublist_of` b -> foldr (fun (k : nat * nat) (ac : nat) => (k.2 + ac)%nat) 0%nat a <= foldr (fun (k : nat * nat) (ac : nat) => (k.2 + ac)%nat) 0%nat b)%nat).
        { clear. intros a b c.
          induction c as [| [c k] y z IH ID | [c k] y z IH ID].
          - easy.
          - rewrite !foldrSum9. lia.
          - rewrite !foldrSum9. lia. }
        assert (dt : ae `sublist_of` reverse items).
        { transitivity (drop (length (reverse items) - (length items - na - 1)) (reverse items)). { exact af. }
          apply sublist_drop. }
        pose proof dsk _ _ dt as tep. rewrite ag in tep.
        assert (frA : forall l p, (foldr (fun (x : nat * nat) (c : nat) => (x.2 + c)%nat) 0%nat (l ++ [p]))%nat = (foldr (fun (x : nat * nat) (c : nat) => x.2 + c) 0%nat l + p.2)%nat).
        { clear. intros l p.
          induction l as [| head tail IH].
          { simpl. lia. }
          rewrite !(ltac:(intros; listsEqual) : forall a b c, (a :: b) ++ [c] = a :: (b ++ [c])).
          destruct head as [m n].
          rewrite !foldrSum9 IH. lia. }
        assert (bts : (foldr (λ (_0 : nat * nat) (_1 : nat), _0.2 + _1) 0 (reverse items) <= length items * Z.to_nat (2^32))%nat).
        { revert frA b32. clear. intros frA b32. induction items as [| head tail IX].
          - easy.
          - remember (Z.to_nat (2^32)) as dtw eqn:vns in |- *.
            simpl. rewrite reverse_cons.
            rewrite frA.
            assert (md : ∀ _0 : nat, ((nth _0 tail (0, 0)).2 < 2 ^ 32)%nat).
            { intro k. pose proof b32 (S k) as da.
              rewrite (ltac:(easy) : nth (S k) (head :: tail) (0%nat, 0%nat) = nth k tail (0%nat, 0%nat)) in da. exact da. }
            pose proof IX md as tje.
            pose proof b32 O as da.
            rewrite (ltac:(easy) : nth O (head :: tail) (0%nat, 0%nat) = head) in da.
            pose proof (ltac:(clear; rewrite Nat2Z.inj_pow; easy) : Z.of_nat (2 ^ 32) = 2^32). lia. }
        rewrite Z.mod_small in hbd.
        { constructor. { lia. }
          pose proof b32 (length items - na - 1)%nat as stone.
          pose proof (ltac:(clear; rewrite Nat2Z.inj_pow; easy) : Z.of_nat (2 ^ 32) = 2^32).
          lia. }
        case_bool_decide as mid; rewrite !leftIdentity; subst bd.
        + rewrite -!bindAssoc dropWithinLoopLiftToWithinLoop !leftIdentity -!bindAssoc pushNumberGet2 !leftIdentity -!bindAssoc pushNumberGet2 !leftIdentity -!bindAssoc pushNumberGet2 !leftIdentity.
          remember (coerceInt _ _) as yr eqn:yu in |- * at 1.
          unfold update in yu. simpl in yu. unfold coerceInt in yu. rewrite !Z.mod_small in yu; try lia. { nia. } { constructor.
          { pose proof (ltac:(lia) : (Z.of_nat (length items) - Z.of_nat na - 1) >= 0) as ta1.
            pose proof (ltac:(lia) : (Z.of_nat limit + 1) >= 0) as ta2.
            pose proof (ltac:(lia) : (Z.of_nat limit + 1 - Z.of_nat ej - 1 - Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).1) >= 0) as ta3.
            revert ta1 ta2 ta3. clear. nia. }
          lia. } { nia. }
          subst yr. rewrite pushDispatch2 unfoldInvoke_S_Retrieve.
          case_decide as ry; [| rewrite app_length map_length repeat_length lengthFill in ry; lia].
          rewrite pushNumberGet2. remember (coerceInt _ _) as twn eqn:wlv in |- * at 1.
          unfold update in wlv. case_decide as uh; [| exfalso; revert uh; clear; easy].
          clear uh. rewrite (nth_lt_default _ _ _ 0) in wlv.
          rewrite -> nth_lookup, lookup_app_l in wlv; [| rewrite map_length lengthFill; lia].
          rewrite !leftIdentity pushDispatch.
          remember (coerceInt _ _) as tjh eqn:uwl in |- * at 1.
          unfold update in uwl. simpl in uwl. unfold coerceInt in uwl. rewrite !Z.mod_small in uwl; try lia.
          rewrite (ltac:(clear;easy) : 0 = Z.of_nat O) -nth_lookup in wlv.
          rewrite map_nth xmd retrievalFact in wlv. { lia. } { lia. }
          unfold coerceInt in wlv. rewrite Z.mod_small in wlv.
          { constructor. { lia. }
            pose proof b32 (length items - na - 1)%nat as stone.
            pose proof (ltac:(clear; rewrite Nat2Z.inj_pow; easy) : Z.of_nat (2 ^ 32) = 2^32).
            lia. }
          rewrite unfoldInvoke_S_Store.
          rewrite (ltac:(lia) : Z.to_nat tjh = ((length items + 1 - na) * (limit + 1) - S ej)%nat).
          case_decide as kew; [| rewrite app_length map_length repeat_length lengthFill in kew; lia].
          rewrite dropWithinLoopLiftToWithinLoop pushNumberSet2.
          rewrite pushNumberSet.
          remember (update _ _ _) as tyt eqn:tut in |- * at 1.
          assert (cqa : tyt = update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)).
          { subst tyt. clear. apply functional_extensionality_dep. intro ga. destruct ga; easy. }
          clear tut. subst tyt.
          remember (fun (x : arrayIndex0) => _) as tyt eqn:tut in |- * at 1.
          assert (nek : tyt = (fun x => match x with | arraydef_0__dp => <[((length items + 1 - na) * (limit + 1) - S ej)%nat:=twn]> ((map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - S ej))) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - S ej))%nat) | arraydef_0__message => [Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).2] | arraydef_0__n => [Z.of_nat (length items)] end)).
          { subst tyt. clear. apply functional_extensionality_dep. intro x.
            destruct x; easy. }
          clear tut. subst tyt.
          assert (td : <[((length items + 1 - na) * (limit + 1) - S ej)%nat:=twn]> ((map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - S ej))) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - S ej))%nat) = (map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - ej))) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - ej))%nat).
          { apply list_eq. intro u.
            destruct (ltac:(lia) : u < ((length items + 1 - na) * (limit + 1) - S ej) \/ u = ((length items + 1 - na) * (limit + 1) - S ej) \/ ((length items + 1 - na) * (limit + 1) - S ej) < u)%nat as [dh | [dh | dh]].
            - rewrite list_lookup_insert_ne. { revert dh. clear. lia. }
              rewrite -> lookup_app_l, -> lookup_app_l; [| rewrite map_length lengthFill | rewrite map_length lengthFill]; try lia.
              remember (_ !! _) as ka1 eqn:qa1.
              remember (_ !! _) as ka2 eqn:qa2 in |- *.
              symmetry in qa1, qa2.
              destruct ka1 as [ka1 |].
              + destruct ka2 as [ka2 |].
                { assert (kt : default (Z.of_nat 0) (Some ka1) = default (Z.of_nat 0) (Some ka2)).
                  { rewrite <- qa1, <- qa2, <- !nth_lookup, !map_nth.
                    rewrite (ltac:(lia) : (length items + 1 - na) * (limit + 1) - ej = S ((length items + 1 - na) * (limit + 1) - S ej))%nat.
                    simpl. rewrite -> !nth_lookup.
                    rewrite -> lookup_app_l. { reflexivity. }
                    rewrite lengthFill. lia. }
                  simpl in kt. rewrite -> kt. reflexivity. }
                  pose proof lookup_ge_None_1 _ _ qa2 as j1.
                  pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ qa1) as j2.
                  rewrite map_length lengthFill in j1.
                  rewrite map_length lengthFill in j2.
                  lia.
              + pose proof lookup_ge_None_1 _ _ qa1 as j1.
                destruct ka2 as [ka2 |].
                { pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ qa2) as j2.
                  rewrite map_length lengthFill in j1.
                  rewrite map_length lengthFill in j2. lia. }
                reflexivity.
            - rewrite dh list_lookup_insert.
              { rewrite app_length map_length repeat_length lengthFill. lia. }
              remember (_ !! _) as ka eqn:qa. symmetry in qa.
              destruct ka as [ka |]; [| pose proof lookup_ge_None_1 _ _ qa as ta; rewrite app_length map_length repeat_length lengthFill in ta; lia].
              rewrite lookup_app_l in qa.
              { rewrite map_length lengthFill. lia. }
              assert (dak : twn = default (Z.of_nat O) (Some ka)).
              { rewrite <- qa, <- nth_lookup, map_nth.
                assert (ql : ((length items + 1 - na) * (limit + 1) - S ej = (length items - na) * (limit + 1) + (limit - ej))%nat).
                { rewrite (ltac:(lia) : (length items + 1 - na = (length items - na) + 1)%nat).
                  rewrite -> Nat.mul_add_distr_r, Nat.mul_1_l.
                  pose proof (ltac:(lia) : (ej <= limit)%nat) as cq.
                  revert cq. clear. nia. }
                rewrite -> ql, retrievalFact.
                { subst twn.
                  assert (km : reverse items !! (length (reverse items) - (length items - na - 1) - 1)%nat =
                  Some (nth (length items - na - 1) items (0%nat, 0%nat))).
                  { remember (_ !! _) as cm eqn:ls in |- *.
                    symmetry in ls.
                    destruct cm as [cm |].
                    { rewrite (ltac:(clear; easy) : cm = default (O, O) (Some cm)).
                      rewrite <- ls, nth_lookup.
                      rewrite reverse_lookup. { 
                      pose proof (ltac:(lia) : length items <> O) as dak.
                      rewrite reverse_length. revert ub dak. clear. lia. }
                      rewrite (ltac:(rewrite reverse_length; lia) : length items - S (length (reverse items) - (length items - na - 1) - 1) = (length items - na - 1))%nat.
                      reflexivity. }
                    pose proof lookup_ge_None_1 _ _ ls as lsv. rewrite reverse_length in lsv. lia. }
                  pose proof (take_drop_middle (reverse items) (length (reverse items) - (length items - na - 1) - 1) (nth (length items - na - 1) items (0%nat, 0%nat))) km as hg.
                  pose proof reverse_length items as vz.
                  rewrite (ltac:(lia) : (length (reverse items) - (length items - na - 1) = na + 1)%nat).
                  rewrite (ltac:(lia) : length (reverse items) - (length items - na) = na)%nat.
                  rewrite (ltac:(lia) : length (reverse items) - (length items - na - 1) - 1 = na)%nat in hg.
                  rewrite <- hg.
                  rewrite -> (ltac:(intros; listsEqual) : forall a b c, a ++ b :: c = (a ++ [b]) ++ c) at 1.
                  rewrite drop_app_ge.
                  { rewrite app_length take_length. simpl. lia. }
                  rewrite app_length take_length reverse_length (ltac:(lia) : (na `min` length items = na)%nat) (ltac:(clear; easy) : forall x, length [x] = 1%nat) Nat.sub_diag (ltac:(clear; easy) : forall x, drop 0 x = x) drop_app_ge take_length reverse_length (ltac:(lia) : (na `min` length items = na))%nat. { lia. }
                  rewrite Nat.sub_diag (ltac:(clear; easy) : forall x, drop 0 x = x).
                  simpl.
                  remember (nth (length items - na - 1) items (0%nat, 0%nat)) as ku eqn:iu.
                  destruct ku as [ku1 ku2].
                  rewrite -> (ltac:(clear; easy) : (ku1, ku2).1 = ku1) in *.
                  rewrite -> (ltac:(clear; easy) : (ku1, ku2).2 = ku2) in *.
                  case_decide as nk. { lia. }
                  rewrite (ltac:(lia) : (length (reverse items) - (length items - na - 1) = S na)%nat) in mid. lia. }
                - clear. lia.
                - lia. }
              simpl in dak. rewrite dak. reflexivity.
            - rewrite list_lookup_insert_ne. { revert dh. clear. lia. }
              rewrite -> lookup_app_r; [| rewrite -> map_length, lengthFill; lia].
              rewrite -> lookup_app_r; [| rewrite -> map_length, lengthFill; lia].
              remember (_ !! _) as t1 eqn:r1 in |- * at 1.
              remember (_ !! _) as t2 eqn:r2 in |- * at 1.
              destruct t1 as [t1 |].
              + destruct t2 as [t2 |].
                * assert (uh : default 0 (Some t1) = default 0 (Some t2)).
                  { rewrite -> r1, r2. rewrite <- !nth_lookup.
                    rewrite -> !nth_repeat. reflexivity. }
                  simpl in uh. rewrite uh.
                  reflexivity.
                * symmetry in r1, r2.
                  pose proof lookup_ge_None_1 _ _ r2 as d1.
                  pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ r1) as d2.
                  rewrite map_length repeat_length lengthFill in d1.
                  rewrite map_length repeat_length lengthFill in d2.
                  lia.
              + destruct t2 as [t2 |].
                * symmetry in r1, r2.
                  pose proof lookup_ge_None_1 _ _ r1 as d1.
                  pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ r2) as d2.
                  rewrite map_length repeat_length lengthFill in d1.
                  rewrite map_length repeat_length lengthFill in d2.
                  lia.
                * reflexivity. }
          rewrite td.
          rewrite ID2. reflexivity.
        (* this case is basically a repeat of the previous but with minor changes *)
        + rewrite -!bindAssoc dropWithinLoopLiftToWithinLoop !leftIdentity -!bindAssoc pushNumberGet2 !leftIdentity -!bindAssoc pushNumberGet2 !leftIdentity -!bindAssoc.
          remember (coerceInt _ _) as yr eqn:yu in |- * at 1.
          unfold update in yu. simpl in yu. unfold coerceInt in yu. rewrite !Z.mod_small in yu; try lia. { nia. } { constructor.
          { pose proof (ltac:(lia) : (Z.of_nat (length items) - Z.of_nat na - 1) >= 0) as ta1.
            pose proof (ltac:(lia) : (Z.of_nat limit + 1) >= 0) as ta2.
            pose proof (ltac:(lia) : (Z.of_nat limit + 1 - Z.of_nat ej - 1 - Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).1) >= 0) as ta3.
            revert ta1 ta2 ta3. clear. nia. }
          lia. } { nia. }
          subst yr. rewrite pushDispatch2 unfoldInvoke_S_Retrieve.
          case_decide as ry; [| rewrite app_length map_length repeat_length lengthFill in ry; lia].
          rewrite !leftIdentity. remember (coerceInt _ _) as twn eqn:wlv in |- * at 1.
          unfold update in wlv. case_decide as uh; [exfalso; revert uh; clear; easy |]. clear uh.
          case_decide as uh; [exfalso; revert uh; clear; easy |]. clear uh.
          case_decide as uh; [| exfalso; revert uh; clear; easy]. clear uh.
          unfold coerceInt in wlv. rewrite !Z.mod_small in wlv; try lia.
          rewrite -> wlv. clear wlv. remember (nth_lt _ _ _) as yn eqn:kn in |- *.
          rewrite (nth_lt_default _ _ _ 0) in kn.
          assert (cr : (Z.to_nat
          ((Z.of_nat (length items) - Z.of_nat na - 1) *
           (Z.of_nat limit + 1) +
           (Z.of_nat limit + 1 - Z.of_nat ej - 1))) = ((length items - na - 1) * (limit + 1) + (limit - ej))%nat). { lia. } rewrite cr in kn. clear cr.
          rewrite nth_lookup lookup_app_l in kn. { rewrite map_length lengthFill. lia. }
          rewrite <- nth_lookup, (ltac:(clear; easy) : 0 = Z.of_nat O) in kn.
          rewrite -> map_nth, retrievalFact in kn; [| lia | lia].
          rewrite -> bindDispatch, -> pushDispatch.
          remember (coerceInt _ _) as uj eqn:lk in |- * at 1.
          unfold update in lk. simpl in lk.
          unfold coerceInt in lk. rewrite !Z.mod_small in lk; try lia.
          subst uj. rewrite unfoldInvoke_S_Store.
          case_decide as nn; [| rewrite app_length map_length repeat_length lengthFill in nn; lia]. rewrite !leftIdentity.
          rewrite dropWithinLoopLiftToWithinLoop pushNumberSet2 pushNumberSet2.
          remember (Z.to_nat _) as tjh eqn:uwl in |- * at 1.
          rewrite (ltac:(lia) : tjh = ((length items + 1 - na) * (limit + 1) - S ej)%nat).
          remember (update _ _ _) as tyt eqn:tut in |- * at 1.
          assert (cqa : tyt = update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)).
          { subst tyt. clear. apply functional_extensionality_dep. intro ga. destruct ga; easy. }
          clear tut. subst tyt.
          remember (fun (x : arrayIndex0) => _) as tyt eqn:tut in |- * at 1.
          assert (nek : tyt = (fun x => match x with | arraydef_0__dp => <[((length items + 1 - na) * (limit + 1) - S ej)%nat:=yn]> ((map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - S ej))) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - S ej))%nat) | arraydef_0__message => [Z.of_nat (nth (length items - na - 1) items (0%nat, 0%nat)).2] | arraydef_0__n => [Z.of_nat (length items)] end)).
          { subst tyt. clear. apply functional_extensionality_dep. intro x.
            destruct x; easy. }
          clear tut. subst tyt.
          assert (td : <[((length items + 1 - na) * (limit + 1) - S ej)%nat:=yn]> ((map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - S ej))) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - S ej))%nat) = (map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - ej))) ++ repeat 0 (1000000 - ((length items + 1 - na) * (limit + 1) - ej))%nat).
          { apply list_eq. intro u.
            destruct (ltac:(lia) : u < ((length items + 1 - na) * (limit + 1) - S ej) \/ u = ((length items + 1 - na) * (limit + 1) - S ej) \/ ((length items + 1 - na) * (limit + 1) - S ej) < u)%nat as [dh | [dh | dh]].
            - rewrite list_lookup_insert_ne. { revert dh. clear. lia. }
              rewrite -> lookup_app_l, -> lookup_app_l; [| rewrite map_length lengthFill | rewrite map_length lengthFill]; try lia.
              remember (_ !! _) as ka1 eqn:qa1.
              remember (_ !! _) as ka2 eqn:qa2 in |- *.
              symmetry in qa1, qa2.
              destruct ka1 as [ka1 |].
              + destruct ka2 as [ka2 |].
                { assert (kt : default (Z.of_nat 0) (Some ka1) = default (Z.of_nat 0) (Some ka2)).
                  { rewrite <- qa1, <- qa2, <- !nth_lookup, !map_nth.
                    rewrite (ltac:(lia) : (length items + 1 - na) * (limit + 1) - ej = S ((length items + 1 - na) * (limit + 1) - S ej))%nat.
                    simpl. rewrite -> !nth_lookup.
                    rewrite -> lookup_app_l. { reflexivity. }
                    rewrite lengthFill. lia. }
                  simpl in kt. rewrite -> kt. reflexivity. }
                  pose proof lookup_ge_None_1 _ _ qa2 as j1.
                  pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ qa1) as j2.
                  rewrite map_length lengthFill in j1.
                  rewrite map_length lengthFill in j2.
                  lia.
              + pose proof lookup_ge_None_1 _ _ qa1 as j1.
                destruct ka2 as [ka2 |].
                { pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ qa2) as j2.
                  rewrite map_length lengthFill in j1.
                  rewrite map_length lengthFill in j2. lia. }
                reflexivity.
            - rewrite dh list_lookup_insert.
              { rewrite app_length map_length repeat_length lengthFill. lia. }
              remember (_ !! _) as ka eqn:qa. symmetry in qa.
              destruct ka as [ka |]; [| pose proof lookup_ge_None_1 _ _ qa as ta; rewrite app_length map_length repeat_length lengthFill in ta; lia].
              rewrite lookup_app_l in qa.
              { rewrite map_length lengthFill. lia. }
              assert (dak : yn = default (Z.of_nat O) (Some ka)).
              { rewrite <- qa, <- nth_lookup, map_nth.
                assert (ql : ((length items + 1 - na) * (limit + 1) - S ej = (length items - na) * (limit + 1) + (limit - ej))%nat).
                { rewrite (ltac:(lia) : (length items + 1 - na = (length items - na) + 1)%nat).
                  rewrite -> Nat.mul_add_distr_r, Nat.mul_1_l.
                  pose proof (ltac:(lia) : (ej <= limit)%nat) as cq.
                  revert cq. clear. nia. }
                rewrite -> ql, retrievalFact.
                { subst yn.
                  assert (km : reverse items !! (length (reverse items) - (length items - na - 1) - 1)%nat =
                  Some (nth (length items - na - 1) items (0%nat, 0%nat))).
                  { remember (_ !! _) as cm eqn:ls in |- *.
                    symmetry in ls.
                    destruct cm as [cm |].
                    { rewrite (ltac:(clear; easy) : cm = default (O, O) (Some cm)).
                      rewrite <- ls, nth_lookup.
                      rewrite reverse_lookup. { 
                      pose proof (ltac:(lia) : length items <> O) as dak.
                      rewrite reverse_length. revert ub dak. clear. lia. }
                      rewrite (ltac:(rewrite reverse_length; lia) : length items - S (length (reverse items) - (length items - na - 1) - 1) = (length items - na - 1))%nat.
                      reflexivity. }
                    pose proof lookup_ge_None_1 _ _ ls as lsv. rewrite reverse_length in lsv. lia. }
                  pose proof (take_drop_middle (reverse items) (length (reverse items) - (length items - na - 1) - 1) (nth (length items - na - 1) items (0%nat, 0%nat))) km as hg.
                  pose proof reverse_length items as vz.
                  rewrite (ltac:(lia) : (length (reverse items) - (length items - na - 1) = na + 1)%nat).
                  rewrite (ltac:(lia) : length (reverse items) - (length items - na) = na)%nat.
                  rewrite (ltac:(lia) : length (reverse items) - (length items - na - 1) - 1 = na)%nat in hg.
                  rewrite <- hg.
                  rewrite -> (ltac:(intros; listsEqual) : forall a b c, a ++ b :: c = (a ++ [b]) ++ c) at 1.
                  rewrite drop_app_ge.
                  { rewrite app_length take_length. simpl. lia. }
                  rewrite app_length take_length reverse_length (ltac:(lia) : (na `min` length items = na)%nat) (ltac:(clear; easy) : forall x, length [x] = 1%nat) Nat.sub_diag (ltac:(clear; easy) : forall x, drop 0 x = x) drop_app_ge take_length reverse_length (ltac:(lia) : (na `min` length items = na))%nat. { lia. }
                  rewrite Nat.sub_diag (ltac:(clear; easy) : forall x, drop 0 x = x).
                  simpl.
                  remember (nth (length items - na - 1) items (0%nat, 0%nat)) as ku eqn:iu.
                  destruct ku as [ku1 ku2].
                  rewrite -> (ltac:(clear; easy) : (ku1, ku2).1 = ku1) in *.
                  rewrite -> (ltac:(clear; easy) : (ku1, ku2).2 = ku2) in *.
                  case_decide as nk. { lia. }
                  rewrite (ltac:(lia) : (length (reverse items) - (length items - na - 1) = S na)%nat) in mid. lia. }
                - clear. lia.
                - lia. }
              simpl in dak. rewrite dak. reflexivity.
            - rewrite list_lookup_insert_ne. { revert dh. clear. lia. }
              rewrite -> lookup_app_r; [| rewrite -> map_length, lengthFill; lia].
              rewrite -> lookup_app_r; [| rewrite -> map_length, lengthFill; lia].
              remember (_ !! _) as t1 eqn:r1 in |- * at 1.
              remember (_ !! _) as t2 eqn:r2 in |- * at 1.
              destruct t1 as [t1 |].
              + destruct t2 as [t2 |].
                * assert (uh : default 0 (Some t1) = default 0 (Some t2)).
                  { rewrite -> r1, r2. rewrite <- !nth_lookup.
                    rewrite -> !nth_repeat. reflexivity. }
                  simpl in uh. rewrite uh.
                  reflexivity.
                * symmetry in r1, r2.
                  pose proof lookup_ge_None_1 _ _ r2 as d1.
                  pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ r1) as d2.
                  rewrite map_length repeat_length lengthFill in d1.
                  rewrite map_length repeat_length lengthFill in d2.
                  lia.
              + destruct t2 as [t2 |].
                * symmetry in r1, r2.
                  pose proof lookup_ge_None_1 _ _ r1 as d1.
                  pose proof lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ r2) as d2.
                  rewrite map_length repeat_length lengthFill in d1.
                  rewrite map_length repeat_length lengthFill in d2.
                  lia.
                * reflexivity. }
          rewrite td.
          rewrite ID2. reflexivity. }
          remember (fun (x : unit) => _) as seecont eqn:hseecont in |- * at 1.
          pose proof adv seecont 0 jk as [hwit hrew].
          assert (ll : ((length items + 1 - na) * (limit + 1) - ej = (length items + 1 - S na) * (limit + 1))%nat).
          { subst ej.
            pose proof (ltac:(lia) : (length items >= na)%nat) as fa. revert fa. clear. nia. }
          rewrite ll in hrew.
          rewrite hrew.
          clear hrew adv.
          subst seecont. rewrite dropWithinLoopLiftToWithinLoop.
          rewrite pushDispatch2 unfoldInvoke_S_Store.
          rewrite (ltac:(easy) : <[Z.to_nat 0:=coerceInt 0 32]> [hwit] = [0]).
          remember (fun (x : arrayIndex0) => _) as tw eqn:ew in |- * at 1.
          case_decide as cl; [| simpl in cl; lia].
          assert (mk : tw = fun (x : arrayIndex0) => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1))) ++ repeat 0 (1000000 - (length items + 1 - na) * (limit + 1))%nat | arraydef_0__message => [0] | arraydef_0__n => [Z.of_nat (length items)] end).
          { subst tw. apply functional_extensionality_dep. intro x. destruct x; easy. }
          rewrite mk. clear mk.
          pose proof IH ltac:(lia) as ID. clear IH.
          rewrite !bindAssoc !bindDispatch. rewrite !bindAssoc !bindDispatch in ID.
          rewrite ID. reflexivity. }
  rewrite (ltac:(lia) : (length items + 1 - na) * (limit + 1) = 0)%nat in wu.
  rewrite (ltac:(clear;easy) : map Z.of_nat (fill (reverse items) limit 0) = []) Nat.sub_0_r app_nil_l in wu.
  rewrite wu.
  rewrite pushDispatch2.
  rewrite unfoldInvoke_S_Retrieve. case_decide as dl; [| simpl in dl; lia].
  rewrite (ltac:(easy) : nth_lt [Z.of_nat (length items)] (Z.to_nat 0) dl = Z.of_nat (length items)).
  rewrite pushNumberGet2.
  rewrite pushNumberGet2.
  remember (coerceInt _ _) as dm eqn:wm in |- * at 1.
  unfold update in wm. simpl in wm.
  unfold coerceInt in wm. rewrite !Z.mod_small in wm; try lia.
  subst dm.
  rewrite pushDispatch2 unfoldInvoke_S_Retrieve.
  case_decide as nw;
  [| rewrite app_length map_length repeat_length lengthFill in nw; lia].
  rewrite !leftIdentity eliminateLift.
  rewrite (nth_lt_default _ _ _ 0) (ltac:(lia) : (Z.to_nat (Z.of_nat (length items) * (Z.of_nat limit + 1) + Z.of_nat limit)) = (length items) * (limit + 1) + limit)%nat.
  rewrite nth_lookup lookup_app_l. { rewrite map_length lengthFill. lia. }
  rewrite <- nth_lookup.
  remember (nth _ (map _ _) _) as df eqn:ff in |- * at 1.
  rewrite (ltac:(clear; easy) : 0 = Z.of_nat O) in ff.
  rewrite map_nth retrievalFact in ff. { lia. } { lia. }
  rewrite reverse_length Nat.sub_diag (ltac:(clear; easy) : forall x, drop 0 x = x) in ff.
  assert (ma : knapsack (reverse items) limit = knapsack items limit).
  { pose proof knapsackMax (reverse items) limit as [ga gb].
    pose proof knapsackMax items limit as [xa xb].
    assert (rsub : forall A (l1 l2 : list A), l1 `sublist_of` l2 -> reverse l1 `sublist_of` reverse l2).
    { clear. intros A l1 l2 i.
      induction i as [| x l1 l2 IH IJ | x l1 l2 IH IJ ].
      - easy.
      - rewrite !reverse_cons.
        apply sublist_app. { assumption. } { easy. }
      - rewrite reverse_cons.
        pose proof sublist_app _ _ [] [x] IJ ltac:(apply sublist_nil_l) as re.
        rewrite app_nil_r in re. exact re. }
    assert (frA : forall l p, (foldr (fun (x : nat * nat) (c : nat) => (x.2 + c)%nat) 0%nat (l ++ [p]))%nat = (foldr (fun (x : nat * nat) (c : nat) => x.2 + c) 0%nat l + p.2)%nat).
    { clear. intros l p.
      induction l as [| head tail IH].
      { simpl. lia. }
      rewrite !(ltac:(intros; listsEqual) : forall a b c, (a :: b) ++ [c] = a :: (b ++ [c])).
      destruct head as [m n].
      rewrite !foldrSum9 IH. lia. }
    assert (frev1 : forall r1, foldr (λ (_0 : nat * nat) (_1 : nat), (_0.2 + _1)%nat) 0%nat (reverse r1) = foldr (λ (_0 : nat * nat) (_1 : nat), (_0.2 + _1)%nat) 0%nat r1).
    { intro y.
      induction y as [| [a b] tail IH].
      { easy. }
      rewrite reverse_cons foldrSum9 frA. simpl. lia. }
    assert (frB : forall l p, (foldr (fun (x : nat * nat) (c : nat) => (x.1 + c)%nat) 0%nat (l ++ [p]))%nat = (foldr (fun (x : nat * nat) (c : nat) => x.1 + c) 0%nat l + p.1)%nat).
    { clear. intros l p.
      induction l as [| head tail IH].
      { simpl. lia. }
      rewrite !(ltac:(intros; listsEqual) : forall a b c, (a :: b) ++ [c] = a :: (b ++ [c])).
      destruct head as [m n].
      rewrite !foldrSum11 IH. lia. }
    assert (frev2 : forall r1, foldr (λ (_0 : nat * nat) (_1 : nat), (_0.1 + _1)%nat) 0%nat (reverse r1) = foldr (λ (_0 : nat * nat) (_1 : nat), (_0.1 + _1)%nat) 0%nat r1).
    { intro y.
      induction y as [| [a b] tail IH].
      { easy. }
      rewrite reverse_cons foldrSum11 frB. simpl. lia. }
    assert (ka1 : (knapsack (reverse items) limit <= knapsack items limit)%nat).
    { apply xb.
      destruct ga as [r1 [r2 [r3 r4]]].
      exists (reverse r1).
      pose proof rsub _ _ _ r2 as nac.
      rewrite reverse_involutive in nac. constructor. { exact nac. }
      rewrite frev1 frev2. tauto. }
    assert (ka2 : (knapsack items limit <= knapsack (reverse items) limit)%nat).
    { apply gb.
      destruct xa as [r1 [r2 [r3 r4]]].
      exists (reverse r1).
      pose proof rsub _ _ _ r2 as nac.
      constructor. { exact nac. }
      rewrite frev1 frev2. tauto. }
    lia. }
  rewrite ma in ff.
Admitted.
