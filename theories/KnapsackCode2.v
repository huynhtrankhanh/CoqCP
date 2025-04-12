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
  rewrite up. clear up. rewrite !leftIdentity pushNumberSet2 pushDispatch2 bindDispatch unfoldInvoke_S_Retrieve. case_decide as yb; [| simpl in yb; lia]. clear i8.
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
  assert (wu : forall cont msg jk, invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1))%nat) ++ repeat 0 (1000000 - (length items + 1 - na) * (limit + 1))%nat | arraydef_0__message => [msg] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (de >>= cont)) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1) * (limit + 1))%nat) ++ repeat 0 (1000000 - (length items + 1) * (limit + 1))%nat | arraydef_0__message => [msg] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (cont tt))).
  { intros cont msg jk.
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
        rewrite IH. { lia. }
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
    assert (adv : forall cont msg jk, invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1) - ej)%nat) ++ repeat 0 (1000000 - (length items + 1 - na) * (limit + 1) - ej)%nat | arraydef_0__message => [msg] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (dk >>= cont)) = invokeContractAux (repeat 1 20) (repeat 0 20) 0 state state (generateData items limit) 1 arrayIndex0 arrayIndexEqualityDecidable0 (arrayType arrayIndex0 environment0) (fun x => match x with | arraydef_0__dp => map Z.of_nat (fill (reverse items) limit ((length items + 1 - na) * (limit + 1))%nat) ++ repeat 0 (1000000 - (length items + 1 - na) * (limit + 1))%nat | arraydef_0__message => [msg] | arraydef_0__n => [Z.of_nat (length items)] end) jk (eliminateLocalVariables xpred0 (update (fun=> 0) vardef_0__main_limit (Z.of_nat limit)) (fun=> repeat 0 20) (cont tt))).
    { clear wg. intros cont1 msg1 jk1. subst dk. induction ej as [| ej ID].
      { rewrite !Nat.sub_0_r.
        rewrite (ltac:(simpl; reflexivity) : loop 0 _ = _).
        rewrite !leftIdentity. reflexivity. }
      rewrite loop_S.
      rewrite <- !bindAssoc.
      rewrite !leftIdentity.
      rewrite -> dropWithinLoopLiftToWithinLoop.
      rewrite <- !bindAssoc, -> eliminateLift.
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
        lia. } } }
Admitted.
