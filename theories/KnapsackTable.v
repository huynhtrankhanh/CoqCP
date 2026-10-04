From stdpp Require Import numbers list.
From CoqCP Require Import Options Imperative Knapsack KnapsackCode ListsEqual.
From Generated Require Import Knapsack.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Coq.Logic.FunctionalExtensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Lemma knapsackReverse (items : list (nat * nat)) (limit : nat) : knapsack (reverse items) limit = knapsack items limit.
Proof.
 pose proof knapsackMax (reverse items) limit as [ga gb].
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
    lia.
Qed.

Lemma filledAnswerEq (items : list (nat * nat)) (limit : nat) :
  nth (length items * (limit + 1) + limit) (fill (reverse items) limit ((length items + 1) * (limit + 1))) 0%nat = knapsack items limit.
Proof.
  rewrite (@retrievalFact (reverse items) limit ((length items + 1) * (limit + 1)) (length items) limit ltac:(lia) ltac:(nia)).
  rewrite length_reverse Nat.sub_diag. simpl. apply knapsackReverse.
Qed.

Lemma filledAnswerOptimal (items : list (nat * nat)) (limit : nat) :
  isMaximum (nth (length items * (limit + 1) + limit) (fill (reverse items) limit ((length items + 1) * (limit + 1))) 0%nat)
    (fun value => exists choice, sublist choice items /\ foldr (fun item sum => (snd item + sum)%nat) 0%nat choice = value /\ (foldr (fun item sum => (fst item + sum)%nat) 0%nat choice <= limit)%nat).
Proof. rewrite filledAnswerEq. apply knapsackMax. Qed.


Definition tableSize (items : list (nat * nat)) limit := ((length items + 1) * (limit + 1))%nat.
Definition table (items : list (nat * nat)) limit top :=
  map Z.of_nat (fill (reverse items) limit top) ++ repeat 0%Z (tableSize items limit - top).

Lemma table_length items limit top (h : (top <= tableSize items limit)%nat) :
  length (table items limit top) = tableSize items limit.
Proof. unfold table. rewrite length_app length_map lengthFill repeat_length. lia. Qed.

Lemma table_read items limit top row cap
  (hCap : (cap <= limit)%nat) (hIndex : (row * (limit + 1) + cap < top)%nat) :
  nth (row * (limit + 1) + cap) (table items limit top) 0%Z =
  Z.of_nat (knapsack (reverse (take row items)) cap).
Proof.
  unfold table. rewrite app_nth1; [rewrite length_map lengthFill; lia |].
  change (nth (row * (limit + 1) + cap) (map Z.of_nat (fill (reverse items) limit top)) (Z.of_nat 0) = Z.of_nat (knapsack (reverse (take row items)) cap)).
  rewrite map_nth (@retrievalFact (reverse items) limit top row cap hCap hIndex).
  rewrite length_reverse -reverse_take. reflexivity.
Qed.

Lemma prefix_step items row (h : (row < length items)%nat) :
  reverse (take (S row) items) = nth row items (0%nat, 0%nat) :: reverse (take row items).
Proof.
  assert (lookup : items !! row = Some (nth row items (0%nat, 0%nat))).
  { rewrite nth_lookup. destruct (items !! row) eqn:e; [reflexivity |].
    apply lookup_ge_None_1 in e. lia. }
  rewrite (take_S_r _ _ _ lookup) reverse_app. reflexivity.
Qed.

Lemma table_insert items limit row cap
  (hRow : (row < length items)%nat) (hCap : (cap <= limit)%nat) :
  let top := (S row * (limit + 1) + cap)%nat in
  <[top := Z.of_nat (knapsack (reverse (take (S row) items)) cap)]>(table items limit top) =
  table items limit (S top).
Proof.
  intro top. unfold table. rewrite insert_app_r_alt; [rewrite length_map lengthFill; lia |].
  rewrite length_map lengthFill Nat.sub_diag.
  assert (hTop : (top < tableSize items limit)%nat) by (unfold top, tableSize; nia).
  replace (tableSize items limit - top)%nat with (S (tableSize items limit - S top)) by lia.
  cbn [repeat insert].
  cbn [fill]. rewrite map_app. cbn [map].
  rewrite <- app_assoc. f_equal.
  f_equal. f_equal.
  unfold top.
  rewrite Nat.div_add_l; [lia |].
  rewrite Nat.div_small; [lia |].
  rewrite Nat.add_0_r.
  rewrite Nat.add_mod; [lia |].
  rewrite Nat.mod_mul; [lia |].
  rewrite Nat.add_0_l Nat.mod_mod; [lia |].
  rewrite Nat.mod_small; [lia |].
  rewrite length_reverse -reverse_take. reflexivity.
Qed.

Lemma knapsack_sum items cap : (knapsack items cap <= list_sum (map snd items))%nat.
Proof.
  induction items as [| [w v] items IH] in cap |- *; simpl; [lia |].
  destruct (decide (cap < w)%nat); specialize (IH cap) as h1; try lia.
  specialize (IH (cap - w)%nat). nia.
Qed.

Lemma sum_take (items : list (nat * nat)) row : (list_sum (map snd (take row items)) <= list_sum (map snd items))%nat.
Proof.
  induction items as [| [w v] items IH] in row |- *; destruct row as [| row]; simpl; try lia.
  specialize (IH row). lia.
Qed.

Lemma sum_reverse (items : list (nat * nat)) : list_sum (map snd (reverse items)) = list_sum (map snd items).
Proof.
  induction items as [| [w v] items IH]; [reflexivity |].
  rewrite reverse_cons map_app list_sum_app IH. simpl. lia.
Qed.

Lemma table_base items limit : table items limit (limit + 1) = repeat 0%Z (tableSize items limit).
Proof.
  unfold table.
  assert (zero : forall top, (top <= limit + 1)%nat -> map Z.of_nat (fill (reverse items) limit top) = repeat 0%Z top).
  { intros top h. induction top as [| top IH]; [reflexivity |].
    cbn [fill]. rewrite map_app IH; [lia |].
    rewrite Nat.div_small; [lia |]. rewrite Nat.sub_0_r drop_all. cbn [knapsack map].
    rewrite <- repeat_cons. reflexivity. }
  rewrite zero; [lia |]. rewrite <- repeat_app. f_equal. unfold tableSize; nia.
Qed.
