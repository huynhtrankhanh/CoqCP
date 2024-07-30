From CoqCP Require Import Options ListsEqual.
From stdpp Require Import numbers list.

Fixpoint multiply (n : nat) (l : list nat) :=
  match n with
  | 0 => []
  | S n => l ++ multiply n l
  end.

Fixpoint lexLess (l1 l2 : list nat) :=
  match l1, l2 with
  | _, [] => false
  | [], (_ :: _) => true
  | (a :: b), (a' :: b') => bool_decide (a < a') || (bool_decide (a = a') && lexLess b b')
  end.

Lemma lexLessTrichotomy (l1 l2 : list nat) : lexLess l1 l2 \/ lexLess l2 l1 \/ l1 = l2.
Proof.
  induction l1 as [| a l1 IH] in l2 |- *.
  - destruct l2; simpl in *; tauto.
  - destruct l2 as [| b l2]; simpl in *; repeat case_bool_decide; rewrite ?orb_True, ?andb_True; try pose proof IH l2; try (lia || intuition). intuition congruence.
Qed.

Lemma lexLessTransitive (l1 l2 l3 : list nat) (h1 : lexLess l1 l2) (h2 : lexLess l2 l3) : lexLess l1 l3.
Proof.
  induction l1 as [| a l1 IH] in l2, l3, h1, h2 |- *.
  - destruct l2; destruct l3; now simpl in *.
  - destruct l2 as [| b l2]; destruct l3 as [| c l3]; simpl in *; try easy.
    repeat case_bool_decide; try lia; rewrite orb_True, andb_True in *; simpl in *; destruct h1; destruct h2; try now (done || lia). right. split; try easy. now apply (IH l2).
Qed.

Lemma lexLessAppend1 (l1 l2 l3 : list nat) (h : lexLess l2 l3) : lexLess (l1 ++ l2) (l1 ++ l3).
Proof.
  induction l1 as [| a l1 IH] in l2, l3, h |- *.
  - now rewrite app_nil_l.
  - simpl. rewrite ?orb_True, ?andb_True.
    repeat case_bool_decide; right; try (done || lia).
    split; try easy. now apply (IH l2).
Qed.

Lemma lexLessAppend2 (l1 l2 l3 : list nat) (h : lexLess (l1 ++ l2) (l1 ++ l3)) : lexLess l2 l3.
Proof.
  induction l1 as [| a l1 IH] in l2, l3, h |- *.
  - now rewrite !app_nil_l in *.
  - simpl in *. rewrite ?orb_True, ?andb_True in *.
    repeat case_bool_decide; try (lia || done || intuition). easy.
Qed.

Lemma lexLessAppend (l1 l2 l3 : list nat) : lexLess l2 l3 <-> lexLess (l1 ++ l2) (l1 ++ l3).
Proof.
  split.
  - apply lexLessAppend1.
  - apply lexLessAppend2.
Qed.

Lemma lexLessDiscard (l1 l2 l3 l4 : list nat) (h : lexLess l1 l2) (hLength : length l1 = length l2) : lexLess (l1 ++ l3) (l2 ++ l4).
Proof.
  induction l1 as [| a l1 IH] in l2, h, hLength |- *.
  - now destruct l2 as [| b l2].
  - destruct l2 as [| b l2]; try easy.
    simpl in *. rewrite ?orb_True, ?andb_True in *. repeat case_bool_decide; destruct h; try (done || lia); try now left.
    right. split; try easy. apply IH; try (done || lia). tauto.
Qed.

Lemma lexLessIrrefl (l : list nat) (h : lexLess l l) : False.
Proof.
  induction l as [| head tail IH].
  - easy.
  - simpl in *. rewrite ?orb_True, ?andb_True in *. repeat case_bool_decide; try (done || lia). destruct h; try (tauto || lia).
Qed.

Lemma repeatA (a b : list nat) (n : nat) (h : lexLess (a ++ b) (b ++ a)) : lexLess (multiply (S n) a ++ b) (b ++ multiply (S n) a).
Proof.
  induction n as [| n IH]; simpl in *.
  - now rewrite !app_nil_r.
  - pose proof lexLessAppend1 a _ _ IH as h1.
    pose proof lexLessDiscard _ _ (a ++ multiply n a) (a ++ multiply n a) h ltac:(rewrite !app_length; lia) as h2.
    rewrite <- !app_assoc in *.
    exact (lexLessTransitive _ _ _ h1 h2).
Qed.

Lemma multiplyAppLeft a n : a ++ multiply n a = multiply (S n) a.
Proof. easy. Qed.

Lemma multiplyAppRight a n : multiply n a ++ a = multiply (S n) a.
Proof.
  induction n as [| n IH].
  - simpl. listsEqual.
  - simpl in *. now rewrite <- !app_assoc, !IH.
Qed.

Lemma multiplyNil (n : nat) : multiply n [] = [].
Proof.
  induction n as [| n IH]; easy.
Qed.

Lemma repeatB (a b : list nat) (n : nat) (h : lexLess (a ++ b) (b ++ a)) : lexLess (a ++ multiply (S n) b) (multiply (S n) b ++ a).
Proof.
  induction n as [| n IH]; simpl in *.
  - now rewrite !app_nil_r.
  - pose proof lexLessDiscard _ _ b b IH ltac:(rewrite !app_length; lia) as h1.
    pose proof lexLessAppend1 (b ++ multiply n b) _ _ h as h2.
    rewrite <- !app_assoc in *.
    pose proof (lexLessTransitive _ _ _ h1 h2) as goal.
    rewrite (ltac:(listsEqual) : b ++ multiply n b ++ a = (b ++ multiply n b) ++ a).
    assert (hMultiplyApp : b ++ multiply n b = multiply n b ++ b).
    { now rewrite multiplyAppLeft, multiplyAppRight. }
    now rewrite hMultiplyApp, <- !app_assoc.
Qed.

Lemma multiplyLength n l : length (multiply n l) = n * length l.
Proof.
  induction n as [| n IH].
  - easy.
  - simpl. rewrite app_length. lia.
Qed.

Lemma lexLessSameLengthAppend (l1 l2 l3 l4 : list nat) (hLength : length l1 = length l2) (hDiff : l1 <> l2) (h : lexLess (l1 ++ l3) (l2 ++ l4)) : lexLess l1 l2.
Proof.
  induction l1 as [| a l1 IH] in l2, hLength, hDiff, h |- *.
  - simpl in *. symmetry in hLength. pose proof nil_length_inv _  hLength as hEnd. now symmetry in hEnd.
  - destruct l2 as [| b l2]; simpl in *; try lia.
    rewrite !orb_True, !andb_True in *.
    repeat case_bool_decide; destruct h as [h | h]; try (lia || tauto); try now left.
    pose proof (ltac:(assumption) : a = b) as hEq.
    rewrite hEq in hDiff. destruct (decide (l1 = l2)) as [hDiffInner | hDiffInner]; try now rewrite hDiffInner in *.
    right. split; try easy. apply IH; (lia || tauto).
Qed.

Lemma repeatAEqual (a b : list nat) (n : nat) (h : a ++ b = b ++ a) : multiply (S n) a ++ b = b ++ multiply (S n) a.
Proof.
  induction n as [| n IH].
  - simpl. now rewrite !app_nil_r.
  - simpl in *. rewrite <- !app_assoc in *. rewrite IH, app_assoc, h. listsEqual.
Qed.

Lemma repeatBEqual (a b : list nat) (n : nat) (h : a ++ b = b ++ a) : a ++ multiply (S n) b = multiply (S n) b ++ a.
Proof.
  induction n as [| n IH].
  - simpl. now rewrite !app_nil_r.
  - simpl in *. rewrite <- !app_assoc in *. rewrite <- IH, app_assoc, h. listsEqual.
Qed.

Lemma repeatABEqual (a b : list nat) (h : a ++ b = b ++ a) : multiply (length b) a = multiply (length a) b.
Proof.
  destruct (decide (length a = 0)) as [h1 | h1]; rewrite ?h1, ?(nil_length_inv _ h1), ?app_nil_r, ?multiplyNil; simpl; try reflexivity.
  destruct (decide (length b = 0)) as [h2 | h2]; rewrite ?h2, ?(nil_length_inv _ h2), ?app_nil_r, ?multiplyNil; simpl; try reflexivity.
  pose proof repeatBEqual _ _ (length a - 1) (repeatAEqual _ _ (length b - 1) h) as hExtended.
  rewrite (ltac:(lia) : S (length a - 1) = length a), (ltac:(lia) : S (length b - 1) = length b) in *.
  assert (hTake : forall a b: list nat, forall n : nat, a = b -> take n a = take n b).
  { intros. congruence. }
  pose proof hTake _ _ (length a * length b) hExtended.
  pose proof take_app (multiply (length b) a) (multiply (length a) b) (length (multiply (length b) a)).
  pose proof take_app (multiply (length a) b) (multiply (length b) a) (length (multiply (length a) b)).
  rewrite Nat.sub_diag, firstn_O, app_nil_r, firstn_all, multiplyLength, (ltac:(lia) : length a * length b = length b * length a) in *. congruence.
Qed.

Lemma repeatABLexLess (a b : list nat) (h : lexLess (a ++ b) (b ++ a)) : lexLess (multiply (length b) a) (multiply (length a) b).
Proof.
  destruct (decide (length a = 0)) as [h1 | h1]; rewrite ?h1, ?(nil_length_inv _ h1), ?app_nil_r, ?multiplyNil in *; simpl; try (pose proof lexLessIrrefl b; tauto).
  destruct (decide (length b = 0)) as [h2 | h2]; rewrite ?h2, ?(nil_length_inv _ h2), ?app_nil_r, ?multiplyNil in *; simpl; try (pose proof lexLessIrrefl a; tauto).
  pose proof repeatB _ _ (length a - 1) (repeatA _ _ (length b - 1) h) as hExtended.
  rewrite (ltac:(lia) : S (length a - 1) = length a), (ltac:(lia) : S (length b - 1) = length b) in *.
  destruct (decide (multiply (length b) a = multiply (length a) b)) as [hEq | hEq].
  - rewrite hEq in *. pose proof lexLessIrrefl _ hExtended. tauto.
  - exact (lexLessSameLengthAppend _ _ _ _ (ltac:(rewrite !multiplyLength; lia) : length (multiply (length b) a) = length (multiply (length a) b)) hEq hExtended).
Qed.

Lemma repeatCompare (a b : list nat) : lexLess (a ++ b) (b ++ a) <-> lexLess (multiply (length b) a) (multiply (length a) b).
Proof.
  pose proof lexLessTrichotomy (a ++ b) (b ++ a) as hSplit.
  destruct hSplit as [h | [h | h]]; split; intro h3; try pose proof repeatABEqual a b h as h1; try pose proof repeatABLexLess a b h as h1; try pose proof repeatABLexLess b a h as h1; try easy.
  - now pose proof lexLessIrrefl _ (lexLessTransitive _ _ _ h h3).
  - now pose proof lexLessIrrefl _ (lexLessTransitive _ _ _ h3 h1).
  - rewrite h in h3. now pose proof lexLessIrrefl _ h3.
  - rewrite h1 in h3. now pose proof lexLessIrrefl _ h3.
Qed.
