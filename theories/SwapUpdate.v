From stdpp Require Import numbers list.
From CoqCP Require Import Options ListDecomposition ListsEqual.

(* all indices 0 based *)
Definition swap {A : Type} (l : list A) (i j : nat) (default : A) :=
  let leftElement := nth i l default in
  let rightElement := nth j l default in
  let updated := <[i := rightElement]> l in
  <[j := leftElement]> updated.

Lemma updateAtIndexLength {A : Type} (l : list A) (value : A) : <[length l := value]> l = l.
Proof.
  induction l as [| head l IHl]; unfold alter; try easy; simpl; unfold alter in IHl; rewrite IHl; easy.
Qed.

Lemma updateAtIndexLengthPlusSomething {A : Type} (l : list A) (value : A) (something : nat) : <[length l + something := value]> l = l.
Proof.
  induction l as [| head l IHl]; unfold alter; try easy; simpl; unfold alter in IHl; rewrite IHl; easy.
Qed.

Lemma updateApp {A : Type} (l1 l2 : list A) (value : A) (i : nat) : <[length l1 + i := value]> (l1 ++ l2) = l1 ++ <[i := value]> l2.
Proof.
  induction l1 as [| head l1 IHl1]; unfold alter; try easy; simpl; unfold alter in IHl1; rewrite IHl1; easy.
Qed.

Lemma updateAppZero {A : Type} (l1 l2 : list A) (value : A) : <[length l1 := value]> (l1 ++ l2) = l1 ++ <[0 := value]> l2.
Proof.
  induction l1 as [| head l1 IHl1]; unfold alter; try easy; simpl; unfold alter in IHl1; rewrite IHl1; easy.
Qed.

Lemma nthApp {A : Type} (l1 l2 : list A) (i : nat) (default : A) : nth (length l1 + i) (l1 ++ l2) default = nth i l2 default.
Proof.
  induction l1 as [| head l1 IHl1]; unfold nth; try easy; simpl; unfold nth in IHl1; rewrite IHl1; easy.
Qed.

Lemma nthAppZero {A : Type} (l1 l2 : list A) (default : A) : nth (length l1) (l1 ++ l2) default = nth 0 l2 default.
Proof.
  induction l1 as [| head l1 IHl1]; unfold nth; try easy; simpl; unfold nth in IHl1; rewrite IHl1; easy.
Qed.

Lemma swapChopOff {A : Type} (l1 l2 : list A) (i j : nat) (default : A) : swap (l1 ++ l2) (length l1 + i) (length l1 + j) default = l1 ++ swap l2 i j default.
Proof.
  induction l1 as [| head l1 IHl1]; simpl; try easy.
  unfold swap. destruct i; destruct j; destruct l1; simpl; try easy; simpl in IHl1; rewrite ?IHl1, ?app_nil_r, ?Nat.add_0_r; simpl; rewrite ?updateAtIndexLength, ?updateAtIndexLengthPlusSomething, ?updateApp, ?updateAppZero, ?nthApp, ?nthAppZero, ?updateApp; easy.
Qed.

Lemma swapChopOff' {A : Type} (l1 l2 : list A) (j : nat) (default : A) : swap (l1 ++ l2) (length l1) (length l1 + j) default = l1 ++ swap l2 0 j default.
Proof.
  induction l1 as [| head l1 IHl1]; simpl; try easy.
  unfold swap. destruct j; destruct l1; simpl; try easy; simpl in IHl1; rewrite ?IHl1, ?app_nil_r, ?Nat.add_0_r; simpl; rewrite ?updateAtIndexLength, ?updateAtIndexLengthPlusSomething, ?updateApp, ?updateAppZero, ?nthApp, ?nthAppZero, ?updateApp; easy.
Qed.

Lemma swapApp {A : Type} (l1 l2 l3 : list A) (a b default : A) : swap (l1 ++ [a] ++ l2 ++ [b] ++ l3) (length l1) (length l1 + length l2 + 1) default = l1 ++ [b] ++ l2 ++ [a] ++ l3.
Proof.
  rewrite <- Nat.add_assoc, swapChopOff'.
  induction l2; simpl; unfold swap.
  - unfold alter. simpl. easy.
  - rewrite Nat.add_1_r. simpl. rewrite nthAppZero. simpl. rewrite updateAppZero. simpl. easy.
Qed.

Lemma swapPreservesLength {A : Type} (l : list A) (default : A) (i j : nat) : length (swap l i j default) = length l.
Proof.
  unfold swap. rewrite ?insert_length. reflexivity.
Qed.

Lemma updateSelf {A : Type} (l : list A) (default : A) (i : nat) : <[i := nth i l default]> l = l.
Proof.
  revert i. induction l as [| head l IHl]; intro i; simpl; destruct i; try simpl; rewrite ?IHl; reflexivity.
Qed.

Lemma swapSelf {A : Type} (l : list A) (default : A) (i : nat) : swap l i i default = l.
Proof.
  unfold swap. rewrite ?updateSelf. reflexivity.
Qed.

Lemma nthTake {A : Type} (l : list A) (default : A) (i j : nat) (hLt : i < j) : nth i l default = nth i (take j l) default.
Proof.
  revert l hLt. revert j. induction i as [| i IHi]; intros j l hLt.
  - destruct l; rewrite ?take_nil; simpl.
    + reflexivity.
    + destruct j; try lia. simpl. reflexivity.
  - destruct l; rewrite ?take_nil; simpl.
    + reflexivity.
    + destruct j; try lia. simpl. apply IHi. lia.
Qed.

Lemma nthConsDrop {A : Type} (l : list A) (default : A) (hNotNil : l <> []) (i : nat) (hLt : i < length l) : nth i l default :: drop (S i) l = drop i l.
Proof.
  revert hNotNil hLt. revert l.
  induction i as [| i IHi]; intros l hNotNil hLt.
  - destruct l; easy.
  - destruct l; simpl; try easy. apply IHi.
    + intro h. rewrite h in hLt. simpl in hLt. lia.
    + simpl in hLt. lia.
Qed.

Lemma swapIndices {A : Type} (l : list A) (default : A) (i j : nat) : swap l i j default = swap l j i default.
Proof.
  unfold swap.
  assert (hCases : i = j \/ i <> j). { lia. }
  destruct hCases as [h | h].
  - rewrite h. reflexivity.
  - rewrite list_insert_commute; try lia. reflexivity.
Qed.

Lemma swapTwice' {A : Type} (l : list A) (default : A) (i j : nat) (hIJ : i < j) (hJ : j < length l) : swap (swap l i j default) i j default = l.
Proof.
  rewrite (listDecomposition l i j ltac:(lia) ltac:(lia) default).
  assert (takeLength : i = length (take i l)). { rewrite take_length. lia. }
  assert (hRewrite : forall x y, swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) i j default = swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) (length (take i l)) j default). { intros. rewrite <- ?takeLength. easy. }
  rewrite hRewrite. clear hRewrite takeLength.
  assert (takeLength : j = length (take i l) + length (drop (S i) (take j l)) + 1).
  { rewrite take_length, drop_length, take_length.
    assert (subtask1 : i `min` length l = i). { lia. }
    assert (subtask2 : j `min` length l = j). { lia. }
    rewrite subtask1, subtask2. lia. }
  assert (hRewrite : forall x y, swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) (length (take i l)) j default = swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) (length (take i l)) (length (take i l) + length (drop (S i) (take j l)) + 1) default). { rewrite <- ?takeLength. easy. }
  rewrite hRewrite, swapApp. clear hRewrite takeLength.
  assert (takeLength : i = length (take i l)). { rewrite take_length. lia. }
  assert (hRewrite : forall x y, swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) i j default = swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) (length (take i l)) j default). { intros. rewrite <- ?takeLength. easy. }
  rewrite hRewrite. clear hRewrite takeLength.
  assert (takeLength : j = length (take i l) + length (drop (S i) (take j l)) + 1).
  { rewrite take_length, drop_length, take_length.
    assert (subtask1 : i `min` length l = i). { lia. }
    assert (subtask2 : j `min` length l = j). { lia. }
    rewrite subtask1, subtask2. lia. }
  assert (hRewrite : forall x y, swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) (length (take i l)) j default = swap (take i l ++ [x] ++ drop (S i) (take j l) ++ [y] ++ drop (j + 1) l) (length (take i l)) (length (take i l) + length (drop (S i) (take j l)) + 1) default). { rewrite <- ?takeLength. easy. }
  rewrite hRewrite, swapApp. clear hRewrite takeLength.
  reflexivity.
Qed.

Lemma swapTwice {A : Type} (l : list A) (default : A) (i j : nat) (hI : i < length l) (hJ : j < length l) : swap (swap l i j default) i j default = l.
Proof.
  assert (hWlog : i < j \/ j < i \/ i = j). { lia. }
  destruct hWlog as [hWlog | [hWlog | hWlog]].
  - apply swapTwice'; lia.
  - rewrite ?(swapIndices _ default i j).
    apply (swapTwice' _ _ j i); lia.
  - rewrite hWlog, ?swapSelf. reflexivity.
Qed.

Lemma swapTwiceVariant {A : Type} (l : list A) (default : A) (i j : nat) (hI : i < length l) (hJ : j < length l) : swap (swap l i j default) j i default = l.
Proof.
  rewrite swapIndices. apply swapTwice; lia.
Qed.

Lemma swapDecomposition {A : Type} (l : list A) (default : A) (i j : nat) (hLt : i < j) (hJ : j < length l) : swap l i j default = take i l ++ [nth j l default] ++ drop (S i) (take j l) ++ [nth i l default] ++ drop (j + 1) l.
Proof.
  rewrite (listDecomposition l i j ltac:(lia) ltac:(lia) default).
  assert (takeLength : i = length (take i l)). { rewrite take_length. lia. }
  assert (hRewrite : swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) i j default = swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) j default). { rewrite <- ?takeLength. easy. }
  rewrite hRewrite. clear hRewrite takeLength.
  assert (takeLength : j = length (take i l) + length (drop (S i) (take j l)) + 1).
  { rewrite take_length, drop_length, take_length.
    assert (subtask1 : i `min` length l = i). { lia. }
    assert (subtask2 : j `min` length l = j). { lia. }
    rewrite subtask1, subtask2. lia. }
  assert (hRewrite : swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) j default = swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) (length (take i l) + length (drop (S i) (take j l)) + 1) default). { rewrite <- ?takeLength. easy. }
  rewrite hRewrite, swapApp. clear hRewrite takeLength.
  rewrite <- (listDecomposition l i j ltac:(lia) ltac:(lia) default). reflexivity.
Qed.

Lemma nthSwap' {A : Type} (l : list A) (default : A) (i j : nat) (hWlog : i < j) (hJ : j < length l) : nth i (swap l i j default) default = nth j l default.
  rewrite (listDecomposition l i j ltac:(lia) ltac:(lia) default).
  assert (takeLength : i = length (take i l)). { rewrite take_length. lia. }
  assert (hRewrite : swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) i j default = swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) j default). { rewrite <- ?takeLength. easy. }
  rewrite hRewrite. clear hRewrite takeLength.
  assert (takeLength : j = length (take i l) + length (drop (S i) (take j l)) + 1).
  { rewrite take_length, drop_length, take_length.
    assert (subtask1 : i `min` length l = i). { lia. }
    assert (subtask2 : j `min` length l = j). { lia. }
    rewrite subtask1, subtask2. lia. }
  assert (hRewrite : swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) j default = swap (take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l) (length (take i l)) (length (take i l) + length (drop (S i) (take j l)) + 1) default). { rewrite <- ?takeLength. easy. }
  rewrite hRewrite, swapApp. clear hRewrite takeLength.
  pose proof nthAppZero (take i l) as H.
  rewrite take_length in H.
  assert (hEqI : i `min` length l = i). { lia. }
  rewrite hEqI in H.
  rewrite H. simpl.
  assert (H' : take i l ++ nth i l default :: drop (S i) (take j l) = take j l).
  { assert (subtask1 : take i l = take i (take j l)).
    { rewrite take_take.
      assert (hIJ : i `min` j = i). { lia. }
      rewrite hIJ. reflexivity. }
    rewrite subtask1.
    assert (subtask2 : nth i l default = nth i (take j l) default).
    { apply nthTake. lia. }
    assert (hNthCons : nth i l default :: drop (S i) (take j l) = drop i (take j l)).
    { rewrite subtask2. apply nthConsDrop.
      - intro h.
        assert (hTakeJ : length (take j l) = j).
        { rewrite take_length. lia. }
        assert (hContradiction : j = 0).
        { rewrite <- hTakeJ, h. easy. }
        lia.
      - rewrite take_length. lia. }
    rewrite hNthCons, take_drop. reflexivity. }
    assert (hRebracketing : forall a c e : list A, forall b d : A, a ++ b :: c ++ d :: e = (a ++ b :: c) ++ d :: e).
    { intros. listsEqual. }
    rewrite hRebracketing, H'.
    rewrite Nat.add_1_r, nthConsDrop; try lia.
    - rewrite take_drop. reflexivity.
    - intro h. rewrite h in *. simpl in *. lia.
Qed.

Lemma nthSwap {A : Type} (l : list A) (default : A) (i j : nat) (hI : i < length l) (hJ : j < length l) : nth i (swap l i j default) default = nth j l default.
Proof.
  assert (hWlog : i = j \/ i < j \/ j < i). { lia. }
  destruct hWlog as [hWlog | [hWlog | hWlog]].
  - rewrite hWlog, swapSelf. reflexivity.
  - apply nthSwap'; lia.
  - pose proof nthSwap' (swap l i j default) default j i as H.
    rewrite swapPreservesLength, swapIndices in H; rewrite ?swapPreservesLength; try lia. rewrite swapTwice in H; try lia. rewrite H; try lia. reflexivity.
Qed.

Lemma nthSwapVariant {A : Type} (l : list A) (default : A) (i j : nat) (hI : i < length l) (hJ : j < length l) : nth i (swap l j i default) default = nth j l default.
Proof.
  rewrite swapIndices, nthSwap; try lia. reflexivity.
Qed.

Lemma nthUpdate {A : Type} (l : list A) (default : A) (i : nat) (value : A) (hLt : i < length l) : nth i (<[i := value]> l) default = value.
Proof.
  revert hLt; revert i; induction l as [| head l IHl]; intros i hLt; unfold alter; try easy; simpl; unfold alter in IHl; destruct i; simpl; rewrite ?IHl; simpl in *; try lia; reflexivity.
Qed.

Lemma nthUpdateExcept {A : Type} (l : list A) (default : A) (i uninvolved : nat) (value : A) (hLt : i < length l) (hUninvolved : uninvolved <> i) : nth uninvolved (<[i := value]> l) default = nth uninvolved l default.
Proof.
  revert hLt; revert hUninvolved; revert i uninvolved; induction l as [| head l IHl]; intros i uninvolved hUninvolved hLt; unfold alter; try easy; unfold alter in IHl; destruct i; rewrite ?IHl; simpl in hLt; try lia.
  - simpl. destruct uninvolved; try lia; reflexivity.
  - simpl. destruct uninvolved; try lia; try reflexivity.
    apply IHl; lia.
Qed.

Lemma nthSwapExcept {A : Type} (l : list A) (default : A) (i j uninvolved : nat) (hI : i < length l) (hJ : j < length l) (hUninvolvedI : uninvolved <> i) (hUninvolvedJ : uninvolved <> j) : nth uninvolved (swap l i j default) default = nth uninvolved l default.
Proof.
  unfold swap. rewrite ?nthUpdateExcept; rewrite ?insert_length; try lia; reflexivity.
Qed.

Lemma nthSwapExceptVariant {A : Type} (l : list A) (default : A) (i j uninvolved : nat) (hI : i < length l) (hJ : j < length l) (hUninvolvedI : uninvolved <> i) (hUninvolvedJ : uninvolved <> j) : nth uninvolved (swap l j i default) default = nth uninvolved l default.
Proof.
  rewrite swapIndices, nthSwapExcept; try lia. reflexivity.
Qed.

Lemma oneDifferentPlace {A : Type} `{EqDecision A} (l1 l2 : list A) (default : A) (hDiff : l1 <> l2) (hSameLength : length l1 = length l2) : exists i, i < length l1 /\ nth i l1 default <> nth i l2 default.
Proof.
  induction l1 as [| head tail IH] in l2, hDiff, hSameLength |- *.
  - simpl in hSameLength. pose proof nil_length_inv _ (eq_sym hSameLength). congruence.
  - destruct l2 as [| head1 tail1]; try easy.
    remember (bool_decide (head = head1)) as split eqn:hSplit.
    destruct split; symmetry in hSplit; rewrite <- ?Is_true_true, <- ?Is_true_false, bool_decide_spec in hSplit.
    + rewrite hSplit in *.
      destruct (IH tail1 ltac:(congruence) ltac:(simpl in *; lia)) as [w h].
      exists (S w). simpl. split; (lia || easy).
    + exists 0. simpl. split; (lia || easy).
Qed.

Lemma takeAppLt {A : Type} (l1 l2 : list A) (i : nat) (hI : i <= length l1) : take i (l1 ++ l2) = take i l1.
Proof.
  induction l1 as [| head tail IH] in i, hI |- *; simpl in *;
  try (rewrite (ltac:(lia) : i = 0) in *; easy).
  destruct i; try easy. simpl. rewrite IH; (done || lia).
Qed.

Lemma takeRepeat {A : Type} (x : A) (i j : nat) (hIJ : i <= j) : take i (repeat x j) = repeat x i.
Proof.
  induction i as [| i IH] in j, hIJ |- *; try easy.
  destruct j; simpl; rewrite ?IH; (lia || done).
Qed.

Lemma dropApp {A : Type} (l1 l2 : list A) (i : nat) (hI : i <= length l1) : drop i (l1 ++ l2) = drop i l1 ++ l2.
Proof.
  induction l1 as [| head tail IH] in i, hI, l2 |- *; simpl in *.
  - now rewrite (ltac:(lia) : i = 0), drop_0.
  - destruct i.
    + now rewrite drop_0.
    + simpl. rewrite IH; (done || lia).
Qed.

Lemma dropRepeat {A : Type} (x : A) (i j : nat) : drop i (repeat x j) = repeat x (j - i).
Proof.
  induction i as [| i IH] in j |- *.
  - now rewrite Nat.sub_0_r, drop_0.
  - destruct j; try easy. simpl. now rewrite IH.
Qed.
