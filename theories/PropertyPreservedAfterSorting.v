From stdpp Require Import numbers list.
From CoqCP Require Import ListsEqual.

(* models the less than operator *)
Structure Comparator := {
  A : Type;
  compare : A -> A -> bool;
  transitive : forall a b c, compare a b -> compare b c -> compare a c;
  irreflexive : forall a, ~compare a a;
  equalityTransitive : forall a b c, let equal := fun a b => ~(compare a b || compare b a) in
  equal a b -> equal b c -> equal a c;
}.

Fixpoint update {A : Type} (l : list A) (i : nat) (value : A) :=
  match l, i with
  | [], _ => []
  | head :: tail, S i => head :: update tail i value
  | head :: tail, 0 => value :: tail
  end.

(* all indices 0 based *)
Definition swap {A : Type} (l : list A) (i j : nat) (default : A) :=
  let leftElement := nth i l default in
  let rightElement := nth j l default in
  let updated := update l i rightElement in
  update updated j leftElement.

Lemma updateAtIndexLength {A : Type} (l : list A) (value : A) : update l (length l) value = l.
Proof.
  induction l; unfold update; try easy; simpl; unfold update in IHl; rewrite IHl; easy.
Qed.

Lemma updateAtIndexLengthPlusSomething {A : Type} (l : list A) (value : A) (something : nat) : update l (length l + something) value = l.
Proof.
  induction l; unfold update; try easy; simpl; unfold update in IHl; rewrite IHl; easy.
Qed.

Lemma updateApp {A : Type} (l1 l2 : list A) (value : A) (i : nat) : update (l1 ++ l2) (length l1 + i) value = l1 ++ update l2 i value.
Proof.
  induction l1; unfold update; try easy; simpl; unfold update in IHl1; rewrite IHl1; easy.
Qed.

Lemma updateAppZero {A : Type} (l1 l2 : list A) (value : A) : update (l1 ++ l2) (length l1) value = l1 ++ update l2 0 value.
Proof.
  induction l1; unfold update; try easy; simpl; unfold update in IHl1; rewrite IHl1; easy.
Qed.

Lemma nthApp {A : Type} (l1 l2 : list A) (i : nat) (default : A) : nth (length l1 + i) (l1 ++ l2) default = nth i l2 default.
Proof.
  induction l1; unfold nth; try easy; simpl; unfold nth in IHl1; rewrite IHl1; easy.
Qed.

Lemma nthAppZero {A : Type} (l1 l2 : list A) (default : A) : nth (length l1) (l1 ++ l2) default = nth 0 l2 default.
Proof.
  induction l1; unfold nth; try easy; simpl; unfold nth in IHl1; rewrite IHl1; easy.
Qed.

Lemma swapChopOff {A : Type} (l1 l2 : list A) (i j : nat) (default : A) : swap (l1 ++ l2) (length l1 + i) (length l1 + j) default = l1 ++ swap l2 i j default.
Proof.
  induction l1; simpl; try easy.
  unfold swap. destruct i; destruct j; destruct l1; simpl; try easy; simpl in IHl1; rewrite ?IHl1, ?app_nil_r, ?Nat.add_0_r; simpl; rewrite ?updateAtIndexLength, ?updateAtIndexLengthPlusSomething, ?updateApp, ?updateAppZero, ?nthApp, ?nthAppZero, ?updateApp; easy.
Qed.

Lemma swapChopOff' {A : Type} (l1 l2 : list A) (j : nat) (default : A) : swap (l1 ++ l2) (length l1) (length l1 + j) default = l1 ++ swap l2 0 j default.
Proof.
  induction l1; simpl; try easy.
  unfold swap. destruct j; destruct l1; simpl; try easy; simpl in IHl1; rewrite ?IHl1, ?app_nil_r, ?Nat.add_0_r; simpl; rewrite ?updateAtIndexLength, ?updateAtIndexLengthPlusSomething, ?updateApp, ?updateAppZero, ?nthApp, ?nthAppZero, ?updateApp; easy.
Qed.

Lemma swapApp {A : Type} (l1 l2 l3 : list A) (a b default : A) : swap (l1 ++ [a] ++ l2 ++ [b] ++ l3) (length l1) (length l1 + length l2 + 1) default = l1 ++ [b] ++ l2 ++ [a] ++ l3.
Proof.
  rewrite <- Nat.add_assoc, swapChopOff'.
  induction l2; simpl; unfold swap.
  - unfold update. simpl. easy.
  - simpl. rewrite Nat.add_1_r, nthAppZero, updateAppZero. simpl. easy.
Qed.

Create HintDb rewriteSwapUpdate.
#[global] Hint Rewrite @updateAtIndexLength : rewriteSwapUpdate.
#[global] Hint Rewrite @updateAtIndexLengthPlusSomething : rewriteSwapUpdate.
#[global] Hint Rewrite @updateApp : rewriteSwapUpdate.
#[global] Hint Rewrite @updateAppZero : rewriteSwapUpdate.
#[global] Hint Rewrite @nthApp : rewriteSwapUpdate.
#[global] Hint Rewrite @nthAppZero : rewriteSwapUpdate.
#[global] Hint Rewrite @swapChopOff : rewriteSwapUpdate.
#[global] Hint Rewrite @swapChopOff': rewriteSwapUpdate.
#[global] Hint Rewrite @swapApp : rewriteSwapUpdate.

(* based on https://github.com/stqam/dafny/blob/master/BubbleSort.dfy *)

Fixpoint performOneBubbleSortPass {A : Type} (j : nat) (l : list A) (compare : A -> A -> bool) (default : A) :=
  match j with
  | 0 => l
  | S j =>
    match compare (nth (S j) l default) (nth j l default) with
    | false => performOneBubbleSortPass j l compare default
    | true => let updated := swap l j (S j) default in
      performOneBubbleSortPass j updated compare default
    end
  end.

(* i from 1 to length - 1, so i' from length - 1 to 1 (0 ignored) => i = length - i' *)
Fixpoint bubbleSortAux {A : Type} (i' : nat) (l : list A) (compare : A -> A -> bool) (default : A) :=
  match i' with
  | 0 => l
  | S i' => let i := length l - S i' in bubbleSortAux i' (performOneBubbleSortPass i l compare default) compare default
  end.

Definition bubbleSortDemo (l : list nat) := bubbleSortAux (length l - 1) l Nat.ltb 0.

Compute bubbleSortDemo [1; 2; 1; 2; 1; 2].
