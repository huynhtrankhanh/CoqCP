From stdpp Require Import numbers list.

(* all indices 0 based *)
Definition swap {A : Type} (l : list A) (i j : nat) (default : A) :=
  let leftElement := nth i l default in
  let rightElement := nth j l default in
  let updated := <[i := rightElement]> l in
  <[j := leftElement]> updated.

Lemma updateAtIndexLength {A : Type} (l : list A) (value : A) : <[length l := value]> l = l.
Proof.
  induction l; unfold alter; try easy; simpl; unfold alter in IHl; rewrite IHl; easy.
Qed.

Lemma updateAtIndexLengthPlusSomething {A : Type} (l : list A) (value : A) (something : nat) : <[length l + something := value]> l = l.
Proof.
  induction l; unfold alter; try easy; simpl; unfold alter in IHl; rewrite IHl; easy.
Qed.

Lemma updateApp {A : Type} (l1 l2 : list A) (value : A) (i : nat) : <[length l1 + i := value]> (l1 ++ l2) = l1 ++ <[i := value]> l2.
Proof.
  induction l1; unfold alter; try easy; simpl; unfold alter in IHl1; rewrite IHl1; easy.
Qed.

Lemma updateAppZero {A : Type} (l1 l2 : list A) (value : A) : <[length l1 := value]> (l1 ++ l2) = l1 ++ <[0 := value]> l2.
Proof.
  induction l1; unfold alter; try easy; simpl; unfold alter in IHl1; rewrite IHl1; easy.
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
  - unfold alter. simpl. easy.
  - rewrite Nat.add_1_r. simpl. rewrite nthAppZero. simpl. rewrite updateAppZero. simpl. easy.
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
