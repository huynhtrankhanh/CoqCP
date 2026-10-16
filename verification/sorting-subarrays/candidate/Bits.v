From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia ZArith.ZArith Sorting.Permutation.
Import ListNotations.

Fixpoint ones (xs : list bool) : nat :=
  match xs with [] => 0 | b :: bs => (if b then 1 else 0) + ones bs end.

Fixpoint paint (l r : nat) (b : bool) (xs : list bool) {struct xs} : list bool :=
  match xs with
  | [] => []
  | x :: rest =>
      match r with
      | 0 => xs
      | S r' => match l with
        | 0 => b :: paint 0 r' b rest
        | S l' => x :: paint l' r' b rest
        end
      end
  end.

Lemma ones_app xs ys : ones (xs ++ ys) = ones xs + ones ys.
Proof. induction xs as [|[] xs IH]; simpl; lia. Qed.

Lemma ones_bound xs : ones xs <= length xs.
Proof. induction xs as [|[] xs IH]; simpl; lia. Qed.

Lemma ones_repeat b n : ones (repeat b n) = if b then n else 0.
Proof. destruct b; induction n; simpl; lia. Qed.

Lemma paint_length l r b xs : length (paint l r b xs) = length xs.
Proof.
  revert l r. induction xs as [|x xs IH]; intros l r.
  - reflexivity.
  - destruct r as [|r]; [reflexivity|].
    destruct l; simpl; now rewrite IH.
Qed.

Lemma paint_app l r b xs ys :
  paint l r b (xs ++ ys) =
  paint l r b xs ++ paint (l - length xs) (r - length xs) b ys.
Proof.
  revert l r. induction xs as [|x xs IH]; intros l r.
  - simpl. now rewrite !Nat.sub_0_r.
  - destruct r as [|r].
    + simpl. destruct ys; reflexivity.
    + destruct l as [|l]; simpl; rewrite IH; reflexivity.
Qed.

Lemma paint_after l r b xs : length xs <= l -> paint l r b xs = xs.
Proof.
  revert l r. induction xs as [|x xs IH]; intros l r H; [reflexivity|].
  destruct r; [reflexivity|]. destruct l; [simpl in H; lia|].
  simpl. rewrite IH by (simpl in H; lia). reflexivity.
Qed.

Lemma paint_full r b xs : length xs <= r -> paint 0 r b xs = repeat b (length xs).
Proof.
  revert r. induction xs as [|x xs IH]; intros r H; [reflexivity|].
  destruct r; [simpl in H; lia|]. simpl. rewrite IH by (simpl in H; lia). reflexivity.
Qed.

Lemma paint_zero l b xs : paint l 0 b xs = xs.
Proof. destruct xs; reflexivity. Qed.

Lemma paint_segment l r b xs : l <= r -> r <= length xs ->
  paint l r b xs = firstn l xs ++ repeat b (r-l) ++ skipn r xs.
Proof.
  revert l r. induction xs as [|x xs IH]; intros l r Hlr Hr.
  - assert (Hz : l=0 /\ r=0) by (simpl in Hr; lia). destruct Hz as [-> ->]. reflexivity.
  - destruct r as [|r].
    + assert (Hz : l=0) by lia. subst. reflexivity.
    + destruct l as [|l].
      * simpl. rewrite IH by (simpl in Hr; lia). simpl. now rewrite ?Nat.sub_0_r.
      * simpl. rewrite IH by (simpl in Hr; lia). reflexivity.
Qed.

Lemma firstn_app_count k xs ys :
  ones (firstn k (xs ++ ys)) =
  ones (firstn k xs) + ones (firstn (k-length xs) ys).
Proof.
  rewrite firstn_app, ones_app. reflexivity.
Qed.

Lemma ones_slice l r xs : l <= r -> r <= length xs ->
  ones (firstn r xs) - ones (firstn l xs) = ones (firstn (r-l) (skipn l xs)).
Proof.
  revert l r. induction xs as [|x xs IH]; intros l r Hlr Hr.
  - assert (Hz : l=0 /\ r=0) by (simpl in Hr; lia). destruct Hz as [-> ->]. reflexivity.
  - destruct l as [|l].
    + simpl. now rewrite !Nat.sub_0_r.
    + destruct r as [|r]; [lia|]. simpl.
      rewrite <- IH by (simpl in Hr; lia).
      destruct x; simpl; lia.
Qed.

Lemma firstn_repeat k n (b : bool) : firstn k (repeat b n) = repeat b (Nat.min k n).
Proof. revert n. induction k as [|k IH]; intros [|n]; simpl; auto. now rewrite IH. Qed.

Lemma nth_repeat_any n (b d : bool) k : k < n -> nth k (repeat b n) d = b.
Proof. revert k. induction n as [|n IH]; intros [|k] H; simpl; try reflexivity; try lia. apply IH. lia. Qed.
