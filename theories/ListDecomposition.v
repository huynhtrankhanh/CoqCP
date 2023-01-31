From stdpp Require Import numbers list.

Lemma listDecomposition {A : Type} (l : list A) (i j : nat) (hLt : i < j) (hUpperBound : j < length l) (default : A) : l = take i l ++ [nth i l default] ++ drop (S i) (take j l) ++ [nth j l default] ++ drop (j + 1) l.
Proof.
  assert (H1 : take i l ++ [nth i l default] = take (S i) l).
  { assert (H : i < length l). { lia. }
    clear hLt hUpperBound j. revert H. revert l. induction i; intros l H.
    - rewrite take_0. destruct l; simpl in *; try lia. rewrite take_0. reflexivity.
    - destruct l; simpl in H; try lia.
      simpl. rewrite IHi; try lia. reflexivity. }
  rewrite app_assoc, H1.
  assert (H2 : take (S i) l = take (S i) (take j l)).
  { rewrite take_take.
    assert (subtask : S i `min` j = S i). { lia. }
    rewrite subtask. reflexivity. }
  rewrite H2. clear H2.
  rewrite app_assoc, take_drop.
  assert (H2 : take j l ++ [nth j l default] = take (S j) l).
  { clear H1 hLt i. revert hUpperBound. revert l. induction j; intros l H.
    - rewrite take_0. destruct l; simpl in *; try lia. rewrite take_0. reflexivity.
    - destruct l; simpl in H; try lia.
      simpl. rewrite IHj; try lia. reflexivity. }
  rewrite app_assoc, H2, Nat.add_1_r, take_drop. reflexivity.
Qed.
