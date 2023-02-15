From stdpp Require Import numbers list.

Fixpoint rangeReversed (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n => n :: rangeReversed n
  end.

(* generates [0, 1, 2, ..., n - 1] *)
Definition range (n : nat) := reverse (rangeReversed n).

(* generates [left, left + 1, left + 2, ... right - 1, right] *)
Definition range2 (left right : nat) := map (fun x => x + left) (range (right - left + 1)).

Lemma rangeZero : range 0 = [].
Proof. easy. Qed.

Lemma rangeOne : range 1 = [0].
Proof. easy. Qed.

Lemma rangeSucc (n : nat) : range (S n) = range n ++ [n].
Proof.
  induction n; try easy; unfold range; simpl; rewrite reverse_cons; reflexivity.
Qed.

Lemma range2LeftLeft (left : nat) : range2 left left = [left].
Proof.
  unfold range2.
  assert (H : left - left + 1 = 1). { lia. }
  rewrite H, rangeOne, map_cons. easy.
Qed.

Lemma range2LeftSucc (left : nat) : range2 left (S left) = [left; S left].
Proof.
  unfold range2.
  assert (H : S left - left + 1 = 2). { lia. }
  rewrite H, rangeSucc, map_app, rangeOne. easy.
Qed.

Lemma range2LeftAdd (left delta : nat) : range2 left (S (left + delta)) = range2 left (left + delta) ++ [S (left + delta)].
Proof.
  unfold range2.
  assert (H : S (left + delta) - left + 1 = S (S delta)). { lia. }
  assert (H' : left + delta - left + 1 = S delta). { lia. }
  rewrite H, H', ?rangeSucc, ?map_app. simpl. rewrite Nat.add_comm. reflexivity.
Qed.
