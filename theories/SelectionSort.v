From stdpp Require Import numbers list.
From CoqCP Require Import Options ListsEqual SwapUpdate ListRange.

Section selectionSort.
Context {A : Type} (default : A) (compare : A -> A -> bool) (l : list A).

Definition pickSmallestInRange (left right : nat) (l : list A) :=
  foldl (fun accumulated current => if compare (nth current l default) (nth accumulated l default) then current else accumulated) left (range2 left right).

Definition selectionSort :=
  foldl (fun accumulated i => swap accumulated i (pickSmallestInRange i (length l - 1) accumulated) default) l (range (length l)).

End selectionSort.

Definition selectionSortDemo (l : list nat) : list nat := selectionSort 0 Nat.ltb l.
