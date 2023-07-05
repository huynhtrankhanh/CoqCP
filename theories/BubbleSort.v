From CoqCP Require Import Options ListsEqual SwapUpdate ListRange.
From stdpp Require Import numbers list.

Section bubbleSort.
Context {A : Type} (default : A) (compare : A -> A -> bool).

Definition compareAndSwap (l : list A) i :=
  if compare (nth (i+1) l default) (nth i l default) then swap l i (i+1) default else l.

Definition bubbleSortPass (l : list A) := foldl compareAndSwap l (seq 0 (length l - 1)).

Definition bubbleSortPassPartial (l : list A) (n : nat) := foldl compareAndSwap l (seq 0 n).

Fixpoint bubbleSortAux (n : nat) (l : list A) :=
  match n with
  | 0 => l
  | S n' => bubbleSortAux n' (bubbleSortPass l)
  end.

Definition bubbleSort (l : list A) := bubbleSortAux (length l) l.

End bubbleSort.

Definition bubbleSortDemo (l : list nat) : list nat := bubbleSort (length l) Nat.ltb l.
