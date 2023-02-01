From stdpp Require Import numbers list.

Definition sorted {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) := forall i j, i < j -> j < length l -> ~compare (nth j l default) (nth i l default).

Definition prefixSorted {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (prefixLength : nat) := forall i j, i < j -> j < prefixLength -> ~compare (nth j l default) (nth i l default).

Definition partitioned {A : Type} (default : A) (compare : A -> A -> bool) (l : list A) (middle : nat) := forall toTheLeft toTheRight, toTheLeft <= middle -> toTheRight >= middle -> toTheRight < length l -> ~compare (nth toTheRight l default) (nth toTheLeft l default).
