From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoTable RenameMemoPlacement.
From Stdlib Require Import Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers.
Module RenameMemoPrefix.
Import RenameMemoTable RenameMemoPlacement.
Theorem accessible_prefix table other size start target distance : (0<size)%nat ->
  (forall index, (index<size)%nat -> table index=other index) ->
  (start<size)%nat -> accessible table size start target distance -> accessible other size start target distance.
Proof.
  intros Hsize Htable Hstart Hpath. induction Hpath as [slot|slot target distance Hoccupied Hpath IH].
  - constructor.
  - constructor.
    + now rewrite <-Htable by exact Hstart.
    + apply IH. now apply next_bound.
Qed.
Theorem indexed_prefix table other size hash : (0<size)%nat ->
  (forall index, (index<size)%nat -> table index=other index) ->
  (forall k, (hash k<size)%nat) -> indexed_by table size hash -> indexed_by other size hash.
Proof.
  intros Hsize Htable Hhash Hindexed index Hindex Hoccupied.
  rewrite <-Htable in Hoccupied |- * by exact Hindex.
  destruct (Hindexed index Hindex Hoccupied) as [distance [Hdistance Hpath]].
  exists distance. split; [exact Hdistance|].
  exact (accessible_prefix table other size _ index distance Hsize Htable (Hhash _) Hpath).
Qed.
Theorem represents_prefix table other size meaning :
  (forall index, (index<size)%nat -> table index=other index) -> represents table size meaning -> represents other size meaning.
Proof. intros Htable Hrep index Hindex Hoccupied. rewrite <-Htable in Hoccupied |- * by exact Hindex. now apply Hrep. Qed.
Theorem scan_prefix table other size key start fuel : (0<size)%nat ->
  (forall index, (index<size)%nat -> table index=other index) -> (start<size)%nat ->
  scan table size key start fuel=scan other size key start fuel.
Proof.
  induction fuel as [|fuel IH] in start|-*; [reflexivity|]. intros Hsize Htable Hstart. cbn [scan].
  rewrite Htable by exact Hstart. destruct bool_decide; [reflexivity|]. destruct bool_decide; [reflexivity|].
  apply IH; try assumption. now apply next_bound.
Qed.
End RenameMemoPrefix.
