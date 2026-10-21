From CoqCP Require Import Options.
From NativeProof Require Import RenameMemoTable.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers.
Open Scope Z_scope.
Module RenameMemoPlacement.
Import RenameMemoTable.
Fixpoint place (table : nat -> entry) size k slot fuel : option nat :=
  match fuel with
  | O => None
  | S rest => if bool_decide (occupied (table slot) = 0) then Some slot
      else if bool_decide (matches (table slot) k) then Some slot
      else place table size k (next size slot) rest
  end.
Theorem place_sound table size k start fuel slot :
  (0 < size)%nat -> (start < size)%nat -> place table size k start fuel = Some slot ->
  (slot < size)%nat /\ (occupied (table slot) = 0 \/ matches (table slot) k) /\
  exists distance, (distance < fuel)%nat /\ accessible table size start slot distance.
Proof.
  induction fuel as [|fuel IH] in start |- *; [discriminate|].
  intros Hsize Hstart. cbn [place].
  destruct (bool_decide (occupied (table start) = 0)) eqn:Hempty.
  - intros Hslot. injection Hslot as <-. split; [exact Hstart|].
    split; [left; now apply bool_decide_eq_true in Hempty|]. exists 0%nat. split; [lia|constructor].
  - destruct (bool_decide (matches (table start) k)) eqn:Hmatch.
    + intros Hslot. injection Hslot as <-. split; [exact Hstart|].
      split; [right; now apply bool_decide_eq_true in Hmatch|]. exists 0%nat. split; [lia|constructor].
    + intros Hrun. destruct (IH (next size start) Hsize (next_bound size start Hsize) Hrun)
        as [Hslot [Hentry [distance [Hdistance Hpath]]]].
      split; [exact Hslot|]. split; [exact Hentry|]. exists (S distance). split; [lia|].
      constructor; [now apply bool_decide_eq_false in Hempty|exact Hpath].
Qed.
Theorem place_scan table size k start fuel :
  scan table size k start fuel = match place table size k start fuel with
    | Some slot => if bool_decide (occupied (table slot) = 0) then None else Some (value (table slot))
    | None => None end.
Proof.
  induction fuel as [|fuel IH] in start |- *; [reflexivity|]. cbn [scan place].
  destruct (bool_decide (occupied (table start) = 0)) eqn:Hempty; [now rewrite Hempty|].
  destruct (bool_decide (matches (table start) k)); [now rewrite Hempty|apply IH].
Qed.
Lemma accessible_preserved table other size start slot distance :
  (forall i, occupied (table i) <> 0 -> occupied (other i) <> 0) ->
  accessible table size start slot distance -> accessible other size start slot distance.
Proof. intros Hoccupied Hpath. induction Hpath as [slot |start slot distance Hnonempty Hpath IH]; [constructor|]. constructor; [now apply Hoccupied|exact IH]. Qed.
Lemma put_nonempty table slot e : occupied e <> 0 ->
  forall i, occupied (table i) <> 0 -> occupied (put table slot e i) <> 0.
Proof. intros He i Hi. unfold put. destruct (Nat.eq_dec i slot); assumption. Qed.
Definition indexed_by (table : nat -> entry) size (hash : key -> nat) :=
  forall index, (index < size)%nat -> occupied (table index) <> 0 ->
    exists distance, (distance < size)%nat /\
      accessible table size (hash (node (table index),depth (table index))) index distance.
Theorem put_indexed table size hash slot k result :
  indexed_by table size hash -> (slot < size)%nat ->
  (exists distance, (distance < size)%nat /\ accessible table size (hash k) slot distance) ->
  indexed_by (put table slot (fst k,snd k,result,1)) size hash.
Proof.
  intros Hindexed Hslot Hpath index Hindex Hoccupied.
  assert (Hmonotone : forall i, occupied (table i) <> 0 -> occupied (put table slot (fst k,snd k,result,1) i) <> 0).
  { exact (put_nonempty table slot (fst k,snd k,result,1) ltac:(discriminate)). }
  destruct (Nat.eq_dec index slot) as [->|Hother].
  - destruct Hpath as [distance [Hdistance Hpath]]. exists distance. split; [exact Hdistance|].
    assert (Hentry : put table slot (fst k,snd k,result,1) slot = (fst k,snd k,result,1)) by (unfold put; now destruct Nat.eq_dec).
    rewrite Hentry. cbn [node depth fst snd]. destruct k as [kn kd]. cbn in *.
    exact (accessible_preserved table _ size _ slot distance Hmonotone Hpath).
  - assert (Hentry : put table slot (fst k,snd k,result,1) index = table index) by (unfold put; destruct Nat.eq_dec; congruence).
    rewrite Hentry in Hoccupied |- *. destruct (Hindexed index Hindex Hoccupied) as [distance [Hdistance Hprevious]].
    exists distance. split; [exact Hdistance|]. now apply accessible_preserved with (table := table).
Qed.
Theorem placed_indexed table size hash k start slot result :
  (0 < size)%nat -> (start < size)%nat -> start = hash k ->
  indexed_by table size hash -> place table size k start size = Some slot ->
  indexed_by (put table slot (fst k,snd k,result,1)) size hash.
Proof.
  intros Hsize Hstart Hhash Hindexed Hplace.
  destruct (place_sound table size k start size slot Hsize Hstart Hplace) as [Hslot [_ Hpath]].
  apply put_indexed; try assumption. now rewrite <-Hhash.
Qed.
Theorem empty_indexed size hash : indexed_by (fun _=>(0,0,0,0)) size hash.
Proof. intros index Hindex Hoccupied. contradiction. Qed.
Lemma accessible_ext table other size start slot distance :
  (forall i, table i = other i) -> accessible table size start slot distance -> accessible other size start slot distance.
Proof.
  intros Htable Hpath. apply accessible_preserved with (table:=table); [intros i; now rewrite <-Htable|exact Hpath].
Qed.
Lemma indexed_ext table other size hash : (forall i, table i = other i) ->
  indexed_by table size hash -> indexed_by other size hash.
Proof.
  intros Htable Hindexed index Hindex Hoccupied. rewrite <-Htable in Hoccupied |- *.
  destruct (Hindexed index Hindex Hoccupied) as [distance [Hdistance Hpath]].
  exists distance. split; [exact Hdistance|]. now apply accessible_ext with (table:=table).
Qed.
Lemma represents_ext table other size meaning : (forall i, table i = other i) ->
  represents table size meaning -> represents other size meaning.
Proof. intros Htable Hrep index Hindex Hoccupied. rewrite <-Htable in Hoccupied |- *. now apply Hrep. Qed.
End RenameMemoPlacement.

