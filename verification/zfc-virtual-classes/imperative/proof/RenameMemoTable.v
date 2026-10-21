From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
From stdpp Require Import numbers.
Open Scope Z_scope.

Module RenameMemoTable.
Definition entry := (Z * Z * Z * Z)%type.
Definition key := (Z * Z)%type.
Definition node (e : entry) := fst (fst (fst e)).
Definition depth (e : entry) := snd (fst (fst e)).
Definition value (e : entry) := snd (fst e).
Definition occupied (e : entry) := snd e.
Definition matches (e : entry) (k : key) := node e = fst k /\ depth e = snd k.
Definition next (size slot : nat) := (S slot mod size)%nat.
Fixpoint scan (table : nat -> entry) (size : nat) (k : key) (slot fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S rest => let e := table slot in
      if bool_decide (occupied e = 0) then None
      else if bool_decide (matches e k) then Some (value e)
      else scan table size k (next size slot) rest
  end.
Lemma next_bound size slot : (0 < size)%nat -> (next size slot < size)%nat.
Proof. intro Hsize. unfold next. apply Nat.mod_upper_bound. lia. Qed.
Theorem scan_sound table size k slot fuel result :
  (0 < size)%nat -> (slot < size)%nat -> scan table size k slot fuel = Some result ->
  exists index, (index < size)%nat /\ occupied (table index) <> 0 /\
    matches (table index) k /\ value (table index) = result.
Proof.
  induction fuel as [|fuel IH] in slot |- *; [discriminate|].
  intros Hsize Hslot. cbn [scan].
  destruct (bool_decide (occupied (table slot) = 0)) eqn:Hempty; [discriminate|].
  destruct (bool_decide (matches (table slot) k)) eqn:Hmatch.
  - intro Hvalue. injection Hvalue as <-. exists slot. split; [exact Hslot|].
    split; [now apply bool_decide_eq_false in Hempty|]. split; [now apply bool_decide_eq_true in Hmatch|reflexivity].
  - intro Hrun. exact (IH (next size slot) Hsize (next_bound size slot Hsize) Hrun).
Qed.
(* No deletion occurs within a substitution. An entry is accessible when no
   earlier slot on its insertion probe path is empty. Collisions are arbitrary. *)
Inductive accessible (table : nat -> entry) (size : nat) : nat -> nat -> nat -> Prop :=
| accessible_here slot : accessible table size slot slot 0
| accessible_next slot target distance : occupied (table slot) <> 0 ->
    accessible table size (next size slot) target distance ->
    accessible table size slot target (S distance).
Theorem scan_complete table size k start target distance fuel :
  accessible table size start target distance -> (distance < fuel)%nat ->
  occupied (table target) <> 0 -> matches (table target) k ->
  exists result, scan table size k start fuel = Some result.
Proof.
  intros Hpath. induction Hpath as [slot |slot target distance Hnonempty Hpath IH] in fuel |- *.
  - intros Hfuel Hoccupied Hmatches. destruct fuel; [lia|]. cbn [scan].
    rewrite bool_decide_false by exact Hoccupied. rewrite bool_decide_true by exact Hmatches. eauto.
  - intros Hfuel Hoccupied Hmatches. destruct fuel; [lia|]. cbn [scan].
    rewrite bool_decide_false by assumption.
    destruct (bool_decide (matches (table slot) k)); [eauto|]. apply IH; try assumption; lia.
Qed.
Definition represents (table : nat -> entry) (size : nat) (meaning : key -> Z -> Prop) :=
  forall index, (index < size)%nat -> occupied (table index) <> 0 ->
    meaning (node (table index),depth (table index)) (value (table index)).
Theorem scan_meaning table size meaning k start fuel result :
  (0 < size)%nat -> (start < size)%nat -> represents table size meaning ->
  scan table size k start fuel = Some result -> meaning k result.
Proof.
  intros Hsize Hstart Hrep Hrun.
  destruct (scan_sound table size k start fuel result Hsize Hstart Hrun)
    as [index [Hindex [Hoccupied [[Hnode Hdepth] Hvalue]]]].
  specialize (Hrep index Hindex Hoccupied). destruct k as [kn kd]. cbn in Hnode,Hdepth.
  now rewrite Hnode,Hdepth,Hvalue in Hrep.
Qed.
(* Updating a correct entry preserves semantic correctness independently of
   table placement. Placement and reachability are separate obligations. *)
Definition put (table : nat -> entry) (slot : nat) (e : entry) :=
  fun i => if Nat.eq_dec i slot then e else table i.
Theorem put_represents table size meaning slot k result :
  represents table size meaning -> meaning k result ->
  represents (put table slot (fst k,snd k,result,1)) size meaning.
Proof.
  intros Hrep Hmeaning index Hindex Hoccupied. unfold put in *.
  destruct (Nat.eq_dec index slot); [destruct k; exact Hmeaning|]. now apply Hrep.
Qed.
Theorem empty_represents size meaning : represents (fun _=>(0,0,0,0)) size meaning.
Proof. intros index Hindex Hoccupied. contradiction. Qed.
End RenameMemoTable.
