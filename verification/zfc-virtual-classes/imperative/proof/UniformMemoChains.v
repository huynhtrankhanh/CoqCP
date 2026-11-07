From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
Import ListNotations.

(* Mathematical model of the collision-chain scan in uniformMemoGet. This is
   not yet a refinement of the generated imperative code: in particular, it
   does not model arrays, 64-bit arithmetic, formulaHash, or growth. *)
Module UniformMemoChains.
Record entry := Entry { node : nat; depth : nat; value : nat; next : nat }.
Definition matches (e : entry) (n d : nat) := Nat.eqb (node e) n && Nat.eqb (depth e) d.
Fixpoint scan (table : nat -> entry) (fuel link n d : nat) : option nat :=
  match fuel, link with
  | O, _ | _, O => None
  | S rest, S index => let e := table index in
      if matches e n d then Some (value e) else scan table rest (next e) n d
  end.

Theorem scan_sound table fuel link n d v : scan table fuel link n d = Some v ->
  exists index, node (table index) = n /\ depth (table index) = d /\ value (table index) = v.
Proof.
 induction fuel as [|fuel IH] in link |- *; [discriminate|]. destruct link as [|index]; [discriminate|].
 cbn [scan]. destruct (matches (table index) n d) eqn:Hmatch.
 - intro H. inversion H; subst. unfold matches in Hmatch.
   apply andb_true_iff in Hmatch as [Hn Hd]. apply Nat.eqb_eq in Hn. apply Nat.eqb_eq in Hd.
   exists index. auto.
 - apply IH.
Qed.

(* Index zero is the empty link and S i names entry i. A well-formed chain
   therefore never dereferences beyond the count supplied as scan fuel. *)
Definition links_bounded table count :=
  forall i, (i < count)%nat -> (next (table i) <= count)%nat.
Theorem scan_sound_bounded table count fuel link n d v :
  links_bounded table count -> (link <= count)%nat ->
  scan table fuel link n d = Some v ->
  exists index, (index < count)%nat /\
    node (table index) = n /\ depth (table index) = d /\ value (table index) = v.
Proof.
 intros Hbound. induction fuel as [|fuel IH] in link |- *; [discriminate|].
 destruct link as [|index]; [discriminate|]. intros Hlink. cbn [scan].
 destruct (matches (table index) n d) eqn:Hmatch.
 - intro H. inversion H; subst. unfold matches in Hmatch.
   apply andb_true_iff in Hmatch as [Hn Hd]. apply Nat.eqb_eq in Hn. apply Nat.eqb_eq in Hd.
   exists index. repeat split; auto; lia.
 - apply IH. apply Hbound. lia.
Qed.

(* A path follows exactly the one-based links used in the program. *)
Inductive path (table : nat -> entry) : nat -> nat -> nat -> Prop :=
| path_here index : path table (S index) index 0
| path_next index target steps : path table (next (table index)) target steps ->
    path table (S index) target (S steps).

Theorem scan_complete table start target steps fuel n d :
  path table start target steps -> (steps < fuel)%nat ->
  node (table target) = n -> depth (table target) = d ->
  exists v, scan table fuel start n d = Some v.
Proof.
 intro Hpath. induction Hpath as [index|index target steps Hpath IH] in fuel |- *.
 - intros Hfuel Hnode Hdepth. destruct fuel; [lia|]. cbn [scan]. unfold matches.
   rewrite Hnode,Hdepth, !Nat.eqb_refl. exists (value (table index)). reflexivity.
 - intros Hfuel Hnode Hdepth. destruct fuel; [lia|]. cbn [scan].
   destruct (matches (table index) n d); [eauto|]. eapply IH; eauto; lia.
Qed.

Definition represents (table : nat -> entry) (meaning : nat -> nat -> nat -> Prop) :=
  forall index, meaning (node (table index)) (depth (table index)) (value (table index)).
Theorem scan_meaning table fuel link n d v meaning :
  represents table meaning -> scan table fuel link n d = Some v -> meaning n d v.
Proof.
 intros Hrep Hscan. destruct (scan_sound _ _ _ _ _ _ Hscan) as [i [Hn [Hd Hv]]].
 specialize (Hrep i). now rewrite Hn,Hd,Hv in Hrep.
Qed.

Definition put (table : nat -> entry) index e := fun i => if Nat.eq_dec i index then e else table i.

(* The loop control of uniformMemoGet, starting with found=false, factored
   into an explicit mutable-state machine. Once break is taken, subsequent
   abstract iterations are no-ops. The connection from this model to the
   generated Action is still separate. *)
Record loop_state := LoopState {
  current : nat;
  found : bool;
  result : nat;
  stopped : bool
}.
Definition loop_step table n d s :=
  if stopped s then s else
  match current s with
  | O => LoopState 0 false (result s) true
  | S index =>
      if matches (table index) n d
      then LoopState (S index) true (value (table index)) true
      else LoopState (next (table index)) false (result s) false
  end.
Fixpoint loop_run table n d fuel s :=
  match fuel with
  | O => s
  | S rest => loop_run table n d rest (loop_step table n d s)
  end.
Lemma loop_run_stopped table n d fuel s :
  stopped s = true -> loop_run table n d fuel s = s.
Proof.
 intro H. induction fuel as [|fuel IH]; [reflexivity|]. cbn [loop_run].
 assert (Hstep : loop_step table n d s = s) by (unfold loop_step; now rewrite H).
 now rewrite Hstep.
Qed.
Lemma loop_step_link_bounded table n d s count :
  links_bounded table count -> (current s <= count)%nat ->
  (current (loop_step table n d s) <= count)%nat.
Proof.
 intros Hlinks Hcurrent. unfold loop_step.
 destruct (stopped s); [exact Hcurrent|].
 destruct (current s) as [|index] eqn:Hlink; [cbn; lia|].
 destruct (matches (table index) n d); cbn; [lia|].
 apply Hlinks. lia.
Qed.
Theorem loop_run_link_bounded table n d fuel s count :
  links_bounded table count -> (current s <= count)%nat ->
  (current (loop_run table n d fuel s) <= count)%nat.
Proof.
 intros Hlinks. induction fuel as [|fuel IH] in s |- *; [auto|].
 cbn [loop_run]. intro Hcurrent. apply IH. now apply loop_step_link_bounded.
Qed.
Theorem loop_run_refines_scan table n d fuel link previous_result :
  let final := loop_run table n d fuel (LoopState link false previous_result false) in
  (if found final then Some (result final) else None) = scan table fuel link n d.
Proof.
 induction fuel as [|fuel IH] in link |- *; [reflexivity|].
 cbn [loop_run loop_step scan]. destruct link as [|index].
 - cbn. rewrite loop_run_stopped by reflexivity. reflexivity.
 - destruct (matches (table index) n d) eqn:Hmatch.
   + cbn. rewrite Hmatch. cbn. rewrite loop_run_stopped by reflexivity. reflexivity.
   + cbn. rewrite Hmatch. cbn. apply IH.
Qed.
Theorem loop_run_result_bounded table count n d fuel link previous_result :
  links_bounded table count -> (link <= count)%nat ->
  let final := loop_run table n d fuel (LoopState link false previous_result false) in
  found final = true ->
  exists index, (index < count)%nat /\ node (table index) = n /\
    depth (table index) = d /\ value (table index) = result final.
Proof.
 intros Hlinks Hlink. cbn zeta. intro Hfound.
 pose proof (loop_run_refines_scan table n d fuel link previous_result) as Hscan.
 cbn zeta in Hscan. rewrite Hfound in Hscan.
 eapply scan_sound_bounded; [exact Hlinks|exact Hlink|symmetry; exact Hscan].
Qed.
Theorem inserted_head table index n d v previous fuel : (0 < fuel)%nat ->
 scan (put table index (Entry n d v previous)) fuel (S index) n d = Some v.
Proof.
 intros Hfuel. destruct fuel; [lia|]. cbn [scan]. unfold put.
 destruct (Nat.eq_dec index index); [|contradiction]. unfold matches. cbn [node depth].
 now rewrite !Nat.eqb_refl.
Qed.
Theorem inserted_collision table index n d v previous fuel qn qd :
  (qn <> n \/ qd <> d) -> (0 < fuel)%nat ->
  scan (put table index (Entry n d v previous)) fuel (S index) qn qd =
  scan (put table index (Entry n d v previous)) (pred fuel) previous qn qd.
Proof.
 intros Hneq Hfuel. destruct fuel; [lia|]. cbn [scan pred]. unfold put at 1.
 destruct (Nat.eq_dec index index); [|contradiction]. unfold matches. cbn [node depth next].
 assert (Hfalse : (n =? qn)%nat && (d =? qd)%nat = false).
 { destruct ((n =? qn)%nat && (d =? qd)%nat) eqn:Htest; [|reflexivity].
   apply andb_true_iff in Htest as [Hn Hd]. apply Nat.eqb_eq in Hn. apply Nat.eqb_eq in Hd. destruct Hneq; congruence. }
 rewrite Hfalse.
 replace (put table index (Entry n d v previous) index) with (Entry n d v previous)
   by (unfold put; destruct (Nat.eq_dec index index); congruence).
 reflexivity.
Qed.
End UniformMemoChains.
