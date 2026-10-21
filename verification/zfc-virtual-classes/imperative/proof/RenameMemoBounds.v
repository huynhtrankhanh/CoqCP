From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Lia.
Import ListNotations.
Open Scope Z_scope.
Module RenameMemoBounds.
Definition maximum : Z := 18446744073709551615.
Definition fuel root := (5 * (S root * S root) + 1)%nat.
Definition keys width := flat_map (fun node=>map (fun depth=>(node,depth)) (seq 0 width)) (seq 0 width).
Lemma grid_length_aux (nodes : list nat) width : length (flat_map (fun node=>map (fun depth=>(node,depth)) (seq 0 width)) nodes) = (length nodes * width)%nat.
Proof. induction nodes as [|node nodes IH]; [reflexivity|]. cbn [flat_map length]. rewrite length_app,length_map,length_seq,IH. lia. Qed.
Lemma grid_length width : length (keys width) = (width * width)%nat.
Proof. unfold keys. rewrite grid_length_aux,length_seq. reflexivity. Qed.
Lemma grid_contains width node depth : (node < width)%nat -> (depth < width)%nat -> In (node,depth) (keys width).
Proof.
  intros Hnode Hdepth. unfold keys. apply in_flat_map. exists node. split; [apply in_seq; lia|]. apply in_map. apply in_seq. lia.
Qed.
Theorem distinct_pairs width visited : NoDup visited ->
  Forall (fun key=> (fst key < width /\ snd key < width)%nat) visited -> (length visited <= width * width)%nat.
Proof.
  intros Hdistinct Hbound. rewrite <-grid_length. apply NoDup_incl_length; [exact Hdistinct|].
  intros [node depth] Hin. apply Forall_forall with (x:=(node,depth)) in Hbound; [|exact Hin].
  destruct Hbound as [Hnode Hdepth]. now apply grid_contains.
Qed.
(* A fresh node/depth pair accounts for its visit and at most two return
   phases. At most two child visits are scheduled by each fresh pair. The
   actual cached traversal must establish these counting invariants. *)
Theorem counted_work width visited hits returns : NoDup visited ->
  Forall (fun key=> (fst key < width /\ snd key < width)%nat) visited ->
  (hits <= 2 * length visited + 1)%nat -> (returns <= 2 * length visited)%nat ->
  (length visited + hits + returns <= 5 * (width * width) + 1)%nat.
Proof. intros Hdistinct Hbounds Hhits Hreturns. pose proof (distinct_pairs width visited Hdistinct Hbounds). nia. Qed.
Theorem root_fuel root visited hits returns : NoDup visited ->
  Forall (fun key=> (fst key <= root /\ snd key <= root)%nat) visited ->
  (hits <= 2 * length visited + 1)%nat -> (returns <= 2 * length visited)%nat ->
  (length visited + hits + returns <= fuel root)%nat.
Proof.
  intros Hdistinct Hbounds Hhits Hreturns. apply (counted_work (S root)); try assumption.
  eapply Forall_impl; [|exact Hbounds]. intros [node depth] [Hnode Hdepth]. cbn in *. lia.
Qed.
(* Absolute binder depths need not start at zero. The runtime cache stores
   absolute depths; translating the finite grid does not change its size. *)
Definition keys_from base width := flat_map
  (fun node=>map (fun depth=>(node,base+depth)%nat) (seq 0 width)) (seq 0 width).
Lemma grid_from_length_aux (nodes : list nat) base width :
  length (flat_map (fun node=>map (fun depth=>(node,base+depth)%nat)
    (seq 0 width)) nodes) = (length nodes * width)%nat.
Proof. induction nodes as [|node nodes IH]; [reflexivity|]. cbn [flat_map length]. rewrite length_app,length_map,length_seq,IH. lia. Qed.
Lemma grid_from_length base width : length (keys_from base width) = (width * width)%nat.
Proof. unfold keys_from. rewrite grid_from_length_aux,length_seq. reflexivity. Qed.
Lemma grid_from_contains base width node depth : (node < width)%nat ->
  (base <= depth < base + width)%nat -> In (node,depth) (keys_from base width).
Proof.
  intros Hnode Hdepth. unfold keys_from. apply in_flat_map. exists node. split; [apply in_seq; lia|].
  apply in_map_iff. exists (depth-base)%nat. split; [f_equal; lia|]. apply in_seq. lia.
Qed.
Theorem distinct_pairs_from base width visited : NoDup visited ->
  Forall (fun key=> (fst key < width /\ base <= snd key < base + width)%nat) visited ->
  (length visited <= width * width)%nat.
Proof.
  intros Hdistinct Hbound. rewrite <-(grid_from_length base). apply NoDup_incl_length; [exact Hdistinct|].
  intros [node depth] Hin. apply Forall_forall with (x:=(node,depth)) in Hbound; [|exact Hin].
  destruct Hbound as [Hnode Hdepth]. now apply grid_from_contains.
Qed.
Theorem root_fuel_from base root visited hits returns : NoDup visited ->
  Forall (fun key=> (fst key <= root /\ base <= snd key <= base + root)%nat) visited ->
  (hits <= 2 * length visited + 1)%nat -> (returns <= 2 * length visited)%nat ->
  (length visited + hits + returns <= fuel root)%nat.
Proof.
  intros Hdistinct Hbounds Hhits Hreturns.
  assert (Hgrid : Forall (fun key=> (fst key < S root /\ base <= snd key < base + S root)%nat) visited).
  { eapply Forall_impl; [|exact Hbounds]. intros [node depth] [Hnode Hdepth]. cbn in *. lia. }
  pose proof (distinct_pairs_from base (S root) visited Hdistinct Hgrid). unfold fuel. nia.
Qed.
(* A child edge decreases the source ID and introduces at most one binder.
   This is a path model, not yet the native arena invariant. *)
Inductive reachable (root base : nat) : nat -> nat -> Prop :=
| reachable_root : reachable root base root base
| reachable_child parent depth child binders : reachable root base parent depth ->
    (child < parent)%nat -> (binders <= 1)%nat ->
    reachable root base child (depth + binders).
Theorem reachable_rank root base node depth : reachable root base node depth ->
  (base <= depth /\ node + (depth-base) <= root)%nat.
Proof. intros Hpath. induction Hpath; cbn in *; lia. Qed.
Theorem reachable_bounds root base node depth : reachable root base node depth ->
  (node <= root /\ base <= depth <= base + root)%nat.
Proof. intros Hpath. pose proof (reachable_rank root base node depth Hpath). lia. Qed.
(* These are the exact arithmetic inequalities tested before the native loop.
   They concern natural-number resource bounds, not successful execution. *)
Theorem checked_arithmetic root : Z.of_nat (fuel root) <= maximum ->
  Z.of_nat root <> maximum /\
  0 < Z.of_nat (S root) /\
  Z.of_nat (S root) <= maximum / Z.of_nat (S root) /\
  Z.of_nat (S root * S root) <= (maximum - 1) / 5 /\
  0 <= Z.of_nat (S root * S root) <= maximum /\
  0 <= Z.of_nat (fuel root) <= maximum.
Proof.
  intros Hfuel. unfold fuel in Hfuel. rewrite Nat2Z.inj_add,Nat2Z.inj_mul,Nat2Z.inj_mul in Hfuel.
  assert (Hwidth : 0 < Z.of_nat (S root)) by lia.
  assert (Hproduct : Z.of_nat (S root) * Z.of_nat (S root) <= maximum) by nia.
  split; [unfold maximum in *; nia|]. split; [exact Hwidth|]. split.
  - apply Z.div_le_lower_bound; nia.
  - split.
    + rewrite Nat2Z.inj_mul. apply Z.div_le_lower_bound; nia.
    + split; [rewrite Nat2Z.inj_mul; nia|]. split; [lia|]. unfold fuel. rewrite Nat2Z.inj_add,Nat2Z.inj_mul,Nat2Z.inj_mul. exact Hfuel.
Qed.
End RenameMemoBounds.
