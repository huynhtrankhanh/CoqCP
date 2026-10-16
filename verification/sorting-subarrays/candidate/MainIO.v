From CoqCP Require Import Options Imperative.
From Stdlib Require Import Lists.List Bool.Bool Lia ZArith.ZArith Arith.PeanoNat.
From stdpp Require Import numbers list.
From Submission Require Import ByteIO.
Require Trusted.Spec.
Import ListNotations.
Local Open Scope Z_scope.

Definition dimensionsb (n k q : Z) :=
  (1 <=? n) && (n <=? 200000) && (1 <=? k) && (k <=? n) &&
  (1 <=? q) && (q <=? 200000).
Definition valueb (x : Z) := negb (x =? 0).
Definition queryb (n : nat) (q : Trusted.Spec.query) :=
  (1 <=? fst q)%nat && (fst q <=? snd q)%nat && (snd q <=? n)%nat.
Definition payloadb n a qs := forallb valueb a && forallb (queryb n) qs.

Fixpoint read_values (count : nat) (acc : list Z) : IO (list Z) :=
  match count with
  | O => ret (List.rev_append acc [])
  | S count => read_integer >>= fun x => read_values count (x :: acc)
  end.
Fixpoint read_queries (count : nat) (acc : list Trusted.Spec.query) : IO (list Trusted.Spec.query) :=
  match count with
  | O => ret (List.rev_append acc [])
  | S count => read_integer >>= fun l => read_integer >>= fun r =>
      read_queries count ((Z.to_nat l, Z.to_nat r) :: acc)
  end.

Fixpoint finish (fuel : nat) : IO unit :=
  match fuel with
  | O => trap
  | S fuel => get >>= fun ch =>
      if ch =? eof then ret tt else if spaceb ch then finish fuel else trap
  end.
Definition flush : IO unit := Dispatch _ _ _ Flush (fun _ => ret tt).

(* This is the actual entry point extracted for the executable. Decimal
   parsing and printing are part of this Action, not native wrapper code. *)
Definition main (solve : list Z -> nat -> list Trusted.Spec.query -> Z) : IO unit :=
  read_integer >>= fun n => read_integer >>= fun k => read_integer >>= fun q =>
  if dimensionsb n k q then
    read_values (Z.to_nat n) [] >>= fun a =>
    read_queries (Z.to_nat q) [] >>= fun qs =>
    if payloadb (Z.to_nat n) a qs then
      finish 16 >>= fun _ =>
      write_bytes (Trusted.Spec.signed_bytes (solve a (Z.to_nat k) qs) ++ [10]) >>=
      fun _ => flush
    else trap
  else trap.

Lemma limit_nat : Z.of_nat 200000%nat = 200000.
Proof. vm_compute. reflexivity. Qed.

Lemma dimensions_correct n k q :
  (1 <= n <= 200000)%nat -> (1 <= k <= n)%nat -> (1 <= q <= 200000)%nat ->
  dimensionsb (Z.of_nat n) (Z.of_nat k) (Z.of_nat q) = true.
Proof.
  intros Hn Hk Hq.
  pose proof limit_nat as LimitNat.
  unfold dimensionsb. repeat rewrite andb_true_iff.
  repeat split; apply Z.leb_le; lia.
Qed.

Lemma payload_correct a k qs : Trusted.Spec.valid_input a k qs -> payloadb (length a) a qs = true.
Proof.
  intros [Hn [Hk [Hq [Ha Hqs]]]]. unfold payloadb. apply andb_true_iff. split.
  - apply List.forallb_forall. intros x Hx. rewrite List.Forall_forall in Ha.
    unfold valueb. apply negb_true_iff, Z.eqb_neq. exact (proj2 (Ha x Hx)).
  - apply List.forallb_forall. intros q Hq'. rewrite List.Forall_forall in Hqs.
    specialize (Hqs q Hq'). destruct Hqs as [Hl [Hlr Hr]]. unfold queryb.
    repeat rewrite andb_true_iff. repeat split; apply Nat.leb_le; assumption.
Qed.

Lemma read_values_correct xs acc rest out :
  Forall (fun x => -1000000000 <= x <= 1000000000) xs ->
  runIO (read_values (length xs) acc) (Trusted.Spec.array_input xs ++ rest) out =
    Some (List.rev acc ++ xs, rest, out).
Proof.
  intro H. induction H as [|x xs Hx Hxs IH] in acc |- *.
  - cbn [read_values length ret runIO Trusted.Spec.array_input List.app]. now rewrite List.rev_append_rev.
  - cbn [read_values length Trusted.Spec.array_input]. rewrite run_bind.
    rewrite <- app_assoc, read_integer_correct by (try exact Hx; destruct xs; reflexivity).
    cbn [fst snd]. rewrite IH. cbn [List.rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma read_queries_correct n qs acc rest out :
  (n <= 200000)%nat -> Forall (Trusted.Spec.valid_query n) qs ->
  runIO (read_queries (length qs) acc) (concat (map Trusted.Spec.query_input qs) ++ rest) out =
    Some (List.rev acc ++ qs, rest, out).
Proof.
  intros Hn H. pose proof limit_nat as LimitNat. induction H as [|[l r] qs Hqr Hqs IH] in acc |- *.
  - cbn [read_queries length ret runIO map concat List.app]. now rewrite List.rev_append_rev.
  - destruct Hqr as [Hl [Hlr Hr]]. cbn [fst snd] in Hl, Hlr, Hr.
    cbn [read_queries length map concat]. unfold Trusted.Spec.query_input at 1. cbn [fst snd].
    rewrite run_bind, <- !app_assoc, read_integer_correct by (try reflexivity; lia).
    cbn [fst snd]. rewrite run_bind, read_integer_correct by (try reflexivity; lia).
    cbn [fst snd]. rewrite !Nat2Z.id, IH. cbn [List.rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma finish_correct fuel out : (0 < fuel)%nat -> runIO (finish fuel) [] out = Some (tt, [], out).
Proof.
  intro H. destruct fuel as [|fuel]; [lia|]. cbn [finish get ret bind runIO].
  change (runIO (if eof =? eof then ret tt else if spaceb eof then finish fuel else trap) [] out = Some (tt, [], out)).
  rewrite Z.eqb_refl. reflexivity.
Qed.

Theorem main_correct solve : Trusted.Spec.required_solver solve -> Trusted.Spec.required (main solve).
Proof.
  intros Hsolve a k qs Hvalid. pose proof limit_nat as LimitNat.
  destruct Hvalid as [Hn [Hk [Hq [Ha Hqs]]]].
  assert (Valid : Trusted.Spec.valid_input a k qs) by (unfold Trusted.Spec.valid_input; tauto).
  assert (Hab : Forall (fun x => -1000000000 <= x <= 1000000000) a).
  { rewrite List.Forall_forall in Ha |- *. intros x Hx. exact (proj1 (Ha x Hx)). }
  unfold main, Trusted.Spec.input_bytes.
  rewrite run_bind, read_integer_correct by (try reflexivity; lia).
  cbn [fst snd]. rewrite run_bind, read_integer_correct by (try reflexivity; lia).
  cbn [fst snd]. rewrite run_bind, read_integer_correct by (try reflexivity; lia).
  cbn [fst snd]. rewrite dimensions_correct by assumption.
  rewrite !Nat2Z.id, run_bind, read_values_correct by exact Hab.
  cbn [fst snd List.rev List.app]. rewrite run_bind.
  pose proof (read_queries_correct (length a) qs [] [] [] (proj2 Hn) Hqs) as Rq.
  rewrite app_nil_r in Rq. rewrite Rq.
  cbn [fst snd List.rev List.app]. rewrite payload_correct with (k:=k) by exact Valid.
  rewrite run_bind, finish_correct by lia. cbn [fst snd].
  rewrite run_bind, run_write. cbn [fst snd List.app flush runIO ret].
  unfold Trusted.Spec.output_bytes. rewrite (Hsolve a k qs Valid). reflexivity.
Qed.
