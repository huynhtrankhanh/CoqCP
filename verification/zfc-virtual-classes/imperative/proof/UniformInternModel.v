From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat Lia.
Import ListNotations.

(* A mathematical hash-cons table for the experimental uniform interner.
   This is deliberately independent of its IIL arrays, hashing implementation,
   machine-word arithmetic and generated-code execution. *)
Module UniformInternModel.
Definition row := (nat * nat * nat)%type.
Definition row_eq_dec (x y : row) : {x = y} + {x <> y}.
Proof. decide equality; try apply Nat.eq_dec; decide equality; apply Nat.eq_dec. Defined.

Definition matches (rows : list row) (key : row) (i : nat) : bool :=
  match nth_error rows i with
  | Some entry => if row_eq_dec entry key then true else false
  | None => false
  end.

Definition lookup (rows : list row) (buckets : nat -> list nat)
    (hash : row -> nat) (key : row) : option nat :=
  find (matches rows key) (buckets (hash key)).

Definition indexed (rows : list row) (buckets : nat -> list nat)
    (hash : row -> nat) : Prop :=
  forall i key, nth_error rows i = Some key -> In i (buckets (hash key)).

Lemma matches_spec rows key i : matches rows key i = true <-> nth_error rows i = Some key.
Proof.
  unfold matches. destruct (nth_error rows i) as [entry|] eqn:Hentry; [|split; discriminate].
  destruct (row_eq_dec entry key) as [->|Hne]; split; intros H; try reflexivity;
    try discriminate; inversion H; contradiction.
Qed.

Theorem lookup_sound rows buckets hash key i :
  lookup rows buckets hash key = Some i -> nth_error rows i = Some key.
Proof.
  unfold lookup. intro H. apply find_some in H as [_ Hmatch].
  now apply matches_spec.
Qed.

Theorem lookup_complete rows buckets hash key i :
  indexed rows buckets hash -> nth_error rows i = Some key ->
  exists j, lookup rows buckets hash key = Some j.
Proof.
  intros Hindex Hkey. unfold lookup.
  destruct (find (matches rows key) (buckets (hash key))) as [j|] eqn:Hfind; [eauto|].
  pose proof (@find_none nat (matches rows key) (buckets (hash key)) Hfind i
    (Hindex i key Hkey)) as Hnone.
  apply matches_spec in Hkey. congruence.
Qed.

Theorem lookup_miss_absent rows buckets hash key :
  indexed rows buckets hash -> lookup rows buckets hash key = None ->
  forall i, nth_error rows i <> Some key.
Proof.
  intros Hindex Hmiss i Hkey. destruct (lookup_complete _ _ _ _ _ Hindex Hkey) as [j Hj].
  congruence.
Qed.

Theorem lookup_canonical rows buckets hash key i :
  NoDup rows -> indexed rows buckets hash -> nth_error rows i = Some key ->
  lookup rows buckets hash key = Some i.
Proof.
  intros Hunique Hindex Hkey.
  destruct (lookup_complete _ _ _ _ _ Hindex Hkey) as [j Hj].
  pose proof (lookup_sound _ _ _ _ _ Hj) as Hother.
  pose proof (proj1 (NoDup_nth_error rows) Hunique) as Hindices.
  assert (j = i) as ->.
  { apply Hindices; [apply nth_error_Some; congruence|congruence]. }
  exact Hj.
Qed.

(* A successful miss may append a new row and link it at the head of its
   bucket. Earlier row indices and all earlier bucket memberships persist. *)
Definition push (buckets : nat -> list nat) bucket index : nat -> list nat :=
  fun b => if Nat.eq_dec b bucket then index :: buckets b else buckets b.

Lemma push_preserves buckets bucket index b i :
  In i (buckets b) -> In i (push buckets bucket index b).
Proof. unfold push. destruct (Nat.eq_dec b bucket); simpl; auto. Qed.

Theorem push_indexed rows buckets hash key :
  indexed rows buckets hash -> indexed (rows ++ [key])
    (push buckets (hash key) (length rows)) hash.
Proof.
  intros Hindex i value Hentry. destruct (Nat.ltb_spec i (length rows)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hentry by exact Hlt. now apply push_preserves, Hindex.
  - rewrite nth_error_app2 in Hentry by lia.
    destruct (i - length rows) as [|n] eqn:Hd; [|destruct n; discriminate].
    cbn in Hentry. inversion Hentry; subst value.
    assert (i = length rows) by lia. subst i.
    unfold push. destruct (Nat.eq_dec (hash key) (hash key)); [now left|contradiction].
Qed.

Theorem append_fresh_unique rows buckets hash key :
  NoDup rows -> indexed rows buckets hash -> lookup rows buckets hash key = None ->
  NoDup (rows ++ [key]).
Proof.
  intros Hunique Hindex Hmiss. apply NoDup_app; [exact Hunique|constructor; [simpl; tauto|constructor]|].
  intros value Hin Hsingle. simpl in Hsingle. destruct Hsingle as [<-|[]].
  apply In_nth_error in Hin as [i Hi]. eapply lookup_miss_absent; eassumption.
Qed.

Theorem pushed_row_is_found rows buckets hash key :
  lookup (rows ++ [key]) (push buckets (hash key) (length rows)) hash key =
    Some (length rows).
Proof.
  unfold lookup, push. destruct (Nat.eq_dec (hash key) (hash key)); [|contradiction].
  cbn [find]. assert (matches (rows ++ [key]) key (length rows) = true) as Hmatch.
  { apply matches_spec. rewrite nth_error_app2 by lia.
    replace (length rows - length rows) with 0 by lia. reflexivity. }
  now rewrite Hmatch.
Qed.

(* Rebuilding all buckets may use any hash function, including one where all
   keys collide. Full tuple comparison is what protects the result. *)
Definition rehash (rows : list row) (hash : row -> nat) (bucket : nat) : list nat :=
  filter (fun i => Nat.eqb (hash (nth i rows (0, 0, 0))) bucket)
         (seq 0 (length rows)).

Theorem rehash_indexed rows hash : indexed rows (rehash rows hash) hash.
Proof.
  intros i key Hkey. unfold rehash. apply filter_In. split.
  - apply in_seq. assert (i < length rows) by (apply nth_error_Some; congruence). lia.
  - apply Nat.eqb_eq. rewrite (@nth_error_nth row rows i key (0, 0, 0) Hkey). reflexivity.
Qed.

Theorem rehash_preserves_lookup rows hash key i :
  NoDup rows -> nth_error rows i = Some key ->
  lookup rows (rehash rows hash) hash key = Some i.
Proof. intros Hunique Hkey. eapply lookup_canonical; eauto using rehash_indexed. Qed.

Example colliding_keys_still_compare_full_rows :
  lookup [(1, 2, 3); (1, 2, 4)] (rehash [(1, 2, 3); (1, 2, 4)] (fun _ => 0))
    (fun _ => 0) (1, 2, 4) = Some 1.
Proof. reflexivity. Qed.
End UniformInternModel.
