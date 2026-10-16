From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Arith.PeanoNat Bool.Bool Lia.
From Submission Require Import Bits.
Import ListNotations.

(* A complete binary tree. Uniform nodes are lazy range assignments. The
   height is passed separately, so every operation descends at most h levels. *)
Inductive tree :=
| Uniform (bit : bool)
| Branch (count : nat) (left right : tree).

Definition capacity (h : nat) := 2 ^ h.
Definition total (h : nat) (t : tree) : nat :=
  match t with Uniform b => if b then capacity h else 0 | Branch c _ _ => c end.
Definition join (h : nat) (a b : tree) : tree :=
  Branch (total h a + total h b) a b.
Definition children (t : tree) : tree * tree :=
  match t with Uniform b => (Uniform b, Uniform b) | Branch _ a b => (a,b) end.

Fixpoint contents (h : nat) (t : tree) {struct t} : list bool :=
  match t with
  | Uniform b => repeat b (capacity h)
  | Branch _ a b => match h with
    | 0 => []
    | S h' => contents h' a ++ contents h' b
    end
  end.

Fixpoint sound (h : nat) (t : tree) {struct t} : Prop :=
  match t with
  | Uniform _ => True
  | Branch c a b => match h with
    | 0 => False
    | S h' => sound h' a /\ sound h' b /\ c = total h' a + total h' b
    end
  end.

Fixpoint prefix (h k : nat) (t : tree) : nat :=
  if capacity h <=? k then total h t else
  match t with
  | Uniform b => if b then k else 0
  | Branch _ a b => match h with
    | 0 => 0
    | S h' => if k <=? capacity h' then prefix h' k a
      else total h' a + prefix h' (k-capacity h') b
    end
  end.

Fixpoint assign (h l r : nat) (b : bool) (t : tree) : tree :=
  if (r =? 0) || (capacity h <=? l) then t else
  if (l =? 0) && (capacity h <=? r) then Uniform b else
  match h with
  | 0 => t
  | S h' => let '(a,c) := children t in
      join h' (assign h' l r b a)
        (assign h' (l-capacity h') (r-capacity h') b c)
  end.

Fixpoint build (h : nat) (xs : list bool) : tree :=
  match h with
  | 0 => Uniform (hd false xs)
  | S h' => join h' (build h' (firstn (capacity h') xs))
                    (build h' (skipn (capacity h') xs))
  end.

Lemma capacity_succ h : capacity (S h) = capacity h + capacity h.
Proof. unfold capacity. simpl. lia. Qed.

Lemma sound_contents h t : sound h t ->
  length (contents h t) = capacity h /\ total h t = ones (contents h t).
Proof.
  revert t. induction h as [|h IH]; intros [b|c a b] H; simpl in *.
  - simpl capacity. destruct b; simpl; auto.
  - contradiction.
  - rewrite repeat_length, ones_repeat. auto.
  - destruct H as [Ha [Hb Hc]]. destruct (IH a Ha) as [La Ca].
    destruct (IH b Hb) as [Lb Cb]. rewrite length_app, ones_app, La, Lb.
    split; [symmetry; apply capacity_succ|lia].
Qed.

Lemma join_sound h a b : sound h a -> sound h b -> sound (S h) (join h a b).
Proof. intros Ha Hb. simpl. auto. Qed.

Lemma children_sound h t : sound (S h) t ->
  sound h (fst (children t)) /\ sound h (snd (children t)) /\
  contents (S h) t = contents h (fst (children t)) ++ contents h (snd (children t)).
Proof.
  destruct t as [b|c a b]; simpl; intro H.
  - split; [exact I|]. split; [exact I|].
    rewrite capacity_succ, repeat_app. reflexivity.
  - tauto.
Qed.

Lemma prefix_correct h k t : sound h t ->
  prefix h k t = ones (firstn k (contents h t)).
Proof.
  revert k t. induction h as [|h IH]; intros k t H.
  all: unfold prefix; fold prefix; destruct (capacity _ <=? k) eqn:E.
  - apply Nat.leb_le in E. rewrite firstn_all2 by (rewrite (proj1 (sound_contents _ _ H)); lia).
    exact (proj2 (sound_contents _ _ H)).
  - destruct t as [b|c a b]; [|contradiction].
    simpl. apply Nat.leb_gt in E. assert (k=0) by (unfold capacity in E; simpl in E; lia).
    subst k. destruct b; reflexivity.
  - apply Nat.leb_le in E. rewrite firstn_all2 by (rewrite (proj1 (sound_contents _ _ H)); lia).
    exact (proj2 (sound_contents _ _ H)).
  - apply Nat.leb_gt in E. destruct t as [b|c a b].
    + simpl. rewrite firstn_repeat, ones_repeat, Nat.min_l by lia. reflexivity.
    + destruct H as [Ha [Hb Hc]]. simpl contents.
      rewrite firstn_app_count. destruct (sound_contents h a Ha) as [La Ca]. rewrite La.
      destruct (k <=? capacity h) eqn:K.
      * apply Nat.leb_le in K. rewrite IH by exact Ha.
        replace (k-capacity h) with 0 by lia. simpl. lia.
      * apply Nat.leb_gt in K. rewrite IH by exact Hb.
        rewrite (firstn_all2 (n:=k) (contents h a)) by (rewrite La; lia). lia.
Qed.

Lemma assign_correct h l r b t : sound h t ->
  sound h (assign h l r b t) /\
  contents h (assign h l r b t) = paint l r b (contents h t).
Proof.
  revert l r t. induction h as [|h IH]; intros l r t H.
  all: unfold assign; fold assign;
    destruct ((r =? 0) || (capacity _ <=? l)) eqn:E.
  - split; [exact H|]. symmetry. apply Bool.orb_true_iff in E.
    destruct E as [E|E].
    + apply Nat.eqb_eq in E. subst. apply paint_zero.
    + apply paint_after. apply Nat.leb_le in E. now rewrite (proj1 (sound_contents _ _ H)).
  - apply Bool.orb_false_iff in E. destruct E as [R L].
    apply Nat.eqb_neq in R. apply Nat.leb_gt in L.
    assert (Hl:l=0) by (unfold capacity in L; simpl in L; lia). subst l.
    assert (Htest : (0 =? 0) && (capacity 0 <=? r) = true).
    { apply Bool.andb_true_iff. split; [reflexivity|]. apply Nat.leb_le. unfold capacity; simpl; lia. }
    rewrite Htest. split; [exact I|]. simpl contents.
    symmetry. rewrite paint_full by (rewrite (proj1 (sound_contents _ _ H)); unfold capacity; simpl; lia).
    now rewrite (proj1 (sound_contents _ _ H)).
  - split; [exact H|]. symmetry. apply Bool.orb_true_iff in E.
    destruct E as [E|E].
    + apply Nat.eqb_eq in E. subst. apply paint_zero.
    + apply paint_after. apply Nat.leb_le in E. now rewrite (proj1 (sound_contents _ _ H)).
  - destruct ((l =? 0) && (capacity (S h) <=? r)) eqn:F.
    + apply Bool.andb_true_iff in F. destruct F as [L R]. apply Nat.eqb_eq in L. subst l.
      split; [exact I|]. simpl contents. symmetry.
      rewrite paint_full by (rewrite (proj1 (sound_contents _ _ H)); now apply Nat.leb_le).
      now rewrite (proj1 (sound_contents _ _ H)).
    + pose proof (children_sound h t H) as HC.
      destruct (children t) as [a c] eqn:C. simpl in HC.
      destruct HC as [Ha [Hc Hct]].
      destruct (IH l r a Ha) as [Sa Ea].
      destruct (IH (l-capacity h) (r-capacity h) c Hc) as [Sc Ec].
      split; [now apply join_sound|]. simpl contents. rewrite Ea, Ec, Hct, paint_app.
      now rewrite (proj1 (sound_contents h a Ha)).
Qed.

Lemma build_sound h xs : sound h (build h xs).
Proof. revert xs. induction h; intros xs; simpl; [exact I|now apply join_sound]. Qed.

Lemma build_correct h xs : length xs = capacity h -> contents h (build h xs) = xs.
Proof.
  revert xs. induction h as [|h IH]; intros xs H.
  - destruct xs as [|x [|y xs]]; simpl in H; try discriminate. reflexivity.
  - simpl build. simpl contents. rewrite !IH.
    + apply firstn_skipn.
    + rewrite skipn_length, H, capacity_succ. lia.
    + rewrite firstn_length, H, capacity_succ, Nat.min_l; lia.
Qed.
