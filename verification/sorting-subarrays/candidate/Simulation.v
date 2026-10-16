From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia ZArith.ZArith.
From Submission Require Import Bits Tree Threshold.
Require Trusted.Spec.
Import ListNotations.

Definition tree_step h t (q : Trusted.Spec.query) :=
  let l := Nat.pred (fst q) in
  let r := snd q in
  let c := prefix h r t - prefix h l t in
  assign h (r-c) r true (assign h l (r-c) false t).

Fixpoint run h t (qs : list Trusted.Spec.query) :=
  match qs with [] => t | q :: qs => run h (tree_step h t q) qs end.

Fixpoint lookup h k t : bool :=
  match t with
  | Uniform b => b
  | Branch _ a b => match h with
    | 0 => false
    | S h' => if k <? capacity h' then lookup h' k a else lookup h' (k-capacity h') b
    end
  end.

Lemma tree_step_correct h t q : sound h t ->
  Trusted.Spec.valid_query (length (contents h t)) q ->
  sound h (tree_step h t q) /\ contents h (tree_step h t q) = bit_step (contents h t) q.
Proof.
  intros Hs [Hl [Hlr Hr]]. unfold tree_step, bit_step.
  rewrite !prefix_correct by exact Hs.
  rewrite ones_slice by lia.
  destruct (assign_correct h (Nat.pred (fst q))
    (snd q - ones (firstn (snd q - Nat.pred (fst q)) (skipn (Nat.pred (fst q)) (contents h t)))) false t Hs) as [S1 E1].
  destruct (assign_correct h
    (snd q - ones (firstn (snd q - Nat.pred (fst q)) (skipn (Nat.pred (fst q)) (contents h t))))
    (snd q) true _ S1) as [S2 E2].
  split; [exact S2|]. now rewrite E2, E1.
Qed.

Lemma firstn_app_left {A} n (xs ys : list A) : n <= length xs ->
  firstn n (xs ++ ys) = firstn n xs.
Proof.
  intro H. rewrite firstn_app. replace (n-length xs) with 0 by lia. simpl. apply app_nil_r.
Qed.

Lemma bit_step_app xs ys q : Trusted.Spec.valid_query (length xs) q ->
  bit_step (xs ++ ys) q = bit_step xs q ++ ys.
Proof.
  intros [Hl [Hlr Hr]]. unfold bit_step.
  rewrite <- !ones_slice by (try rewrite length_app; lia).
  rewrite !firstn_app_left by lia.
  set (c := ones (firstn (snd q) xs) - ones (firstn (Nat.pred (fst q)) xs)).
  rewrite !paint_app, paint_length.
  replace (Nat.pred (fst q)-length xs) with 0 by lia.
  replace (snd q-c-length xs) with 0 by lia.
  replace (snd q-length xs) with 0 by lia.
  rewrite !paint_zero. reflexivity.
Qed.

Lemma run_correct h qs a m pad t :
  Forall (Trusted.Spec.valid_query (length a)) qs -> sound h t ->
  contents h t = bits m a ++ pad ->
  sound h (run h t qs) /\ contents h (run h t qs) = bits m (Trusted.Spec.execute a qs) ++ pad.
Proof.
  revert a t. induction qs as [|q qs IH]; intros a t Hq Hs Hc.
  - simpl. auto.
  - inversion Hq as [|? ? Hhead Htail]; subst. simpl.
    assert (Hqtree : Trusted.Spec.valid_query (length (contents h t)) q).
    { rewrite Hc, length_app. unfold bits. rewrite length_map.
      destruct Hhead as [Hl [Hlr Hr]]. unfold Trusted.Spec.valid_query. simpl in *. lia. }
    destruct (tree_step_correct h t q Hs Hqtree) as [S E].
    apply IH.
    + now rewrite sort_length.
    + exact S.
    + rewrite E, Hc, bit_step_app by (unfold bits; now rewrite length_map).
      rewrite threshold_step by exact Hhead. reflexivity.
Qed.

Lemma lookup_correct h k t : sound h t -> k < capacity h ->
  lookup h k t = nth k (contents h t) false.
Proof.
  revert k t. induction h as [|h IH]; intros k [b|c a b] Hs Hk.
  - simpl in *. assert (k=0) by (unfold capacity in Hk; simpl in Hk; lia). now subst.
  - contradiction.
  - simpl. rewrite nth_repeat_any by exact Hk. reflexivity.
  - destruct Hs as [Ha [Hb Hc]]. simpl.
    destruct (k <? capacity h) eqn:E.
    + apply Nat.ltb_lt in E. rewrite IH by auto.
      rewrite app_nth1 by (rewrite (proj1 (sound_contents _ _ Ha)); lia). reflexivity.
    + apply Nat.ltb_ge in E. rewrite IH by (try exact Hb; rewrite capacity_succ in Hk; lia).
      rewrite app_nth2 by (rewrite (proj1 (sound_contents _ _ Ha)); lia).
      now rewrite (proj1 (sound_contents _ _ Ha)).
Qed.

Definition height (n : nat) := Nat.log2_up n.

Lemma height_capacity n : n <= capacity (height n).
Proof.
  unfold height, capacity. destruct (le_dec n 1) as [H|H].
  - rewrite Nat.log2_up_eqn0 by exact H. simpl. lia.
  - apply Nat.log2_up_spec. lia.
Qed.

Definition decide (a : list Z) (k : nat) (qs : list Trusted.Spec.query) (m : Z) : bool :=
  let h := height (length a) in
  let bs := bits m a in
  let t := build h (bs ++ repeat false (capacity h-length a)) in
  lookup h (Nat.pred k) (run h t qs).

Lemma decide_correct a k qs m : 1 <= k <= length a ->
  Forall (Trusted.Spec.valid_query (length a)) qs ->
  decide a k qs m = Z.ltb m (nth (Nat.pred k) (Trusted.Spec.execute a qs) 0%Z).
Proof.
  intros Hk Hqs. unfold decide.
  set (h := height (length a)). set (pad := repeat false (capacity h-length a)).
  assert (Hcap : length a <= capacity h) by apply height_capacity.
  assert (Hlen : length (bits m a ++ pad) = capacity h).
  { unfold pad, bits. rewrite length_app, length_map, repeat_length. lia. }
  pose proof (build_sound h (bits m a ++ pad)) as Hs.
  pose proof (build_correct h _ Hlen) as Hc.
  destruct (run_correct h qs a m pad _ Hqs Hs Hc) as [Sr Er].
  rewrite lookup_correct by (try exact Sr; lia).
  rewrite Er, app_nth1 by (unfold bits; rewrite length_map, execute_length by exact Hqs; lia).
  unfold bits. rewrite <- (map_nth (Z.ltb m) (Trusted.Spec.execute a qs) 0%Z (Nat.pred k)).
  apply nth_indep. rewrite length_map, execute_length by exact Hqs. lia.
Qed.
