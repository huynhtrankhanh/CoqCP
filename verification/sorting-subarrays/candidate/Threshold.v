From CoqCP Require Import Options.
From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia ZArith.ZArith Sorting.Permutation.
From stdpp Require Import numbers sorting.
From Submission Require Import Bits.
Require Trusted.Spec.
Import ListNotations.

Definition bits (m : Z) (a : list Z) := map (Z.ltb m) a.
Definition regroup (xs : list bool) :=
  repeat false (length xs - ones xs) ++ repeat true (ones xs).
Definition bit_step (xs : list bool) (q : Trusted.Spec.query) :=
  let l := Nat.pred (fst q) in
  let r := snd q in
  let c := ones (firstn (r-l) (skipn l xs)) in
  paint (r-c) r true (paint l (r-c) false xs).

Lemma ones_permutation xs ys : Permutation xs ys -> ones xs = ones ys.
Proof. induction 1; simpl; lia. Qed.

Lemma forall_true_repeat xs : Forall (fun b => b = true) xs -> xs = repeat true (length xs).
Proof. induction 1 as [|b xs Hb Hxs IH]; simpl; [reflexivity|]. rewrite Hb. f_equal. exact IH. Qed.

Lemma sorted_bits_canonical xs :
  StronglySorted (fun x y : bool => x = true -> y = true) xs -> xs = regroup xs.
Proof.
  induction 1 as [|b xs Hsort IH Hall].
  - reflexivity.
  - destruct b.
    + assert (Ht : xs = repeat true (length xs)).
      { apply forall_true_repeat. rewrite List.Forall_forall in Hall |- *.
        intros b Hb. apply (Hall b Hb). reflexivity. }
      unfold regroup. simpl. rewrite Ht, ones_repeat, repeat_length.
      rewrite Nat.sub_diag. simpl. reflexivity.
    + unfold regroup in *. simpl. pose proof (ones_bound xs) as Hb.
      replace (S (length xs) - ones xs) with (S (length xs - ones xs)) by lia.
      simpl. now rewrite <- IH.
Qed.

Lemma sorted_threshold m xs : StronglySorted Z.le xs ->
  StronglySorted (fun x y : bool => x = true -> y = true) (bits m xs).
Proof.
  induction 1 as [|x xs Hsort IH Hall]; simpl; constructor; [exact IH|].
  apply List.Forall_forall. intros b Hb. unfold bits in Hb. apply in_map_iff in Hb.
  destruct Hb as [y [<- Hy]]. intro Hx. apply Z.ltb_lt in Hx. apply Z.ltb_lt.
  rewrite List.Forall_forall in Hall. specialize (Hall y Hy). lia.
Qed.

Lemma bits_sort m a : bits m (merge_sort Z.le a) = regroup (bits m a).
Proof.
  assert (Hs : StronglySorted (fun x y : bool => x = true -> y = true) (bits m (merge_sort Z.le a))).
  { apply sorted_threshold. apply StronglySorted_merge_sort.
    - intros x y z Hxy Hyz. lia.
    - intros x y. lia. }
  rewrite (sorted_bits_canonical _ Hs).
  unfold regroup. unfold bits. rewrite !length_map.
  pose proof (merge_sort_Permutation Z.le a) as Hp.
  rewrite (Permutation_length Hp).
  rewrite (ones_permutation _ _ (Permutation_map (Z.ltb m) Hp)). reflexivity.
Qed.

Lemma sort_length a q : Trusted.Spec.valid_query (length a) q ->
  length (Trusted.Spec.sort_subarray a q) = length a.
Proof.
  intros [Hl [Hlr Hr]]. unfold Trusted.Spec.sort_subarray.
  rewrite !length_app, (Permutation_length (merge_sort_Permutation Z.le _)),
    !length_firstn, !length_skipn.
  rewrite !Nat.min_l; lia.
Qed.

Lemma bit_step_segment xs q : Trusted.Spec.valid_query (length xs) q ->
  bit_step xs q = firstn (Nat.pred (fst q)) xs ++
    regroup (firstn (snd q-Nat.pred (fst q)) (skipn (Nat.pred (fst q)) xs)) ++
    skipn (snd q) xs.
Proof.
  intros [Hl [Hlr Hr]]. unfold bit_step.
  set (l := Nat.pred (fst q)). set (r := snd q).
  set (mid := firstn (r-l) (skipn l xs)). set (c := ones mid).
  assert (Hlr' : l <= r) by (unfold l, r; lia).
  assert (Hlen : length mid = r-l).
  { unfold mid. rewrite length_firstn, length_skipn, Nat.min_l; lia. }
  assert (Hc : c <= r-l) by (unfold c; pose proof (ones_bound mid); lia).
  rewrite paint_segment by (try rewrite paint_length; lia).
  rewrite paint_segment by lia.
  set (pre := firstn l xs). set (post := skipn (r-c) xs).
  assert (Lp : length pre = l) by (unfold pre; rewrite length_firstn, Nat.min_l; lia).
  rewrite firstn_app. rewrite firstn_app.
  rewrite Lp, firstn_all2 by lia.
  rewrite repeat_length, firstn_repeat.
  replace (r-c-l) with (r-l-c) by lia.
  rewrite Nat.min_id.
  rewrite Nat.sub_diag. simpl. rewrite app_nil_r.
  rewrite skipn_app, skipn_app, Lp, repeat_length.
  rewrite (skipn_all2 pre) by lia.
  rewrite (skipn_all2 (repeat false (r-l-c))) by (rewrite repeat_length; lia).
  simpl. unfold post. rewrite skipn_skipn.
  replace (r-l-(r-l-c)+(r-c)) with r by lia.
  replace (r-(r-c)) with c by lia.
  unfold regroup. rewrite Hlen. unfold c.
  rewrite !app_assoc. reflexivity.
Qed.

Lemma threshold_step m a q : Trusted.Spec.valid_query (length a) q ->
  bit_step (bits m a) q = bits m (Trusted.Spec.sort_subarray a q).
Proof.
  intro H. rewrite bit_step_segment by (unfold bits; now rewrite length_map).
  unfold Trusted.Spec.sort_subarray, bits. rewrite !map_app, !firstn_map, !skipn_map.
  rewrite firstn_map. pose proof (bits_sort m (firstn (snd q-Nat.pred (fst q)) (skipn (Nat.pred (fst q)) a))) as B.
  unfold bits in B. now rewrite <- B.
Qed.

Lemma execute_length a qs : Forall (Trusted.Spec.valid_query (length a)) qs ->
  length (Trusted.Spec.execute a qs) = length a.
Proof.
  revert a. induction qs as [|q qs IH]; intros a H; [reflexivity|].
  inversion H as [|? ? Hq Hqs]; subst. simpl.
  rewrite IH, sort_length; auto. now rewrite sort_length.
Qed.

Lemma forall_firstn {A} (P : A -> Prop) n xs : Forall P xs -> Forall P (firstn n xs).
Proof.
  intro H. revert n. induction H as [|x xs Hx Hxs IH]; intros [|n]; simpl; constructor; auto.
Qed.

Lemma forall_skipn {A} (P : A -> Prop) n xs : Forall P xs -> Forall P (skipn n xs).
Proof.
  intro H. revert n. induction H as [|x xs Hx Hxs IH]; intros [|n]; simpl; auto.
Qed.

Lemma execute_bounds (lo hi : Z) a qs :
  Forall (fun x => (lo <= x <= hi)%Z) a ->
  Forall (fun x => (lo <= x <= hi)%Z) (Trusted.Spec.execute a qs).
Proof.
  revert a. induction qs as [|q qs IH]; intros a Ha; [exact Ha|].
  apply IH. unfold Trusted.Spec.sort_subarray. apply Forall_app; split.
  - apply forall_firstn. exact Ha.
  - apply Forall_app; split.
    + eapply Permutation_Forall; [apply Permutation_sym; apply merge_sort_Permutation|].
      apply forall_firstn, forall_skipn. exact Ha.
    + apply forall_skipn. exact Ha.
Qed.
