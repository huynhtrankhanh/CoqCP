From CoqCP Require Import Options KoxiaPaths.
Require Trusted.Spec Submission.SpecProperties Submission.OptimalSplit.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat Lia
  Sorting.Permutation.
Import ListNotations Trusted.Spec Submission.SpecProperties Submission.OptimalSplit.
Local Open Scope nat_scope.

Definition prefixHistory (keep : bool) (history : list bool * nat) :=
  (keep :: fst history, snd history).
Fixpoint histories (s : list bool) (height : nat) : list (list bool * nat) :=
  match s with
  | [] => [([],height)]
  | true :: s => map (prefixHistory true) (histories s (S height))
  | false :: s =>
      match height with
      | O => map (prefixHistory false) (histories s 0)
      | S h => map (prefixHistory true) (histories s h) ++
               map (prefixHistory false) (histories s (S h))
      end
  end.

Lemma OnlyClose_cons ch s keep mask :
  OnlyClose (ch :: s) (keep :: mask) <->
  (keep = true \/ ch = false) /\ OnlyClose s mask.
Proof.
  unfold OnlyClose, removed. destruct ch, keep; cbn [map retain negb];
    rewrite ?Forall_cons_iff; intuition discriminate.
Qed.

Lemma prefixHistory_member keep xs mask final :
  In (mask, final) (map (prefixHistory keep) xs) <->
  exists tail, mask = keep :: tail /\ In (tail, final) xs.
Proof.
  rewrite in_map_iff. split.
  - intros [[tail h] [equal member]]. cbn [prefixHistory fst snd] in equal.
    injection equal as eqmask eqh. subst h. exists tail. auto.
  - intros [tail [eqmask member]]. subst mask. exists (tail,final). auto.
Qed.

Theorem histories_characterization s height mask final :
  In (mask,final) (histories s height) <->
  length mask = length s /\ OnlyClose s mask /\ scan (retain s mask) height = Some final.
Proof.
  induction s as [| ch s IH] in height, mask, final |- *.
  - cbn [histories]. destruct mask as [| keep mask].
    + cbn [length retain scan]. unfold OnlyClose, removed. cbn.
      split; [intros [equal | impossible]; [injection equal as eq; subst; auto | contradiction] |].
      intros [_ [_ equal]]. injection equal as eq. subst. auto.
    + cbn [length]. split; [intros [equal | impossible]; [discriminate equal | contradiction] | lia].
  - destruct ch.
    + cbn [histories]. rewrite prefixHistory_member.
      split.
      * intros [tail [equal member]]. subst mask. apply IH in member.
        destruct member as [len [close scanned]]. cbn [length retain scan].
        split; [lia |]. split; [apply OnlyClose_cons; auto | exact scanned].
      * destruct mask as [| keep mask]; [cbn [length]; lia |].
        intros [len [close scanned]]. apply OnlyClose_cons in close.
        destruct close as [[eq | bad] close]; [subst keep | discriminate bad].
        exists mask. split; [reflexivity |]. apply IH. cbn [length retain scan] in *.
        split; [lia | auto].
    + destruct height as [| height].
      * cbn [histories]. rewrite prefixHistory_member. split.
        -- intros [tail [equal member]]. subst mask. apply IH in member.
           destruct member as [len [close scanned]]. cbn [length retain scan].
           split; [lia |]. split; [apply OnlyClose_cons; auto | exact scanned].
        -- destruct mask as [| keep mask]; [cbn [length]; lia |].
           intros [len [close scanned]]. apply OnlyClose_cons in close. destruct close as [_ close].
           destruct keep; [discriminate scanned |]. exists mask. split; [reflexivity |].
           apply IH. cbn [length retain scan] in *. split; [lia | auto].
      * cbn [histories]. rewrite in_app_iff, !prefixHistory_member. split.
        -- intros [[tail [equal member]] | [tail [equal member]]].
           ++ subst mask. apply IH in member. destruct member as [len [close scanned]].
              cbn [length retain scan]. split; [lia |].
              split; [apply OnlyClose_cons; auto | exact scanned].
           ++ subst mask. apply IH in member. destruct member as [len [close scanned]].
              cbn [length retain scan]. split; [lia |].
              split; [apply OnlyClose_cons; auto | exact scanned].
        -- destruct mask as [| keep mask]; [cbn [length]; lia |].
           intros [len [close scanned]]. apply OnlyClose_cons in close. destruct close as [_ close].
           destruct keep.
           ++ left. exists mask. split; [reflexivity |]. apply IH.
              cbn [length retain scan] in *. split; [lia | auto].
           ++ right. exists mask. split; [reflexivity |]. apply IH.
              cbn [length retain scan] in *. split; [lia | auto].
Qed.

Lemma bracketPaths_app s xs ys :
  bracketPaths s (xs ++ ys) = bracketPaths s xs ++ bracketPaths s ys.
Proof.
  induction s as [| ch s IH] in xs,ys |- *; [reflexivity |].
  cbn [bracketPaths]. destruct ch; unfold bracketAdvance;
    rewrite ?map_app, ?flat_map_app; apply IH.
Qed.
Lemma bracketPaths_empty s : bracketPaths s [] = [].
Proof. induction s as [| [] s IH]; cbn [bracketPaths bracketAdvance]; exact IH || reflexivity. Qed.

Theorem histories_paths s height : map snd (histories s height) = bracketPaths s [height].
Proof.
  induction s as [| ch s IH] in height |- *; [reflexivity |].
  destruct ch; cbn [histories bracketPaths bracketAdvance map].
  - rewrite map_map. change (map snd (histories s (S height)) = bracketPaths s [S height]). apply IH.
  - destruct height as [| height].
    + rewrite map_map. change (map snd (histories s 0) = bracketPaths s [0]). apply IH.
    + rewrite map_app, !map_map.
      change (map snd (histories s height) ++ map snd (histories s (S height)) =
        bracketPaths s [height; S height]).
      rewrite !IH. change (bracketPaths s [height] ++ bracketPaths s [S height] = bracketPaths s ([height] ++ [S height])). apply eq_sym, bracketPaths_app.
Qed.

Lemma histories_masks_unique s height : NoDup (map fst (histories s height)).
Proof.
  induction s as [| ch s IH] in height |- *.
  - cbn [histories map]. repeat constructor. auto.
  - destruct ch; cbn [histories].
    + rewrite map_map. change (NoDup (map (fun h => true :: fst h) (histories s (S height)))).
      rewrite <- (map_map fst (cons true)). apply cons_NoDup, IH.
    +
    destruct height as [| height].
    * rewrite map_map. change (NoDup (map (fun h => false :: fst h) (histories s 0))).
      rewrite <- (map_map fst (cons false)). apply cons_NoDup, IH.
    * rewrite map_app, !map_map. change (NoDup
        (map (fun h => true :: fst h) (histories s height) ++
         map (fun h => false :: fst h) (histories s (S height)))).
      rewrite <- (map_map fst (cons true)), <- (map_map fst (cons false)).
      apply List.NoDup_app; [apply cons_NoDup, IH | apply cons_NoDup, IH |].
      intros mask left right. apply in_map_iff in left. apply in_map_iff in right.
      destruct left as [ma [ea _]], right as [mb [eb _]]. subst mask. discriminate eb.
Qed.

Definition halfPredicate s mask :=
  balanced (retain s mask) && forallb (fun ch => negb ch) (removed s mask).
Definition halfMasks s := filter (halfPredicate s) (masks (length s)).

Lemma halfPredicate_true s mask : halfPredicate s mask = true <->
  Dyck (retain s mask) /\ OnlyClose s mask.
Proof.
  unfold halfPredicate. rewrite andb_true_iff, balanced_Dyck.
  unfold OnlyClose. rewrite forallb_forall, Forall_forall.
  split.
  - intros [dyck all]. split; [exact dyck |]. intros ch member.
    specialize (all ch member). destruct ch; cbn in all; congruence.
  - intros [dyck all]. split; [exact dyck |]. intros ch member.
    specialize (all ch member). subst ch. reflexivity.
Qed.
Lemma halfMasks_characterization s mask : In mask (halfMasks s) <->
  length mask = length s /\ OnlyClose s mask /\ Dyck (retain s mask).
Proof. unfold halfMasks. rewrite filter_In, masks_complete, halfPredicate_true. tauto. Qed.
Lemma halfMasks_unique s : NoDup (halfMasks s).
Proof. apply NoDup_filter, masks_unique. Qed.

Definition completedHistories s := filter (fun h => Nat.eqb (snd h) 0) (histories s 0).
Lemma completed_masks_characterization s mask :
  In mask (map fst (completedHistories s)) <->
  length mask = length s /\ OnlyClose s mask /\ Dyck (retain s mask).
Proof.
  unfold completedHistories. rewrite in_map_iff. split.
  - intros [[tail final] [equal member]]. cbn in equal. subst tail.
    apply filter_In in member. destruct member as [member done]. cbn in done.
    apply Nat.eqb_eq in done. subst final. apply histories_characterization in member.
    rewrite scan_Dyck in member. exact member.
  - intros [len [close dyck]]. exists (mask,0). split; [reflexivity |].
    apply filter_In. split; [apply histories_characterization; rewrite scan_Dyck; auto | reflexivity].
Qed.
Lemma map_filter_unique {A B} (f : A -> B) test xs :
  NoDup (map f xs) -> NoDup (map f (filter test xs)).
Proof.
  induction xs as [| x xs IH]; cbn; [auto |]. intro unique. inversion unique as [| ? ? fresh tail].
  destruct (test x); cbn; [constructor | apply IH; exact tail].
  - intro member. apply fresh. apply in_map_iff in member. destruct member as [y [eq member]].
    apply filter_In in member. apply in_map_iff. exists y. tauto.
  - apply IH. exact tail.
Qed.
Lemma halfMasks_completed s : Permutation (halfMasks s) (map fst (completedHistories s)).
Proof.
  apply NoDup_Permutation.
  - apply halfMasks_unique.
  - apply map_filter_unique, histories_masks_unique.
  - intro mask. rewrite halfMasks_characterization, completed_masks_characterization. reflexivity.
Qed.
Lemma count_occ_filter xs height :
  count_occ Nat.eq_dec xs height = length (filter (fun x => Nat.eqb x height) xs).
Proof.
  induction xs as [| x xs IH]; cbn -[Nat.eq_dec]; [reflexivity |].
  destruct (Nat.eq_dec x height) as [equal | different].
  - subst x. rewrite Nat.eqb_refl. cbn. f_equal. exact IH.
  - apply Nat.eqb_neq in different. rewrite different. exact IH.
Qed.
Theorem half_count_masks s : occurrences (bracketPaths s [0]) 0 = length (halfMasks s).
Proof.
  rewrite <- histories_paths. unfold occurrences. rewrite count_occ_filter.
  rewrite filter_map_swap. rewrite length_map.
  pose proof (Permutation_length (halfMasks_completed s)) as len.
  unfold completedHistories in len. rewrite length_map in len. lia.
Qed.

Theorem half_dp_matches_masks s : SuffixNonpositive s ->
  KoxiaPolynomial.run (eventsFrom s 0) (pathCoefficients [0]) 0%Z =
  Z.of_nat (length (halfMasks s)).
Proof.
  intro suffix. rewrite half_count_correct by (apply suffix_greedy_zero; exact suffix).
  rewrite half_count_masks. reflexivity.
Qed.
