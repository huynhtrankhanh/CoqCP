From CoqCP Require Import Options.
From Submission Require Import KoxiaPolynomial KoxiaPaths.
Require Trusted.Spec Submission.SpecProperties Submission.OptimalSplit Submission.HalfCounting.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat Lia
  Sorting.Permutation.
Import ListNotations Trusted.Spec Submission.SpecProperties Submission.OptimalSplit Submission.HalfCounting.
Local Open Scope nat_scope.

Definition rightMasks b := map (@rev bool) (halfMasks (flipRev b)).
Lemma rightMasks_characterization b mask : In mask (rightMasks b) <->
  length mask = length b /\ OnlyOpen b mask /\ Dyck (retain b mask).
Proof.
  unfold rightMasks. rewrite in_map_iff. split.
  - intros [tail [equal member]]. subst mask. apply halfMasks_characterization in member.
    destruct member as [len [close good]].
    assert (lr : length (rev tail) = length b) by (rewrite length_rev, len, flipRev_length; reflexivity).
    split; [exact lr |]. split.
    + apply OnlyOpen_flipRev; [exact lr |]. rewrite rev_involutive. exact close.
    + apply Dyck_flipRev. rewrite <- retain_flipRev by exact lr. rewrite rev_involutive. exact good.
  - intros [len [opens good]]. exists (rev mask). split; [apply rev_involutive |].
    apply halfMasks_characterization. split; [rewrite length_rev, flipRev_length; exact len |]. split.
    + apply OnlyOpen_flipRev; assumption.
    + rewrite retain_flipRev by exact len. apply Dyck_flipRev. exact good.
Qed.

Lemma map_injective_unique {A B} (f : A -> B) xs :
  (forall x y, f x = f y -> x = y) -> NoDup xs -> NoDup (map f xs).
Proof.
  intros injective unique. induction unique as [| x xs fresh unique IH]; cbn; [constructor |].
  constructor; [| exact IH]. intro member. apply in_map_iff in member.
  destruct member as [y [equal member]]. apply injective in equal. subst y. contradiction.
Qed.
Lemma rightMasks_unique b : NoDup (rightMasks b).
Proof.
  unfold rightMasks. apply map_injective_unique; [| apply halfMasks_unique].
  intros x y equal. apply (f_equal (@rev bool)) in equal. rewrite !rev_involutive in equal. exact equal.
Qed.

Definition combineMasks xs ys := flat_map (fun x : list bool => map (app x) ys) xs.
Lemma combineMasks_member xs ys mask : In mask (combineMasks xs ys) <->
  exists x y, In x xs /\ In y ys /\ mask = x ++ y.
Proof.
  unfold combineMasks. rewrite in_flat_map. split.
  - intros [x [member row]]. apply in_map_iff in row. destruct row as [y [equal membery]].
    exists x,y. auto.
  - intros [x [y [memberx [membery equal]]]]. subst mask.
    exists x. split; [exact memberx |]. apply in_map. exact membery.
Qed.
Lemma concat_prefix_equal (a b a' b' : list bool) : length a = length a' ->
  a ++ b = a' ++ b' -> a = a'.
Proof.
  intros len equal. apply (f_equal (firstn (length a))) in equal.
  rewrite !firstn_app, firstn_all in equal. rewrite len, firstn_all in equal.
  replace (length a' - length a') with 0 in equal by lia.
  rewrite firstn_O, !app_nil_r in equal. exact equal.
Qed.
Lemma combineMasks_unique xs ys n :
  NoDup xs -> NoDup ys -> (forall x, In x xs -> length x = n) ->
  NoDup (combineMasks xs ys).
Proof.
  intros uniqueX uniqueY lengths. induction uniqueX as [| x xs fresh unique IH].
  - constructor.
  - cbn [combineMasks flat_map]. apply List.NoDup_app.
    + apply map_injective_unique; [intros a b; apply app_inv_head | exact uniqueY].
    + apply IH. intros y member. apply lengths. right. exact member.
    + intros mask memberx membertail. apply in_map_iff in memberx.
      destruct memberx as [y [equal _]]. apply combineMasks_member in membertail.
      destruct membertail as [x' [y' [member [membery eqtail]]]].
      apply fresh. assert (same : x = x').
      { apply (concat_prefix_equal x y x' y').
        - rewrite (lengths x ltac:(left; reflexivity)), (lengths x' ltac:(right; exact member)). reflexivity.
        - congruence. }
      subst x'. exact member.
Qed.
Lemma combineMasks_length xs ys : length (combineMasks xs ys) = length xs * length ys.
Proof.
  induction xs as [| x xs IH]; cbn [combineMasks flat_map length Nat.mul]; [reflexivity |].
  fold (combineMasks xs ys). rewrite length_app, length_map, IH. reflexivity.
Qed.

Theorem optimalMasks_product a b : MinimumCut a b ->
  Permutation (optimalMasks (a ++ b)) (combineMasks (halfMasks a) (rightMasks b)).
Proof.
  intro cut. apply NoDup_Permutation.
  - apply optimalMasks_unique.
  - apply (combineMasks_unique _ _ (length a)); [apply halfMasks_unique | apply rightMasks_unique |].
    intros mask member. apply halfMasks_characterization in member. tauto.
  - intro mask. rewrite optimalMasks_characterization, combineMasks_member. split.
    + intro optimal. destruct optimal as [len [good maximal]].
      pose (ma := firstn (length a) mask). pose (mb := skipn (length a) mask).
      assert (la : length ma = length a).
      { unfold ma. rewrite length_firstn, len, length_app, Nat.min_l by lia. reflexivity. }
      assert (lb : length mb = length b).
      { unfold mb. rewrite length_skipn, len, length_app. lia. }
      assert (mask_eq : mask = ma ++ mb) by (unfold ma, mb; symmetry; apply firstn_skipn).
      assert (opt : Optimal (a ++ b) (ma ++ mb)) by (rewrite <- mask_eq; split; [exact len |]; split; [exact good | exact maximal]).
      apply (optimal_halves a b ma mb cut la lb) in opt. destruct opt as [ca [da [cb db]]].
      exists ma,mb. split; [apply halfMasks_characterization; auto |].
      split; [apply rightMasks_characterization; auto | exact mask_eq].
    + intros [ma [mb [membera [memberb equal]]]]. subst mask.
      apply halfMasks_characterization in membera. apply rightMasks_characterization in memberb.
      destruct membera as [la [ca da]], memberb as [lb [cb db]].
      apply (optimal_halves a b ma mb cut la lb). auto.
Qed.

Theorem number_optimal_masks a b : MinimumCut a b ->
  length (optimalMasks (a ++ b)) = length (halfMasks a) * length (halfMasks (flipRev b)).
Proof.
  intro cut. pose proof (Permutation_length (optimalMasks_product a b cut)) as len.
  rewrite combineMasks_length in len. unfold rightMasks in len. rewrite length_map in len. exact len.
Qed.

Definition halfDP s := run (eventsFrom s 0) (pathCoefficients [0]) 0%Z.
Definition abstractAnswer a b := (halfDP a * halfDP (flipRev b) mod 998244353)%Z.

Theorem abstract_solver_correct a b : MinimumCut a b ->
  abstractAnswer a b = Z.of_nat (answer (a ++ b)).
Proof.
  intro cut. unfold abstractAnswer, halfDP.
  rewrite !half_dp_matches_masks.
  - unfold answer. rewrite number_optimal_masks by exact cut.
    rewrite Nat2Z.inj_mul. symmetry. apply Z2Nat.id.
    apply Z.mod_pos_bound. lia.
  - apply good_flipRev_suffix. apply (cut_right_prefix a b). exact cut.
  - apply (cut_left_suffix a b). exact cut.
Qed.
