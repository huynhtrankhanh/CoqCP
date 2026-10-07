From CoqCP Require Import Options.
Require Trusted.Spec.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat Lia.
Import ListNotations.
Import Trusted.Spec.
Local Open Scope nat_scope.

(* Validate the small specification against the literal mathematical problem.
   These proofs do not assert correctness of the generated solver. *)
Definition Dyck (s : list bool) : Prop :=
  balance s = 0%Z /\ forall i, i <= length s -> (0 <= balance (firstn i s))%Z.

Definition Optimal (s mask : list bool) : Prop :=
  length mask = length s /\ Dyck (retain s mask) /\
  forall other, length other = length s -> Dyck (retain s other) ->
    length (retain s other) <= length (retain s mask).

Lemma masks_complete n mask : In mask (masks n) <-> length mask = n.
Proof.
  induction n as [| n IH] in mask |- *.
  - cbn [masks]. destruct mask; cbn; intuition discriminate.
  - cbn [masks]. rewrite in_app_iff, !in_map_iff.
    split.
    + intros [[tail [equal member]] | [tail [equal member]]];
        subst mask; cbn; apply f_equal; apply IH; exact member.
    + destruct mask as [| ch tail]; cbn; [lia |].
      intro len. assert (member : In tail (masks n)) by (apply IH; lia).
      destruct ch.
      * right. exists tail. auto.
      * left. exists tail. auto.
Qed.

Lemma cons_NoDup (ch : bool) (xs : list (list bool)) :
  NoDup xs -> NoDup (map (cons ch) xs).
Proof.
  intro h. induction h as [| x xs hn hd IH]; cbn; [constructor |].
  constructor; [| exact IH]. intro bad. apply in_map_iff in bad.
  destruct bad as [y [eq hy]]. injection eq as same. subst y. contradiction.
Qed.

Lemma masks_unique n : NoDup (masks n).
Proof.
  induction n as [| n IH].
  - repeat constructor. intro h. exact h.
  - cbn [masks]. apply List.NoDup_app.
    + apply cons_NoDup. exact IH.
    + apply cons_NoDup. exact IH.
    + intros mask left right. apply in_map_iff in left. apply in_map_iff in right.
      destruct left as [a [ha _]], right as [b [hb _]].
      subst mask. discriminate hb.
Qed.

Lemma balanced_Dyck s : balanced s = true <-> Dyck s.
Proof.
  unfold balanced, Dyck. rewrite andb_true_iff, Z.eqb_eq, forallb_forall.
  split.
  - intros [total prefixes]. split; [exact total |].
    intros i bound. apply Z.leb_le. apply prefixes. apply in_seq. lia.
  - intros [total prefixes]. split; [exact total |].
    intros i member. apply Z.leb_le. apply prefixes. apply in_seq in member. lia.
Qed.

Lemma retain_bound s mask : length (retain s mask) <= length s.
Proof.
  induction s as [| ch s IH] in mask |- *; destruct mask as [| b mask]; cbn; try lia.
  destruct b; cbn; specialize (IH mask); lia.
Qed.

Lemma retain_delete_all s : retain s (repeat false (length s)) = [].
Proof. induction s; cbn; auto. Qed.

Lemma feasible_characterization s mask :
  In mask (feasible s) <-> length mask = length s /\ Dyck (retain s mask).
Proof.
  unfold feasible. rewrite filter_In, masks_complete, balanced_Dyck. reflexivity.
Qed.

Lemma feasible_nonempty s : feasible s <> [].
Proof.
  assert (member : In (repeat false (length s)) (feasible s)).
  { apply feasible_characterization. split; [apply repeat_length |].
    rewrite retain_delete_all. apply balanced_Dyck. reflexivity. }
  intro empty. rewrite empty in member. contradiction.
Qed.

Lemma fold_max_upper xs x : In x xs -> x <= fold_right Nat.max 0 xs.
Proof.
  induction xs as [| y xs IH]; cbn; [contradiction |].
  intros [-> | member].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact member | apply Nat.le_max_r].
Qed.

Lemma fold_max_least xs bound :
  (forall x, In x xs -> x <= bound) -> fold_right Nat.max 0 xs <= bound.
Proof.
  induction xs as [| x xs IH]; cbn; [lia |].
  intro h. apply Nat.max_lub.
  - apply h. left. reflexivity.
  - apply IH. intros y member. apply h. right. exact member.
Qed.

Lemma fold_max_attained xs : xs <> [] -> In (fold_right Nat.max 0 xs) xs.
Proof.
  induction xs as [| x xs IH]; cbn; [contradiction |]. intros _.
  destruct xs as [| y xs].
  - cbn. rewrite Nat.max_0_r. left. reflexivity.
  - destruct (Nat.max_dec x (fold_right Nat.max 0 (y :: xs))) as [eq | eq].
    + rewrite eq. left. reflexivity.
    + rewrite eq. right. apply IH. discriminate.
Qed.

Lemma longest_upper s mask : length mask = length s -> Dyck (retain s mask) ->
  length (retain s mask) <= longest s.
Proof.
  intros len good. unfold longest. apply fold_max_upper.
  apply in_map_iff. exists mask. split; [reflexivity |].
  apply feasible_characterization. auto.
Qed.

Lemma longest_attained s : exists mask,
  length mask = length s /\ Dyck (retain s mask) /\ length (retain s mask) = longest s.
Proof.
  assert (member : In (longest s)
    (map (fun mask => length (retain s mask)) (feasible s))).
  { unfold longest. apply fold_max_attained. intro empty.
    apply map_eq_nil in empty. apply (feasible_nonempty s). exact empty. }
  apply in_map_iff in member. destruct member as [mask [eq member]].
  apply feasible_characterization in member. exists mask. tauto.
Qed.

Lemma optimalMasks_characterization s mask :
  In mask (optimalMasks s) <-> Optimal s mask.
Proof.
  unfold optimalMasks, Optimal. rewrite filter_In, feasible_characterization, Nat.eqb_eq.
  split.
  - intros [[len good] equal]. split; [exact len |]. split; [exact good |].
    intros other len' good'. rewrite equal. apply longest_upper; assumption.
  - intros [len [good maximal]]. split; [auto |].
    destruct (longest_attained s) as [other [len' [good' equal]]].
    specialize (maximal other len' good').
    pose proof (longest_upper s mask len good). lia.
Qed.

Lemma optimalMasks_unique s : NoDup (optimalMasks s).
Proof.
  unfold optimalMasks, feasible. apply NoDup_filter. apply NoDup_filter.
  apply masks_unique.
Qed.

Lemma minimum_deletions s mask : Optimal s mask ->
  forall other, length other = length s -> Dyck (retain s other) ->
  length s - length (retain s mask) <= length s - length (retain s other).
Proof. intros [_ [_ optimal]] other len good. specialize (optimal other len good). lia. Qed.

Lemma optimal_iff_minimum_deletions s mask : Optimal s mask <->
  length mask = length s /\ Dyck (retain s mask) /\
  forall other, length other = length s -> Dyck (retain s other) ->
    length s - length (retain s mask) <= length s - length (retain s other).
Proof.
  split.
  - intros h. destruct h as [len [good maximal]]. split; [exact len |].
    split; [exact good |]. intros other len' good'.
    specialize (maximal other len' good'). lia.
  - intros [len [good minimal]]. split; [exact len |]. split; [exact good |].
    intros other len' good'. specialize (minimal other len' good').
    pose proof (retain_bound s mask). pose proof (retain_bound s other). lia.
Qed.

Lemma answer_range s : (0 <= Z.of_nat (answer s) < 998244353)%Z.
Proof.
  unfold answer.
  pose proof (Z.mod_pos_bound (Z.of_nat (length (optimalMasks s))) 998244353 ltac:(lia)) as range.
  rewrite Z2Nat.id by lia. exact range.
Qed.

Local Open Scope Z_scope.
Fixpoint decoded (bytes : list Z) : Z :=
  match bytes with
  | [] => 0
  | ch :: bytes => (ch - 48) * 10 ^ Z.of_nat (length bytes) + decoded bytes
  end.

Lemma decoded_last bytes ch : decoded (bytes ++ [ch]) = 10 * decoded bytes + ch - 48.
Proof.
  induction bytes as [| digit bytes IH].
  - change ((ch - 48) * 1 + 0 = 10 * 0 + ch - 48). ring.
  - cbn [app decoded]. rewrite length_app. cbn [length].
    rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    replace (10 ^ Z.of_nat 1) with 10 by reflexivity. rewrite IH. ring.
Qed.

Lemma decimal_decodes fuel value :
  0 <= Z.of_nat value < 10 ^ Z.of_nat fuel -> decoded (decimal fuel value) = Z.of_nat value.
Proof.
  induction fuel as [| fuel IH] in value |- *.
  - cbn [decimal]. cbn [Z.of_nat Z.pow]. intro bound.
    assert (value = 0%nat) by lia. subst value. reflexivity.
  - cbn [decimal]. intro bound. destruct (value <? 10)%nat eqn:small.
    + change ((Z.of_nat value + 48 - 48) * 1 + 0 = Z.of_nat value). ring.
    + rewrite decoded_last, IH.
      * rewrite Nat2Z.inj_div, Nat2Z.inj_mod.
        pose proof (Z.div_mod (Z.of_nat value) 10 ltac:(lia)). lia.
      * rewrite Nat2Z.inj_div. split; [apply Z.div_pos; lia |].
        apply Z.div_lt_upper_bound; [lia |].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in bound by lia. nia.
Qed.

Lemma decimal_digits fuel value : Forall (fun ch => 48 <= ch < 58) (decimal fuel value).
Proof.
  induction fuel as [| fuel IH] in value |- *; cbn [decimal]; [constructor |].
  destruct (value <? 10)%nat eqn:small.
  - apply Nat.ltb_lt in small. constructor; [lia | constructor].
  - apply Forall_app. split; [apply IH |].
    constructor; [pose proof (Nat.mod_upper_bound value 10 ltac:(lia)); lia | constructor].
Qed.

Lemma output_decimal_correct s : decoded (decimal 10 (answer s)) = Z.of_nat (answer s).
Proof.
  apply decimal_decodes. pose proof (answer_range s).
  change (0 <= Z.of_nat (answer s) < 10000000000). lia.
Qed.

Local Open Scope nat_scope.

Example sample_one : answer [true; false; false; true; true; false] = 4.
Proof. vm_compute. reflexivity. Qed.
Example sample_two : answer [true] = 1.
Proof. vm_compute. reflexivity. Qed.
Example duplicate_characters : answer [true; true; false] = 2.
Proof. vm_compute. reflexivity. Qed.
Example empty_sequence : balanced [] = true.
Proof. reflexivity. Qed.
