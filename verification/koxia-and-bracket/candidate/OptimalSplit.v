From CoqCP Require Import Options.
From Submission Require Import KoxiaPaths.
Require Trusted.Spec Submission.SpecProperties.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat
  Lia Sorting.Permutation Logic.FunctionalExtensionality.
Import ListNotations.
Import Trusted.Spec Submission.SpecProperties.
Local Open Scope Z_scope.

Definition delta (b : bool) : Z := if b then 1 else -1.
Definition Good (initial : Z) (s : list bool) : Prop :=
  forall i, (i <= length s)%nat -> 0 <= initial + balance (firstn i s).

Lemma balance_app a b : balance (a ++ b) = balance a + balance b.
Proof.
  induction a as [| ch a IH]; cbn [app balance]; [lia |].
  rewrite IH. destruct ch; lia.
Qed.
Lemma balance_rev s : balance (rev s) = balance s.
Proof.
  induction s as [| ch s IH]; [reflexivity |].
  cbn [rev]. rewrite balance_app, IH. cbn [balance]. destruct ch; lia.
Qed.
Lemma balance_flip s : balance (map negb s) = - balance s.
Proof.
  induction s as [| ch s IH]; [reflexivity |].
  cbn [map]. destruct ch; cbn [negb balance]; rewrite IH; lia.
Qed.
Definition flipRev (s : list bool) := rev (map negb s).
Lemma flipRev_length s : length (flipRev s) = length s.
Proof. unfold flipRev. rewrite length_rev, length_map. reflexivity. Qed.
Lemma flipRev_balance s : balance (flipRev s) = - balance s.
Proof. unfold flipRev. rewrite balance_rev, balance_flip. reflexivity. Qed.
Lemma flipRev_involution s : flipRev (flipRev s) = s.
Proof.
  unfold flipRev. rewrite map_rev, rev_involutive, map_map.
  replace (fun x : bool => negb (negb x)) with (fun x : bool => x).
  - apply map_id.
  - apply functional_extensionality. intros []; reflexivity.
Qed.

Lemma Good_zero s : Good 0 s <-> forall i, (i <= length s)%nat ->
  0 <= balance (firstn i s).
Proof. unfold Good. setoid_rewrite Z.add_0_l. reflexivity. Qed.
Lemma Good_cons initial ch s : Good initial (ch :: s) <->
  0 <= initial /\ Good (initial + delta ch) s.
Proof.
  unfold Good. split.
  - intro h. split.
    + specialize (h 0%nat ltac:(cbn; lia)). cbn [firstn balance] in h. lia.
    + intros i hi. specialize (h (S i) ltac:(cbn; lia)).
      cbn [firstn balance] in h. unfold delta. destruct ch; lia.
  - intros [hi h] [| i] bound.
    + cbn [firstn balance]. lia.
    + cbn [firstn balance]. specialize (h i ltac:(cbn in bound; lia)).
      unfold delta in h. destruct ch; lia.
Qed.

Fixpoint scan (s : list bool) (height : nat) : option nat :=
  match s with
  | [] => Some height
  | true :: s => scan s (S height)
  | false :: s => match height with O => None | S h => scan s h end
  end.

Lemma scan_characterization s height final : scan s height = Some final <->
  Z.of_nat height + balance s = Z.of_nat final /\ Good (Z.of_nat height) s.
Proof.
  induction s as [| ch s IH] in height, final |- *.
  - cbn [scan balance]. split.
    + intro equal. injection equal as equal. subst final. split; [lia |].
      intros i hi. assert (i = 0%nat) by (cbn in hi; lia). subst i.
      cbn [firstn balance]. lia.
    + intros [equal _]. f_equal. lia.
  - destruct ch.
    + cbn [scan balance]. rewrite IH, Good_cons. cbn [delta].
      rewrite Nat2Z.inj_succ. split; intros [total good].
      * split; [lia |]. split; [lia |].
        replace (Z.of_nat height + 1) with (Z.of_nat height + 1) by lia. exact good.
      * destruct good as [_ good]. split; [lia | exact good].
    + destruct height as [| height].
      * cbn [scan]. split; [discriminate |].
        intros [_ good]. apply Good_cons in good. destruct good as [_ good].
        specialize (good 0%nat ltac:(lia)). rewrite firstn_O in good.
        change (0 <= -1) in good. lia.
      * cbn [scan balance]. rewrite IH, Good_cons. cbn [delta].
        rewrite Nat2Z.inj_succ. split; intros [total good].
        -- split; [lia |]. split; [lia |].
           replace (Z.succ (Z.of_nat height) + -1) with (Z.of_nat height) by lia. exact good.
        -- destruct good as [_ good]. split; [lia |].
           replace (Z.succ (Z.of_nat height) + -1) with (Z.of_nat height) in good by lia.
           exact good.
Qed.

Lemma scan_Dyck s : scan s 0 = Some 0%nat <-> Dyck s.
Proof.
  rewrite scan_characterization. unfold Dyck. rewrite Good_zero. cbn [Z.of_nat].
  rewrite Z.add_0_l. reflexivity.
Qed.

Lemma Dyck_flipRev s : Dyck (flipRev s) <-> Dyck s.
Proof.
  assert (forward : forall s, Dyck s -> Dyck (flipRev s)).
  { intros word [total prefixes]. split.
    - rewrite flipRev_balance, total. reflexivity.
    - intros i bound. unfold flipRev. rewrite firstn_rev, length_map, skipn_map.
      rewrite balance_rev, balance_flip.
      pose proof (balance_app (firstn (length word - i) word) (skipn (length word - i) word)) as parts.
      rewrite firstn_skipn, total in parts.
      specialize (prefixes (length word - i)%nat ltac:(lia)). lia. }
  split.
  - intro h. pose proof (forward (flipRev s) h) as other. rewrite flipRev_involution in other. exact other.
  - apply forward.
Qed.

Fixpoint maxSuffix (s : list bool) : Z :=
  match s with [] => 0 | ch :: s => Z.max (balance (ch :: s)) (maxSuffix s) end.

Lemma maxSuffix_nonnegative s : 0 <= maxSuffix s.
Proof.
  induction s as [| ch s IH]; [reflexivity |]. cbn [maxSuffix].
  eapply Z.le_trans; [exact IH | apply Z.le_max_r].
Qed.
Lemma maxSuffix_whole s : balance s <= maxSuffix s.
Proof. destruct s; [reflexivity | apply Z.le_max_l]. Qed.
Lemma maxSuffix_bound s i : balance (skipn i s) <= maxSuffix s.
Proof.
  induction s as [| ch s IH] in i |- *.
  - destruct i; reflexivity.
  - destruct i as [| i]; [apply maxSuffix_whole |]. cbn [skipn maxSuffix].
    eapply Z.le_trans; [apply IH | apply Z.le_max_r].
Qed.
Lemma maxSuffix_least s upper : 0 <= upper ->
  (forall i, (i <= length s)%nat -> balance (skipn i s) <= upper) -> maxSuffix s <= upper.
Proof.
  induction s as [| ch s IH]; [auto |]. intros hu bound. cbn [maxSuffix].
  apply Z.max_lub.
  - apply (bound 0%nat). cbn. lia.
  - apply IH; [exact hu |]. intros i hi. apply (bound (S i)). cbn. lia.
Qed.

Lemma greedyHeight_formula s height : Z.of_nat (greedyHeight s height) =
  Z.max (Z.of_nat height + balance s) (maxSuffix s).
Proof.
  induction s as [| ch s IH] in height |- *.
  - cbn [greedyHeight balance maxSuffix]. rewrite Z.add_0_r, Z.max_l by lia. reflexivity.
  - destruct ch.
    + cbn [greedyHeight]. rewrite IH. cbn [maxSuffix balance]. rewrite Nat2Z.inj_succ.
      rewrite Z.max_assoc.
      rewrite (Z.max_l (Z.of_nat height + (1 + balance s)) (1 + balance s)) by lia.
      f_equal. lia.
    + destruct height as [| height].
      * cbn [greedyHeight]. rewrite IH. cbn [Z.of_nat maxSuffix balance].
        pose proof (maxSuffix_whole s) as hw.
        rewrite Z.max_r by lia. rewrite Z.max_r by lia. rewrite Z.max_r by lia. reflexivity.
      * cbn [greedyHeight]. rewrite IH. cbn [maxSuffix balance]. rewrite Nat2Z.inj_succ.
        rewrite Z.max_assoc.
        rewrite (Z.max_l (Z.succ (Z.of_nat height) + (-1 + balance s)) (-1 + balance s)) by lia.
        f_equal. lia.
Qed.

Definition SuffixNonpositive (s : list bool) : Prop :=
  forall i, (i <= length s)%nat -> balance (skipn i s) <= 0.

Lemma suffix_greedy_zero s : SuffixNonpositive s -> greedyHeight s 0 = 0%nat.
Proof.
  intro h. pose proof (maxSuffix_least s 0 ltac:(lia) h) as upper.
  pose proof (maxSuffix_nonnegative s) as lower.
  pose proof (h 0%nat ltac:(lia)) as total. rewrite skipn_O in total.
  pose proof (greedyHeight_formula s 0) as formula.
  replace (maxSuffix s) with 0 in formula by lia.
  cbn [Z.of_nat] in formula. rewrite Z.add_0_l, Z.max_r in formula by lia. lia.
Qed.

Fixpoint greedyMask (s : list bool) (height : nat) : list bool :=
  match s with
  | [] => []
  | true :: s => true :: greedyMask s (S height)
  | false :: s =>
      match height with O => false :: greedyMask s 0 | S h => true :: greedyMask s h end
  end.

Definition removed (s mask : list bool) := retain s (map negb mask).
Definition OnlyClose (s mask : list bool) := Forall (fun ch => ch = false) (removed s mask).
Definition OnlyOpen (s mask : list bool) := Forall (fun ch => ch = true) (removed s mask).

Lemma greedyMask_length s h : length (greedyMask s h) = length s.
Proof.
  induction s as [| ch s IH] in h |- *; [reflexivity |].
  destruct ch; cbn [greedyMask length]; [rewrite IH; reflexivity |].
  destruct h; cbn [length]; rewrite IH; reflexivity.
Qed.
Lemma greedyMask_scan s h : scan (retain s (greedyMask s h)) h = Some (greedyHeight s h).
Proof.
  induction s as [| ch s IH] in h |- *; [reflexivity |].
  destruct ch; cbn [greedyMask retain scan greedyHeight]; [apply IH |].
  destruct h; cbn [retain scan]; apply IH.
Qed.
Lemma greedyMask_only_close s h : OnlyClose s (greedyMask s h).
Proof.
  unfold OnlyClose, removed. induction s as [| ch s IH] in h |- *; [constructor |].
  destruct ch; cbn [greedyMask map negb retain]; [apply IH |].
  destruct h; cbn [map negb retain]; [constructor; [reflexivity | apply IH] | apply IH].
Qed.
Lemma close_witness s : SuffixNonpositive s -> exists mask,
  length mask = length s /\ OnlyClose s mask /\ Dyck (retain s mask).
Proof.
  intro h. exists (greedyMask s 0). split; [apply greedyMask_length |].
  split; [apply greedyMask_only_close |]. apply scan_Dyck.
  rewrite greedyMask_scan, suffix_greedy_zero by exact h. reflexivity.
Qed.

Lemma retain_app a b ma mb : length ma = length a ->
  retain (a ++ b) (ma ++ mb) = retain a ma ++ retain b mb.
Proof.
  induction a as [| ch a IH] in ma |- *; destruct ma as [| keep ma]; cbn; try discriminate.
  - reflexivity.
  - intro len. destruct keep; cbn; rewrite IH by lia; reflexivity.
Qed.
Lemma removed_app a b ma mb : length ma = length a ->
  removed (a ++ b) (ma ++ mb) = removed a ma ++ removed b mb.
Proof. intro h. unfold removed. rewrite map_app, retain_app; [reflexivity | rewrite length_map; exact h]. Qed.
Lemma partition_length s mask : length mask = length s ->
  (length (retain s mask) + length (removed s mask) = length s)%nat.
Proof.
  unfold removed. induction s as [| ch s IH] in mask |- *;
    destruct mask as [| keep mask]; cbn; try discriminate; [reflexivity |].
  intro len. destruct keep; cbn; specialize (IH mask ltac:(lia)); lia.
Qed.
Lemma partition_balance s mask : length mask = length s ->
  balance (retain s mask) + balance (removed s mask) = balance s.
Proof.
  unfold removed. induction s as [| ch s IH] in mask |- *;
    destruct mask as [| keep mask]; cbn; try discriminate; [reflexivity |].
  intro len. specialize (IH mask ltac:(lia)). destruct keep, ch; cbn [negb retain balance] in *; lia.
Qed.
Lemma balance_bounds s : - Z.of_nat (length s) <= balance s <= Z.of_nat (length s).
Proof.
  induction s as [| ch s IH]; [cbn; lia |]. cbn [balance length].
  rewrite Nat2Z.inj_succ. destruct ch; lia.
Qed.
Lemma all_close_balance s : Forall (fun ch => ch = false) s <->
  balance s = - Z.of_nat (length s).
Proof.
  induction s as [| ch s IH]; [cbn; intuition constructor |].
  rewrite Forall_cons_iff, IH. cbn [balance length]. rewrite Nat2Z.inj_succ.
  pose proof (balance_bounds s). destruct ch; split; intros h; try discriminate; intuition lia.
Qed.
Lemma all_open_balance s : Forall (fun ch => ch = true) s <->
  balance s = Z.of_nat (length s).
Proof.
  induction s as [| ch s IH]; [cbn; intuition constructor |].
  rewrite Forall_cons_iff, IH. cbn [balance length]. rewrite Nat2Z.inj_succ.
  pose proof (balance_bounds s). destruct ch; split; intros h; try discriminate; intuition lia.
Qed.

Definition MinimumCut (a b : list bool) : Prop :=
  forall i, (i <= length (a ++ b))%nat -> balance a <= balance (firstn i (a ++ b)).

Lemma cut_left_suffix a b : MinimumCut a b -> SuffixNonpositive a.
Proof.
  intros cut i bound. unfold MinimumCut in cut.
  specialize (cut i ltac:(rewrite length_app; lia)).
  rewrite firstn_app in cut.
  replace (i - length a)%nat with 0%nat in cut by lia. cbn [firstn app] in cut.
  rewrite app_nil_r in cut.
  pose proof (balance_app (firstn i a) (skipn i a)) as parts.
  rewrite firstn_skipn in parts. lia.
Qed.

Lemma cut_right_prefix a b : MinimumCut a b -> Good 0 b.
Proof.
  intros cut i bound. unfold MinimumCut in cut.
  specialize (cut (length a + i)%nat ltac:(rewrite length_app; lia)).
  rewrite firstn_app, firstn_all2 in cut by lia.
  replace (length a + i - length a)%nat with i in cut by lia.
  rewrite balance_app in cut. lia.
Qed.

Lemma good_flipRev_suffix s : Good 0 s -> SuffixNonpositive (flipRev s).
Proof.
  intros good i bound. unfold flipRev.
  rewrite skipn_rev, length_map, firstn_map, balance_rev, balance_flip.
  specialize (good (length s - i)%nat ltac:(lia)). lia.
Qed.

Lemma Dyck_app a b : Dyck a -> Dyck b -> Dyck (a ++ b).
Proof.
  intros [ta pa] [tb pb]. split; [rewrite balance_app; lia |].
  intros i bound. rewrite firstn_app, balance_app.
  destruct (le_dec i (length a)) as [within | past].
  - replace (i - length a)%nat with 0%nat by lia. rewrite firstn_O.
    cbn [balance]. specialize (pa i within). lia.
  - rewrite firstn_all2 by lia. rewrite ta.
    specialize (pb (i - length a)%nat ltac:(rewrite length_app in bound; lia)). lia.
Qed.

Lemma Good_app initial a b : Good initial (a ++ b) <->
  Good initial a /\ Good (initial + balance a) b.
Proof.
  split.
  - intro good. split.
    + intros i bound. specialize (good i ltac:(rewrite length_app; lia)).
      rewrite firstn_app in good. replace (i - length a)%nat with 0%nat in good by lia.
      rewrite firstn_O, app_nil_r in good. exact good.
    + intros i bound. specialize (good (length a + i)%nat ltac:(rewrite length_app; lia)).
      rewrite firstn_app, firstn_all2 in good by lia.
      replace (length a + i - length a)%nat with i in good by lia.
      rewrite balance_app in good. lia.
  - intros [ga gb] i bound. rewrite firstn_app, balance_app.
    destruct (le_dec i (length a)) as [within | past].
    + replace (i - length a)%nat with 0%nat by lia. rewrite firstn_O.
      cbn [balance]. specialize (ga i within). lia.
    + rewrite firstn_all2 by lia. specialize (gb (i - length a)%nat ltac:(rewrite length_app in bound; lia)).
      lia.
Qed.

Lemma Dyck_prefix_balance a b : Dyck (a ++ b) -> 0 <= balance a.
Proof.
  intros [_ good]. assert (g : Good 0 (a ++ b)) by (apply Good_zero; exact good).
  apply Good_app in g. destruct g as [g _]. specialize (g (length a) ltac:(lia)).
  rewrite firstn_all in g. lia.
Qed.

Lemma Dyck_split a b : Dyck (a ++ b) -> balance a = 0 -> Dyck a /\ Dyck b.
Proof.
  intros [total good] ba. assert (g : Good 0 (a ++ b)) by (apply Good_zero; exact good).
  apply Good_app in g. destruct g as [ga gb]. rewrite ba, Z.add_0_l in gb.
  rewrite balance_app, ba in total.
  split.
  - split; [exact ba |]. apply Good_zero. exact ga.
  - split; [lia |]. apply Good_zero. exact gb.
Qed.

Lemma retain_flip s mask : retain (map negb s) mask = map negb (retain s mask).
Proof.
  induction s as [| ch s IH] in mask |- *; destruct mask as [| keep mask]; cbn; try reflexivity.
  destruct keep; cbn; rewrite IH; reflexivity.
Qed.
Lemma retain_rev s mask : length mask = length s ->
  retain (rev s) (rev mask) = rev (retain s mask).
Proof.
  induction s as [| ch s IH] in mask |- *; destruct mask as [| keep mask]; cbn; try discriminate.
  - reflexivity.
  - intro len. rewrite retain_app by (rewrite !length_rev; lia).
    rewrite IH by lia. destruct keep; cbn [retain rev]; [reflexivity | apply app_nil_r].
Qed.
Lemma retain_flipRev s mask : length mask = length s ->
  retain (flipRev s) (rev mask) = flipRev (retain s mask).
Proof.
  intro len. unfold flipRev. rewrite <- map_rev, retain_flip, retain_rev by exact len.
  apply map_rev.
Qed.
Lemma removed_flipRev s mask : length mask = length s ->
  removed (flipRev s) (rev mask) = flipRev (removed s mask).
Proof.
  intro len. unfold removed. rewrite map_rev, retain_flipRev; [reflexivity | rewrite length_map; exact len].
Qed.
Lemma OnlyOpen_flipRev s mask : length mask = length s ->
  OnlyOpen s mask <-> OnlyClose (flipRev s) (rev mask).
Proof.
  intro len. unfold OnlyOpen, OnlyClose. rewrite removed_flipRev by exact len.
  unfold flipRev. split.
  - intro all. apply Forall_rev. apply Forall_map.
    eapply Forall_impl; [| exact all]. intros [] eq; cbn in *; congruence.
  - intro all. apply Forall_rev in all. rewrite rev_involutive in all.
    apply Forall_map in all. eapply Forall_impl; [| exact all].
    intros [] eq; cbn in *; congruence.
Qed.

Lemma minimum_halves_witness a b : MinimumCut a b -> exists ma mb,
  length ma = length a /\ length mb = length b /\
  OnlyClose a ma /\ Dyck (retain a ma) /\ OnlyOpen b mb /\ Dyck (retain b mb).
Proof.
  intro cut.
  destruct (close_witness a (cut_left_suffix a b cut)) as [ma [la [ca da]]].
  destruct (close_witness (flipRev b) (good_flipRev_suffix b (cut_right_prefix a b cut)))
    as [mb [lb [cb db]]].
  exists ma, (rev mb). split; [exact la |].
  assert (lr : length (rev mb) = length b) by (rewrite length_rev, lb, flipRev_length; reflexivity).
  split; [exact lr |]. split; [exact ca |]. split; [exact da |]. split.
  - apply OnlyOpen_flipRev; [exact lr |]. rewrite rev_involutive. exact cb.
  - apply Dyck_flipRev. rewrite <- retain_flipRev by exact lr. rewrite rev_involutive. exact db.
Qed.

Definition deletionCost s mask := Z.of_nat (length (removed s mask)).
Definition splitCost a b := balance b - balance a.

Lemma deletionCost_complement s mask : length mask = length s ->
  deletionCost s mask = Z.of_nat (length s) - Z.of_nat (length (retain s mask)).
Proof.
  intro len. pose proof (partition_length s mask len) as total.
  unfold deletionCost. lia.
Qed.

Lemma deletionCost_halves a b ma mb : length ma = length a -> length mb = length b ->
  OnlyClose a ma -> Dyck (retain a ma) -> OnlyOpen b mb -> Dyck (retain b mb) ->
  deletionCost (a ++ b) (ma ++ mb) = splitCost a b.
Proof.
  intros la lb ca [ba _] cb [bb _].
  pose proof (partition_balance a ma la) as pa.
  pose proof (partition_balance b mb lb) as pb.
  apply all_close_balance in ca. apply all_open_balance in cb.
  unfold deletionCost. rewrite removed_app by exact la. rewrite length_app, Nat2Z.inj_add.
  unfold splitCost. lia.
Qed.

Lemma deletionCost_lower a b ma mb : length ma = length a -> length mb = length b ->
  Dyck (retain (a ++ b) (ma ++ mb)) ->
  0 <= balance (retain a ma) /\
  splitCost a b + 2 * balance (retain a ma) <= deletionCost (a ++ b) (ma ++ mb).
Proof.
  intros la lb good. rewrite retain_app in good by exact la.
  pose proof (Dyck_prefix_balance _ _ good) as hnonneg.
  destruct good as [total _]. rewrite balance_app in total.
  pose proof (partition_balance a ma la) as pa.
  pose proof (partition_balance b mb lb) as pb.
  pose proof (balance_bounds (removed a ma)) as ra.
  pose proof (balance_bounds (removed b mb)) as rb.
  unfold deletionCost, splitCost. rewrite removed_app by exact la.
  rewrite length_app, Nat2Z.inj_add. split; [exact hnonneg | lia].
Qed.

Lemma deletionCost_any_lower a b mask : length mask = length (a ++ b) ->
  Dyck (retain (a ++ b) mask) -> splitCost a b <= deletionCost (a ++ b) mask.
Proof.
  intros len good.
  assert (la : length (firstn (length a) mask) = length a).
  { rewrite length_firstn, len, length_app, Nat.min_l by lia. reflexivity. }
  assert (lb : length (skipn (length a) mask) = length b).
  { rewrite length_skipn, len, length_app. lia. }
  pose proof (deletionCost_lower a b (firstn (length a) mask) (skipn (length a) mask) la lb) as lower.
  rewrite firstn_skipn in lower. specialize (lower good). destruct lower as [nonnegative lower]. lia.
Qed.

Lemma optimum_cost a b mask : MinimumCut a b -> Optimal (a ++ b) mask ->
  deletionCost (a ++ b) mask = splitCost a b.
Proof.
  intros cut [len [good maximal]].
  destruct (minimum_halves_witness a b cut) as [ma [mb [la [lb [ca [da [cb db]]]]]]].
  assert (lwhole : length (ma ++ mb) = length (a ++ b)) by (rewrite !length_app, la, lb; reflexivity).
  assert (gwhole : Dyck (retain (a ++ b) (ma ++ mb))).
  { rewrite retain_app by exact la. apply Dyck_app; assumption. }
  specialize (maximal (ma ++ mb) lwhole gwhole).
  pose proof (deletionCost_halves a b ma mb la lb ca da cb db) as witness.
  pose proof (deletionCost_any_lower a b mask len good) as lower.
  rewrite deletionCost_complement in witness by exact lwhole.
  rewrite deletionCost_complement in lower by exact len.
  rewrite deletionCost_complement by exact len. lia.
Qed.

Theorem optimal_halves a b ma mb : MinimumCut a b ->
  length ma = length a -> length mb = length b ->
  (Optimal (a ++ b) (ma ++ mb) <->
   OnlyClose a ma /\ Dyck (retain a ma) /\ OnlyOpen b mb /\ Dyck (retain b mb)).
Proof.
  intros cut la lb. split.
  - intro optimal.
    pose proof (optimum_cost a b (ma ++ mb) cut optimal) as cost.
    destruct optimal as [len [good _]].
    destruct (deletionCost_lower a b ma mb la lb good) as [hnonneg lower].
    assert (zero : balance (retain a ma) = 0) by lia.
    rewrite retain_app in good by exact la.
    destruct (Dyck_split _ _ good zero) as [da db].
    pose proof (partition_balance a ma la) as pa.
    pose proof (partition_balance b mb lb) as pb.
    pose proof (balance_bounds (removed a ma)) as ra.
    pose proof (balance_bounds (removed b mb)) as rb.
    destruct db as [bb gb].
    unfold deletionCost, splitCost in cost. rewrite removed_app in cost by exact la.
    rewrite length_app, Nat2Z.inj_add in cost.
    split.
    + unfold OnlyClose. apply all_close_balance. lia.
    + split; [exact da |]. split.
      * unfold OnlyOpen. apply all_open_balance. lia.
      * split; assumption.
  - intros [ca [da [cb db]]].
    assert (len : length (ma ++ mb) = length (a ++ b)) by (rewrite !length_app, la, lb; reflexivity).
    split; [exact len |]. split.
    + rewrite retain_app by exact la. apply Dyck_app; assumption.
    + intros other lother gother.
      pose proof (deletionCost_any_lower a b other lother gother) as bound.
      pose proof (deletionCost_halves a b ma mb la lb ca da cb db) as cost.
      rewrite deletionCost_complement in bound by exact lother.
      rewrite deletionCost_complement in cost by exact len. lia.
Qed.
