From CoqCP Require Import Options.

Require Export Trusted.Spec.
From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lists.List Bool.Bool Lia.
From Stdlib Require Import ZArith.ZArith.
Import ListNotations.
Local Open Scope nat_scope.

(* A partition probe is two country queries, with sentinels answered locally. *)
Fixpoint search (fuel : nat) (p : nat -> bool) (lo hi : nat) : nat :=
  match fuel with
  | 0 => lo
  | S fuel =>
      if lo <? hi then
        let mid := (lo + hi) / 2 in
        if p mid then search fuel p lo mid else search fuel p (S mid) hi
      else lo
  end.
Fixpoint probes (fuel : nat) (p : nat -> bool) (lo hi : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel =>
      if lo <? hi then
        let mid := (lo + hi) / 2 in
        mid :: if p mid then probes fuel p lo mid else probes fuel p (S mid) hi
      else []
  end.

Lemma midpoint_bounds lo hi (h : lo < hi) :
  lo <= (lo + hi) / 2 < hi /\
  2 * ((lo + hi) / 2) <= lo + hi < 2 * (S ((lo + hi) / 2)).
Proof.
  pose proof (Nat.div_mod (lo + hi) 2 ltac:(lia)) as hd.
  pose proof (Nat.mod_upper_bound (lo + hi) 2 ltac:(lia)) as hm.
  nia.
Qed.

Lemma search_correct fuel p low high lo hi
  (hInterval : low <= lo /\ lo <= hi /\ hi <= high)
  (hWidth : hi - lo < 2 ^ fuel)
  (hHigh : p hi = true)
  (hLow : forall x, low <= x < lo -> p x = false)
  (hMono : forall x y, low <= x -> x <= y -> y <= high ->
    p x = true -> p y = true) :
  low <= search fuel p lo hi <= high /\
  p (search fuel p lo hi) = true /\
  (forall x, low <= x < search fuel p lo hi -> p x = false).
Proof.
  induction fuel as [| fuel IH] in lo, hi, hInterval, hWidth, hHigh, hLow |- *.
  - cbn [search] in *. assert (lo = hi) by (cbn in hWidth; lia).
    subst hi. repeat split; try lia; assumption.
  - cbn [search]. destruct (lo <? hi) eqn:hTest.
    + apply Nat.ltb_lt in hTest.
      pose proof (midpoint_bounds lo hi hTest) as hm.
      rewrite Nat.pow_succ_r in hWidth by lia.
      destruct (p ((lo + hi) / 2)) eqn:hMid.
      * apply IH; try assumption; try lia; nia.
      * apply IH; try assumption; try lia; try nia.
        intros x hx. destruct (p x) eqn:hxP; [| reflexivity].
        assert (bad : p ((lo + hi) / 2) = true).
        { apply (hMono x); try assumption; lia. }
        congruence.
    + apply Nat.ltb_ge in hTest. assert (lo = hi) by lia.
      subst hi. repeat split; try lia; assumption.
Qed.

Lemma probes_length fuel p lo hi : length (probes fuel p lo hi) <= fuel.
Proof.
  induction fuel as [| fuel IH] in lo, hi |- *; [cbn; lia |].
  cbn [probes]. destruct (lo <? hi); [| cbn; lia].
  destruct (p ((lo + hi) / 2)); cbn [length].
  - pose proof (IH lo ((lo+hi)/2)). lia.
  - pose proof (IH (S ((lo+hi)/2)) hi). lia.
Qed.

Lemma probes_bounds fuel p lo hi x :
  lo <= hi -> In x (probes fuel p lo hi) -> lo <= x < hi.
Proof.
  induction fuel as [| fuel IH] in lo, hi |- *.
  - cbn [probes In]. tauto.
  - cbn [probes]. intros hRange hIn. destruct (lo <? hi) eqn:hTest.
    + apply Nat.ltb_lt in hTest.
      pose proof (midpoint_bounds lo hi hTest) as hm.
      cbn [In] in hIn. destruct hIn as [heq | hIn]; [subst x; lia |].
      destruct (p ((lo+hi)/2)).
      * pose proof (IH lo ((lo+hi)/2) ltac:(lia) hIn). lia.
      * pose proof (IH (S ((lo+hi)/2)) hi ltac:(lia) hIn). lia.
    + contradiction.
Qed.

(* Counts all real country scores strictly greater than s. *)

Lemma above_cut f n s t
  (hBound : t <= n)
  (hPrefix : forall r, 1 <= r <= t -> s < f r)
  (hSuffix : forall r, t < r <= n -> f r <= s) :
  above f n s = t.
Proof.
  induction n as [| n IH] in t, hBound, hPrefix, hSuffix |- *.
  - cbn [above]. lia.
  - cbn [above]. destruct (Nat.eq_dec t (S n)) as [heq | hne].
    + subst t. assert (hLast : (s <? f (S n)) = true).
      { apply Nat.ltb_lt. apply hPrefix. lia. }
      rewrite hLast.
      assert (hRest : above f n s = n).
      { apply IH; [lia | |].
        - intros r hr. apply hPrefix. lia.
        - intros r hr. lia. }
      rewrite hRest. lia.
    + assert (hLast : (s <? f (S n)) = false).
      { apply Nat.ltb_ge. apply hSuffix. lia. }
      rewrite hLast, Nat.add_0_r. apply IH; try lia; try assumption.
      intros r hr. apply hSuffix. lia.
Qed.


(* Constructing sentinels from exactly the task's ordinary input assumptions. *)
Definition extend (n : nat) (raw : nat -> nat) (i : nat) :=
  if i =? 0 then ceiling else if i <=? n then raw i else 0.
Lemma extend_valid n raw
  (hBounds : forall i, 1 <= i <= n -> 1 <= raw i <= 1000000000)
  (hSorted : forall i j, 1 <= i -> i < j -> j <= n -> raw j < raw i) :
  country_valid n (extend n raw).
Proof.
  unfold country_valid. split; [reflexivity |]. split.
  - unfold extend.
    assert (hz : (S n =? 0) = false) by (apply Nat.eqb_neq; lia).
    assert (hn : (S n <=? n) = false) by (apply Nat.leb_gt; lia).
    rewrite hz, hn. reflexivity.
  - intros x y hxy hyn. unfold extend.
    destruct (x =? 0) eqn:hx; destruct (y =? 0) eqn:hy.
    + apply Nat.eqb_eq in hy. lia.
    + apply Nat.eqb_eq in hx. subst x.
      destruct (y <=? n) eqn:hyN.
      * apply Nat.leb_le in hyN. pose proof (hBounds y ltac:(lia)). unfold ceiling. lia.
      * unfold ceiling. lia.
    + apply Nat.eqb_eq in hy. lia.
    + apply Nat.eqb_neq in hx. apply Nat.eqb_neq in hy.
      assert (hxN : (x <=? n) = true) by (apply Nat.leb_le; lia).
      rewrite hxN. destruct (y <=? n) eqn:hyN.
      * apply Nat.leb_le in hyN. apply hSorted; lia.
      * pose proof (hBounds x ltac:(lia)). lia.
Qed.

Section Contest.
  Variables (n k : nat) (F S : nat -> nat).
  Hypothesis hn : 1 <= n.
  Hypothesis hk : 1 <= k <= 2 * n.
  Hypothesis hF : country_valid n F.
  Hypothesis hS : country_valid n S.
  Hypothesis hDistinct : forall i j, 1 <= i <= n -> 1 <= j <= n -> F i <> S j.

  Definition low := k - n.
  Definition high := Nat.min k n.
  Definition crossing i := F (Datatypes.S i) <? S (k - i).
  Definition partition := search 17 crossing low high.
  Definition answer := Nat.min (F partition) (S (k - partition)).
  Local Notation kth_highest := (Trusted.Spec.kth_highest n k F S).

  Lemma feasible_bounds : low <= high /\ high <= n /\ high <= k.
  Proof. unfold low, high. pose proof (Nat.le_min_l k n). pose proof (Nat.le_min_r k n). lia. Qed.
  Lemma descending_le f (hf : country_valid n f) x y :
    x <= y -> y <= Datatypes.S n -> f y <= f x.
  Proof.
    intros hxy hy. destruct (Nat.eq_dec x y); [subst; lia |].
    destruct hf as [_ [_ hd]]. specialize (hd x y ltac:(lia) hy). lia.
  Qed.
  Lemma score_positive f (hf : country_valid n f) i : i <= n -> 0 < f i.
  Proof.
    intro hi. destruct hf as [_ [hz hd]].
    specialize (hd i (Datatypes.S n) ltac:(lia) ltac:(lia)). rewrite hz in hd. exact hd.
  Qed.
  Lemma score_below_ceiling f (hf : country_valid n f) i :
    1 <= i <= Datatypes.S n -> f i < ceiling.
  Proof.
    intro hi. destruct hf as [hz [_ hd]].
    specialize (hd 0 i ltac:(lia) ltac:(lia)). rewrite hz in hd. exact hd.
  Qed.

  Lemma crossing_monotone x y :
    low <= x -> x <= y -> y <= high -> crossing x = true -> crossing y = true.
  Proof.
    intros hx hxy hy hp. unfold crossing in *. apply Nat.ltb_lt in hp. apply Nat.ltb_lt.
    pose proof feasible_bounds as hb.
    assert (hyN : y <= n) by lia.
    assert (hxS : k - x <= n) by (unfold low in hx; lia).
    pose proof (descending_le F hF (Datatypes.S x) (Datatypes.S y) ltac:(lia) ltac:(lia)).
    pose proof (descending_le S hS (k-y) (k-x) ltac:(lia) ltac:(lia)). lia.
  Qed.

  Lemma crossing_high : crossing high = true.
  Proof.
    unfold crossing, high. apply Nat.ltb_lt.
    destruct (le_dec k n) as [hkn | hkn].
    - rewrite Nat.min_l by lia. rewrite Nat.sub_diag.
      destruct hS as [hs _]. rewrite hs. apply score_below_ceiling; [exact hF | lia].
    - rewrite Nat.min_r by lia. destruct hF as [_ [hf _]]. rewrite hf.
      apply score_positive; [exact hS | lia].
  Qed.

  Lemma partition_correct (hSize : n <= 100000) :
    low <= partition <= high /\ crossing partition = true /\
    (forall x, low <= x < partition -> crossing x = false).
  Proof.
    unfold partition. apply search_correct.
    - pose proof feasible_bounds. lia.
    - pose proof feasible_bounds.
      (* Compute the closed bound with binary integers, avoiding expansion of
         131,072 unary successors in the portable VM fallback. *)
      assert (hp : 100000 < 2^17).
      { apply Nat2Z.inj_lt. rewrite Nat2Z.inj_pow.
        change (100000 < 2^17)%Z. vm_compute. reflexivity. }
      lia.
    - apply crossing_high.
    - intros x hx. lia.
    - exact crossing_monotone.
  Qed.

  Lemma partition_other_boundary i
    (hi : low <= i <= high) (hMin : forall x, low <= x < i -> crossing x = false) :
    S (Datatypes.S (k-i)) < F i.
  Proof.
    pose proof feasible_bounds as hb.
    destruct (Nat.eq_dec i low) as [heq | hne].
    - subst i. unfold low. destruct (le_dec k n) as [hkn | hkn].
      + replace (k-n) with 0 by lia. destruct hF as [hf _]. rewrite hf.
        apply score_below_ceiling; [exact hS | lia].
      + replace (k-(k-n)) with n by lia. destruct hS as [_ [hs _]]. rewrite hs.
        apply score_positive; [exact hF | unfold low in *; lia].
    - assert (hPred : crossing (i-1) = false) by (apply hMin; lia).
      unfold crossing in hPred. replace (Datatypes.S (i-1)) with i in hPred by lia.
      replace (k-(i-1)) with (Datatypes.S (k-i)) in hPred by lia.
      apply Nat.ltb_ge in hPred.
      assert (hj : Datatypes.S (k-i) <= n) by (unfold low in *; lia).
      assert (hiReal : 1 <= i <= n) by lia.
      pose proof (hDistinct i (Datatypes.S (k-i)) hiReal ltac:(lia)). lia.
  Qed.

  Lemma partition_rank i
    (hi : low <= i <= high)
    (hFirst : F (Datatypes.S i) < S (k-i))
    (hOther : S (Datatypes.S (k-i)) < F i) :
    kth_highest (Nat.min (F i) (S (k-i))).
  Proof.
    pose proof feasible_bounds as hb.
    assert (hiN : i <= n) by lia.
    assert (hjN : k-i <= n) by (unfold low in hi; lia).
    assert (hSum : i+(k-i) = k) by lia.
    destruct (le_dec (F i) (S (k-i))) as [hFS | hSF].
    - rewrite Nat.min_l by assumption.
      assert (hiPos : 1 <= i).
      { destruct i; [| lia]. destruct hF as [hf _]. rewrite hf in hFS.
        assert (hjPos : 1 <= k-0 <= Datatypes.S n) by lia.
        pose proof (score_below_ceiling S hS (k-0) hjPos). lia. }
      assert (hStrict : F i < S (k-i)).
      { destruct (Nat.eq_dec (k-i) 0) as [hz | hnz].
        - rewrite hz. destruct hS as [hs _]. rewrite hs. apply score_below_ceiling; [exact hF | lia].
        - pose proof (hDistinct i (k-i) ltac:(lia) ltac:(lia)). lia. }
      split.
      + left. exists i. auto.
      + assert (hCountF : above F n (F i) = i-1).
        { apply above_cut; [lia | |].
          - intros r hr. destruct hF as [_ [_ hd]]. apply hd; lia.
          - intros r hr. apply descending_le; [exact hF | lia | lia]. }
        assert (hCountS : above S n (F i) = k-i).
        { apply above_cut; [lia | |].
          - intros r hr. pose proof (descending_le S hS r (k-i) ltac:(lia) ltac:(lia)). lia.
          - intros r hr. pose proof (descending_le S hS (Datatypes.S (k-i)) r ltac:(lia) ltac:(lia)). lia. }
        rewrite hCountF, hCountS. lia.
    - rewrite Nat.min_r by lia.
      assert (hjPos : 1 <= k-i).
      { destruct (Nat.eq_dec (k-i) 0) as [hz | hnz]; [| lia].
        rewrite hz in hSF. destruct hS as [hs _]. rewrite hs in hSF.
        pose proof (score_below_ceiling F hF i ltac:(lia)). lia. }
      split.
      + right. exists (k-i). auto.
      + assert (hCountS : above S n (S (k-i)) = (k-i)-1).
        { apply above_cut; [lia | |].
          - intros r hr. destruct hS as [_ [_ hd]]. apply hd; lia.
          - intros r hr. apply descending_le; [exact hS | lia | lia]. }
        assert (hCountF : above F n (S (k-i)) = i).
        { apply above_cut; [lia | |].
          - intros r hr. pose proof (descending_le F hF r i ltac:(lia) ltac:(lia)). lia.
          - intros r hr. pose proof (descending_le F hF (Datatypes.S i) r ltac:(lia) ltac:(lia)). lia. }
        rewrite hCountF, hCountS. lia.
  Qed.

  Theorem answer_correct (hSize : n <= 100000) : kth_highest answer.
  Proof.
    destruct (partition_correct hSize) as [hi [hCross hMin]].
    apply Nat.ltb_lt in hCross. unfold answer.
    apply partition_rank; [exact hi | exact hCross |].
    apply partition_other_boundary; assumption.
  Qed.
End Contest.

Print Assumptions answer_correct.

Inductive Country := Finland | Sweden.
Definition Query := (Country * nat)%type.
Definition valid_query n (q : Query) := 1 <= snd q <= n.
Definition emit_query n c i : list Query :=
  if ((i =? 0) || (i =? S n))%bool then [] else [(c, i)].
Definition probe_queries n k i :=
  emit_query n Finland (S i) ++ emit_query n Sweden (k-i).
Definition query_trace n k F S :=
  flat_map (probe_queries n k) (probes 17 (crossing k F S) (low n k) (high n k)) ++
  emit_query n Finland (partition n k F S) ++
  emit_query n Sweden (k - partition n k F S).

Lemma emit_query_length n c i : length (emit_query n c i) <= 1.
Proof. unfold emit_query. destruct (((i =? 0) || (i =? S n))%bool); cbn; lia. Qed.
Lemma emit_query_legal n c i (hi : i <= S n) :
  Forall (valid_query n) (emit_query n c i).
Proof.
  unfold emit_query. destruct (((i =? 0) || (i =? S n))%bool) eqn:h.
  - constructor.
  - apply Bool.orb_false_iff in h. destruct h as [hz hn].
    apply Nat.eqb_neq in hz. apply Nat.eqb_neq in hn.
    constructor; [unfold valid_query; cbn; lia | constructor].
Qed.
Lemma probe_queries_length n k i : length (probe_queries n k i) <= 2.
Proof.
  unfold probe_queries. rewrite length_app.
  pose proof (emit_query_length n Finland (S i)).
  pose proof (emit_query_length n Sweden (k-i)). lia.
Qed.
Lemma probe_queries_legal n k i (hi : low n k <= i <= high n k) :
  Forall (valid_query n) (probe_queries n k i).
Proof.
  unfold probe_queries. apply Forall_app. split; apply emit_query_legal;
    unfold low, high in hi;
    pose proof (Nat.le_min_l k n); pose proof (Nat.le_min_r k n); lia.
Qed.
Lemma flat_probes_length n k indices :
  length (flat_map (probe_queries n k) indices) <= 2 * length indices.
Proof.
  induction indices as [| i indices IH]; [cbn; lia |].
  cbn [flat_map length]. rewrite length_app.
  pose proof (probe_queries_length n k i). lia.
Qed.

Theorem query_limit n k F S : length (query_trace n k F S) <= 36.
Proof.
  unfold query_trace. rewrite !length_app.
  pose proof (flat_probes_length n k (probes 17 (crossing k F S) (low n k) (high n k))).
  pose proof (probes_length 17 (crossing k F S) (low n k) (high n k)).
  pose proof (emit_query_length n Finland (partition n k F S)).
  pose proof (emit_query_length n Sweden (k-partition n k F S)). lia.
Qed.

Theorem queries_legal n k F S
  (hn : 1 <= n) (hk : 1 <= k <= 2*n)
  (hF : country_valid n F) (hS : country_valid n S) (hSize : n <= 100000) :
  Forall (valid_query n) (query_trace n k F S).
Proof.
  unfold query_trace. apply Forall_app. split.
  - apply Forall_flat_map. apply Forall_forall. intros i hIn.
    pose proof (feasible_bounds n k hn hk) as hb.
    pose proof (probes_bounds 17 (crossing k F S) (low n k) (high n k) i ltac:(lia) hIn) as hi.
    apply probe_queries_legal. lia.
  - destruct (partition_correct n k F S hn hk hF hS hSize) as [hi _].
    apply Forall_app. split; apply emit_query_legal;
      unfold low, high in hi;
      pose proof (Nat.le_min_l k n); pose proof (Nat.le_min_r k n); lia.
Qed.

Theorem solve_correct n k F S
  (hn : 1 <= n) (hk : 1 <= k <= 2*n) (hSize : n <= 100000)
  (hF : country_valid n F) (hS : country_valid n S)
  (hDistinct : forall i j, 1 <= i <= n -> 1 <= j <= n -> F i <> S j) :
  kth_highest n k F S (answer n k F S) /\
  Forall (valid_query n) (query_trace n k F S) /\
  length (query_trace n k F S) <= 36.
Proof.
  split.
  - apply answer_correct; assumption.
  - split.
    + apply queries_legal; assumption.
    + apply query_limit.
Qed.
Print Assumptions solve_correct.
