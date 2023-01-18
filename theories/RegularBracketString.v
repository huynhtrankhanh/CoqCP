From stdpp Require Import numbers list.
Require Import Wellfounded.
From CoqCP Require Import ExistsInRange.

Inductive Bracket :=
| BracketOpen
| BracketClose.

Inductive isBalanced : list Bracket -> Prop :=
| EmptyBalanced : isBalanced []
| WrapBalanced (s : list Bracket) : isBalanced s -> isBalanced ([BracketOpen] ++ s ++ [BracketClose])
| JoinBalanced (s1 s2 : list Bracket) : isBalanced s1 -> isBalanced s2 -> isBalanced (s1 ++ s2).

#[export] Instance bracketEqualityDecidable : EqDecision Bracket.
Proof. solve_decision. Defined.

Definition countOpen (s : list Bracket) := count_occ bracketEqualityDecidable s BracketOpen.
Definition countClose (s : list Bracket) := count_occ bracketEqualityDecidable s BracketClose.

Definition balanceFactorBasedDefinition (s : list Bracket) := countOpen s = countClose s /\ forall prefix, prefix `prefix_of` s -> countOpen prefix >= countClose prefix.

Fixpoint isBalancedBoolAux (s : list Bracket) (balanceFactor : nat) :=
  match s with
  | [] => bool_decide (balanceFactor = 0)
  | (BracketOpen :: s) => isBalancedBoolAux s (S balanceFactor)
  | (BracketClose :: s) =>
    match balanceFactor with
    | 0 => false
    | (S balanceFactor) => isBalancedBoolAux s balanceFactor
    end
  end.

Definition isBalancedBool (s : list Bracket) := isBalancedBoolAux s 0.

Definition withInitialBalanceFactor (s : list Bracket) (balanceFactor : nat) := countOpen s + balanceFactor = countClose s /\ forall prefix, prefix `prefix_of` s -> countOpen prefix + balanceFactor >= countClose prefix.

Lemma ifSubstituteZero (s : list Bracket) : withInitialBalanceFactor s 0 <-> balanceFactorBasedDefinition s.
Proof.
  unfold balanceFactorBasedDefinition.
  unfold withInitialBalanceFactor.
  split.
  - intro H. rewrite Nat.add_0_r in H.
    split.
    * tauto.
    * destruct H as [_ H]. intros prefix h.
      pose proof H prefix h. lia.
  - intro H. rewrite Nat.add_0_r.
    split.
    * tauto.
    * destruct H as [_ H]. intros prefix h.
      pose proof H prefix h. lia.
Qed.

Lemma countOpenEmpty : countOpen [] = 0.
Proof. auto. Qed.
Lemma countCloseEmpty : countClose [] = 0.
Proof. auto. Qed.
Lemma countOpenConsOpen (s : list Bracket) : countOpen (BracketOpen :: s) = countOpen s + 1.
Proof. unfold countOpen. simpl. lia. Qed.
Lemma countOpenConsClose (s : list Bracket) : countOpen (BracketClose :: s) = countOpen s.
Proof. auto. Qed.
Lemma countCloseConsOpen (s : list Bracket) : countClose (BracketOpen :: s) = countClose s.
Proof. auto. Qed.
Lemma countCloseConsClose (s : list Bracket) : countClose (BracketClose :: s) = countClose s + 1.
Proof. unfold countClose. simpl. lia. Qed.
Lemma countOpenApp (s1 s2 : list Bracket) : countOpen (s1 ++ s2) = countOpen s1 + countOpen s2.
Proof. unfold countOpen. rewrite count_occ_app. reflexivity. Qed.
Lemma countCloseApp (s1 s2 : list Bracket) : countClose (s1 ++ s2) = countClose s1 + countClose s2.
Proof. unfold countClose. rewrite count_occ_app. reflexivity. Qed.

Create HintDb rewriteCount.
#[global] Hint Rewrite countOpenEmpty : rewriteCount.
#[global] Hint Rewrite countCloseEmpty : rewriteCount.
#[global] Hint Rewrite countOpenConsOpen : rewriteCount.
#[global] Hint Rewrite countOpenConsClose : rewriteCount.
#[global] Hint Rewrite countCloseConsOpen : rewriteCount.
#[global] Hint Rewrite countCloseConsClose : rewriteCount.
#[global] Hint Rewrite countOpenApp : rewriteCount.
#[global] Hint Rewrite countCloseApp : rewriteCount.

Lemma withInitialBalanceFactor_empty (balanceFactor : nat) : withInitialBalanceFactor [] balanceFactor <-> balanceFactor = 0.
Proof.
  unfold withInitialBalanceFactor.
  rewrite countOpenEmpty, countCloseEmpty. simpl.
  split.
  - tauto.
  - intros. split.
    + tauto.
    + intros prefix h. pose proof prefix_nil_inv _ h as h1.
      rewrite h1, countOpenEmpty, countCloseEmpty. lia.
Qed.

Lemma isBalancedBoolAux_empty (balanceFactor : nat) : isBalancedBoolAux [] balanceFactor = bool_decide (balanceFactor = 0).
Proof. easy. Qed.

Lemma withInitialBalanceFactor_consBracketOpen (s : list Bracket) (balanceFactor : nat) : withInitialBalanceFactor (BracketOpen :: s) balanceFactor <-> withInitialBalanceFactor s (S balanceFactor).
Proof.
  unfold withInitialBalanceFactor.
  split.
  - rewrite countOpenConsOpen, countCloseConsOpen.
    intro h. split.
    + lia.
    + intros prefix h1. destruct h as [h2 h3].
      pose proof (h3 (BracketOpen :: prefix)) (prefix_cons _ _ _ h1) as H.
      rewrite countOpenConsOpen, countCloseConsOpen in H. lia.
  - rewrite countOpenConsOpen, countCloseConsOpen.
    intro h. split.
    + lia.
    + intros prefix h1. destruct h as [h2 h3].
      destruct prefix.
      * rewrite countOpenEmpty, countCloseEmpty. lia.
      * pose proof prefix_cons_inv_1 _ _ _ _ h1 as H. rewrite H in *.
        rewrite countOpenConsOpen, countCloseConsOpen.
        pose proof h3 prefix (prefix_cons_inv_2 _ _ _ _ h1). lia.
Qed.

Lemma isBalancedBoolAux_consBracketOpen (s : list Bracket) (balanceFactor : nat) : isBalancedBoolAux (BracketOpen :: s) balanceFactor = isBalancedBoolAux s (S balanceFactor).
Proof. easy. Qed.

Lemma withInitialBalanceFactor_consBracketClose_balanceFactorZero (s : list Bracket) : withInitialBalanceFactor (BracketClose :: s) 0 <-> false.
Proof.
  unfold withInitialBalanceFactor.
  split.
  - intro h. rewrite countOpenConsClose, countCloseConsClose in h.
    destruct h as [h1 h2].
    assert (h3 : [BracketClose] `prefix_of` BracketClose :: s).
    { apply prefix_cons. apply prefix_nil. }
    pose proof h2 [BracketClose] h3 as H.
    rewrite countOpenConsClose, countCloseConsClose, countOpenEmpty, countCloseEmpty in H. lia.
  - easy.
Qed.

Lemma isBalancedBoolAux_consBracketClose_balanceFactorZero (s : list Bracket) : isBalancedBoolAux (BracketClose :: s) 0 = false.
Proof. easy. Qed.

Lemma withInitialBalanceFactor_consBracketClose_balanceFactorSucc (s : list Bracket) (balanceFactor : nat) : withInitialBalanceFactor (BracketClose :: s) (S balanceFactor) <-> withInitialBalanceFactor s balanceFactor.
Proof.
  unfold withInitialBalanceFactor.
  split.
  - intro h. rewrite countOpenConsClose, countCloseConsClose in h.
    destruct h as [h1 h2]. split.
    + lia.
    + intros prefix h.
      pose proof (h2 (BracketClose :: prefix) (prefix_cons _ _ _ h)) as H.
      rewrite countOpenConsClose, countCloseConsClose in H. lia.
  - intro h. rewrite countOpenConsClose, countCloseConsClose. split.
    + lia.
    + intros prefix h1. destruct h as [h2 h3].
      destruct prefix.
      * rewrite countOpenEmpty, countCloseEmpty. lia.
      * pose proof h3 prefix (prefix_cons_inv_2 _ _ _ _ h1) as H.
        pose proof prefix_cons_inv_1 _ _ _ _ h1 as H0. rewrite H0 in *.
        rewrite countOpenConsClose, countCloseConsClose. lia.
Qed.

Lemma isBalancedBoolAux_consBracketClose_balanceFactorSucc (s : list Bracket) (balanceFactor : nat) : isBalancedBoolAux (BracketClose :: s) (S balanceFactor) = isBalancedBoolAux s balanceFactor.
Proof. easy. Qed.

Lemma isBalancedBoolAuxIffWithInitialBalanceFactor (s : list Bracket) (balanceFactor : nat) : (isBalancedBoolAux s balanceFactor = true) <-> withInitialBalanceFactor s balanceFactor.
Proof.
  revert balanceFactor.
  induction s.
  - intro balanceFactor. rewrite isBalancedBoolAux_empty, withInitialBalanceFactor_empty. case_bool_decide; easy.
  - intro balanceFactor. destruct a.
    + rewrite isBalancedBoolAux_consBracketOpen, withInitialBalanceFactor_consBracketOpen. easy.
    + destruct balanceFactor.
      * rewrite isBalancedBoolAux_consBracketClose_balanceFactorZero, withInitialBalanceFactor_consBracketClose_balanceFactorZero. easy.
      * rewrite isBalancedBoolAux_consBracketClose_balanceFactorSucc, withInitialBalanceFactor_consBracketClose_balanceFactorSucc. easy.
Qed.

Lemma isBalancedBoolIffBalanceFactorBasedDefinition (s : list Bracket) : (isBalancedBool s = true) <-> balanceFactorBasedDefinition s.
Proof. unfold isBalancedBool. rewrite <- ifSubstituteZero. apply isBalancedBoolAuxIffWithInitialBalanceFactor. Qed.

Lemma prefixOfAppSingleton {A : Type} (l1 l2 : list A) (x : A) : l1 `prefix_of` l2 ++ [x] -> l1 `prefix_of` l2 \/ l1 = l2 ++ [x].
Proof.
  unfold prefix. intro h.
  destruct h as [w h].
  induction w using rev_ind.
  - right. rewrite app_nil_r in h. easy.
  - left. exists w. pose proof app_inj_tail l2 (l1 ++ w) x x0 as H.
    rewrite <- app_assoc in H. tauto.
Qed.

Lemma prefixAppCases {A : Type} (l x y : list A) (h : l `prefix_of` x ++ y) : l `prefix_of` x \/ exists l', l = x ++ l'.
Proof.
  induction y using rev_ind.
  - left. rewrite app_nil_r in h. tauto.
  - rewrite app_assoc in h. pose proof (prefixOfAppSingleton _ _ _ h). destruct H.
    * tauto.
    * rewrite H. right. exists (y ++ [x0]). rewrite app_assoc. easy.
Qed.

Lemma isBalancedImpliesBalanceFactorBasedDefinition (s : list Bracket) : isBalanced s -> balanceFactorBasedDefinition s.
Proof.
  intro h.
  induction h.
  - unfold balanceFactorBasedDefinition. rewrite countOpenEmpty, countCloseEmpty.
    split.
    + easy.
    + intros prefix h. rewrite (prefix_nil_inv _ h), countOpenEmpty, countCloseEmpty. lia.
  - unfold balanceFactorBasedDefinition.
    split.
    + unfold countOpen, countClose. repeat rewrite count_occ_app. simpl.
      unfold balanceFactorBasedDefinition in IHh.
      destruct IHh as [h1 _]. unfold countOpen, countClose in h1.
      lia.
    + unfold balanceFactorBasedDefinition in IHh. destruct IHh as [_ h1].
      intros prefix h2.
      simpl in h2. destruct prefix.
      * rewrite countOpenEmpty, countCloseEmpty. lia.
      * pose proof prefix_cons_inv_1 _ _ _ _ h2 as H0. rewrite H0 in *.
        rewrite countOpenConsOpen, countCloseConsOpen.
        pose proof prefix_cons_inv_2 _ _ _ _ h2 as H.
        pose proof prefixOfAppSingleton _ _ _ H. destruct H1.
        { pose proof h1 _ H1. lia. }
        { rewrite H1 in *. autorewrite with rewriteCount.
          assert (prefixSelf : s `prefix_of` s). { auto. }
          pose proof h1 s prefixSelf.
          lia. }
  - unfold balanceFactorBasedDefinition in *. autorewrite with rewriteCount.
    split.
    + lia.
    + intros prefix h.
      destruct IHh1 as [_ h3].
      destruct IHh2 as [_ h4].
      pose proof prefixAppCases _ _ _ h as H.
      destruct H.
      * pose proof h3 _ H. easy.
      * destruct H as [w H]. rewrite H in h. pose proof h4 _ (prefix_app_inv _ _ _ h).
        rewrite H. autorewrite with rewriteCount.
        assert (prefixSelf : s1 `prefix_of` s1). { auto. }
        pose proof h3 _ prefixSelf. lia.
Qed.

Definition canSplit (s : list Bracket) := existsInRange (length s - 2) (fun n => bool_decide (countOpen (take (S n) s) = countClose (take (S n) s))).

Lemma balanceFactorBasedDefinitionImpliesIsBalanced (s : list Bracket) : balanceFactorBasedDefinition s -> isBalanced s.
Proof.
  induction s using (well_founded_induction (wf_inverse_image _ nat _ (@length _) PeanoNat.Nat.lt_wf_0)).
  remember (bool_decide (length s = 0)) as hEmptyDecide.
  case_bool_decide as hEmpty.
  - rewrite (nil_length_inv _ hEmpty). intro h. exact EmptyBalanced.
  - clear HeqhEmptyDecide. clear hEmptyDecide.
    remember (bool_decide (length s = 1)) as hSingletonDecide.
    case_bool_decide as hSingleton.
    + intro h. unfold balanceFactorBasedDefinition in h.
      destruct h as [single _].
      destruct s.
      * easy.
      * destruct s.
        { destruct b; autorewrite with rewriteCount in single; lia. }
        { easy. }
    + clear HeqhSingletonDecide. clear hSingletonDecide.
      assert (hInequality : 1 < length s). { lia. }
      remember (canSplit s) as hCanSplitDecide.
      destruct hCanSplitDecide.
      * unfold canSplit in *. pose proof existsInRangeMeaning (length s - 2) (fun n => bool_decide (countOpen (take (S n) s) = countClose (take (S n) s))) as H0.
        assert (H1 : existsInRangeLogic (length s - 2) (λ n : nat, bool_decide (countOpen (take (S n) s) = countClose (take (S n) s)))).
        { assert (H2 : existsInRange (length s - 2) (λ n : nat, bool_decide (countOpen (take (S n) s) = countClose (take (S n) s))) = true).
          { easy. }
          destruct H0. pose proof Is_true_true_2 _ H2. tauto. }
        clear H0. clear HeqhCanSplitDecide. unfold existsInRangeLogic in H1.
        destruct H1 as [w H1].
        rewrite bool_decide_eq_true in H1.
        pose proof (H (take (S w) s)) as H0.
        assert (H2 : length (take (S w) s) < length s).
        { rewrite take_length. lia. }
        pose proof H0 H2 as H3.
        intro hBalanceFactor.
        assert (H4 : balanceFactorBasedDefinition (take (S w) s)).
        { split.
          - easy.
          - pose proof take_drop (S w) s. intros prefix h.
            destruct hBalanceFactor as [_ hBalanceFactor].
            assert (H5 : prefix `prefix_of` s).
            { unfold list.prefix. destruct h as [w1 h]. exists (w1 ++ drop (S w) s).
              rewrite app_assoc. rewrite <- h. rewrite take_drop. reflexivity. }
              pose proof hBalanceFactor _ H5. tauto. }
        pose proof (H3 H4) as hBalancedLeft.
        assert (H5 : balanceFactorBasedDefinition (drop (S w) s)).
        { rewrite <- (take_drop (S w)) in hBalanceFactor.
          unfold balanceFactorBasedDefinition in hBalanceFactor. autorewrite with rewriteCount in hBalanceFactor.
          destruct hBalanceFactor as [hBalanceFactorLeft hBalanceFactorRight].
          destruct H4 as [H4Left H4Right].
          split.
          - lia.
          - intros prefix h.
            pose proof hBalanceFactorRight (take (S w) s ++ prefix) (prefix_app _ _ _ h) as H4.
            autorewrite with rewriteCount in H4. lia. }
        pose proof H (drop (S w) s) as H6.
        assert (H7 : length (drop (S w) s) < length s).
        { rewrite drop_length. lia. }
        pose proof H6 H7 H5 as hBalancedRight.
        pose proof JoinBalanced _ _ hBalancedLeft hBalancedRight as H8.
        rewrite take_drop in H8. assumption.
      * unfold canSplit in *.
        assert (H1 : ~existsInRange (length s - 2) (λ n : nat, bool_decide (countOpen (take (S n) s) = countClose (take (S n) s)))).
        { rewrite Is_true_false. easy. }
        clear HeqhCanSplitDecide. rewrite notExistsInRangeMeaning in H1.
        unfold notExistsInRangeLogic in H1.
        intro h.
        assert (hUnwrap : exists t, s = [BracketOpen] ++ t ++ [BracketClose]).
        { exists (take (length s - 2) (drop 1 s)).
          destruct s.
          - simpl in hEmpty. lia.
          - destruct b.
            + unfold drop. rewrite cons_length. simpl.
              induction s using rev_ind.
              * simpl in hSingleton. lia.
              * clear IHs. rewrite app_length. simpl. rewrite Nat.add_sub.
                rewrite (take_app s [x]).
                destruct x.
                { destruct h as [h h1]. autorewrite with rewriteCount in h.
                  simpl in h.
                  assert (H2 : BracketOpen :: s `prefix_of` BracketOpen :: s ++ [BracketOpen]).
                  { unfold list.prefix. exists [BracketOpen]. easy. }
                  pose proof h1 (BracketOpen :: s) H2 as H0. autorewrite with rewriteCount in H0. lia. }
                { reflexivity. }
            + destruct h as [_ h].
              pose proof h [BracketClose] as H0.
              assert (H2 : [BracketClose] `prefix_of` BracketClose :: s).
              { unfold list.prefix. exists s. easy. }
              pose proof H0 H2 as H3.
              autorewrite with rewriteCount in H3. lia. }
          destruct hUnwrap as [w hUnwrap].
          rewrite hUnwrap in h. autorewrite with rewriteCount in h. simpl in h.
          destruct h as [h1 h2].
          autorewrite with rewriteCount in h1.
          assert (h3 : countOpen w = countClose w). { lia. }
          rewrite hUnwrap in H1. repeat rewrite app_length in H1. simpl in H1.
          assert (h4 : forall prefix : list Bracket, prefix `prefix_of` w -> countOpen prefix >= countClose prefix).
          { intros prefix h.
            autorewrite with rewriteCount.
            remember (bool_decide (prefix = w)) as hDecide.
            case_bool_decide as hSplit.
            - rewrite hSplit. lia.
            - pose proof (H1 (length prefix)) as H0.
              assert (H2_sub : length prefix <= length w + 1 - 1).
              { destruct h as [w1 h]. rewrite h. repeat rewrite app_length. simpl. lia. }
              assert (H2_sub2 : length prefix <> length w).
              { intro hContradiction. destruct h as [w1 h]. rewrite h in hContradiction. rewrite app_length in hContradiction.
                assert (lengthZero : length w1 = 0). { lia. }
                assert (w1Empty : w1 = []). { apply nil_length_inv. assumption. }
                rewrite w1Empty in h. rewrite app_nil_r in h.
                assert (hPrefixW : prefix = w). { easy. }
                pose proof (hSplit hPrefixW). assumption. }
              assert (H2 : length prefix < length w + 1 - 1). { lia. }
              pose proof H0 H2 as H3. rewrite bool_decide_spec in H3. clear H0. clear H2. autorewrite with rewriteCount in H3.
              assert (H4 : BracketOpen :: prefix `prefix_of` BracketOpen :: w ++ [BracketClose]).
              { apply prefix_cons. apply prefix_app_r. assumption. }
              pose proof h2 (BracketOpen :: prefix) H4 as H0. autorewrite with rewriteCount in H0.
              assert (H5 : take (length prefix) (w ++ [BracketClose]) = prefix).
              { destruct h as [w1 h]. rewrite h. rewrite <- app_assoc. rewrite take_app. reflexivity. }
              rewrite H5 in *.
              lia. }
          assert (H2 : balanceFactorBasedDefinition w). { split; assumption. }
          assert (H3 : length w < length s). { rewrite hUnwrap. repeat rewrite app_length. simpl. lia. }
          pose proof H w H3 H2 as H0.
          pose proof WrapBalanced _ H0.
          rewrite <- hUnwrap in H4. tauto.
Qed.
