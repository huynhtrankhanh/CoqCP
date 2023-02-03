From stdpp Require Import numbers list.
From CoqCP Require Import RegularBracketString PrefixApp ListsEqual SelectionSort Comparator Sorted SortedProperties SelectionSortProperties.

Definition compareSymbols (a b : Bracket) :=
  match a, b with
  | BracketOpen, BracketOpen => false
  | BracketOpen, BracketClose => true
  | BracketClose, BracketOpen => false
  | BracketClose, BracketClose => false
  end.

Lemma symbolComparator : Comparator Bracket.
Proof.
  exact {| compare := compareSymbols; transitive := ltac:(intros a b c h1 h2; destruct a; destruct b; destruct c; simpl in *; easy); irreflexive := ltac:(intro a; destruct a; easy); asymmetry := ltac:(intros a b h; destruct a; destruct b; simpl in *; easy); equalityExcludedMiddle := ltac:(intros a b; destruct a; destruct b; try (left; easy); try (right; easy)); connected := ltac:(intros a b h; destruct a; destruct b; simpl in *; try (left; easy); try (right; easy)) |}.
Defined.

Fixpoint fillLeftToRight (withBlanks : list (option Bracket)) (toFill : list Bracket) : list Bracket :=
  match withBlanks, toFill with
  | [], _ => []
  | (None :: tail), (toFill :: remaining) => toFill :: fillLeftToRight tail remaining
  | (None :: tail), [] => []
  | (Some stuff :: tail), remaining => stuff :: fillLeftToRight tail remaining
  end.

#[export] Instance optionBracketEqualityDecidable : EqDecision (option Bracket).
Proof. solve_decision. Defined.

Definition possibleToFill (withBlanks : list (option Bracket)) := exists toFill, length toFill = count_occ optionBracketEqualityDecidable withBlanks None /\ isBalanced (fillLeftToRight withBlanks toFill).

Definition getWitness (withBlanks : list (option Bracket)) :=
  let count := length withBlanks / 2 in
  let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
  let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
  repeat BracketOpen remainingOpenCount ++ repeat BracketClose remainingCloseCount.

Definition possibleToFillBool (withBlanks : list (option Bracket)) :=
  match bool_decide (2 | length withBlanks) with
  | false => false
  | true =>
    let count := length withBlanks / 2 in
    let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
    let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
    match bool_decide (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) <= count) && bool_decide (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) <= count) with
    | false => false
    | true => isBalancedBool (fillLeftToRight withBlanks (getWitness withBlanks))
    end
  end.

Lemma possibleToFillBool_oddLength (withBlanks : list (option Bracket)) (h : ~(2 | length withBlanks)) : ~possibleToFillBool withBlanks.
Proof.
  unfold possibleToFillBool; case_bool_decide; simpl; easy.
Qed.

Lemma possibleToFillBool_openCountGreaterHalfLength (withBlanks : list (option Bracket)) (h : length withBlanks / 2 < count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) : ~possibleToFillBool withBlanks.
Proof.
  unfold possibleToFillBool; case_bool_decide; simpl; try case_bool_decide; simpl; try easy; intro h1; case_bool_decide; simpl in h; lia.
Qed.

Lemma possibleToFillBool_closeCountGreaterHalfLength (withBlanks : list (option Bracket)) (h : length withBlanks / 2 < count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)) : ~possibleToFillBool withBlanks.
Proof.
  unfold possibleToFillBool; case_bool_decide; simpl; try case_bool_decide; simpl; try easy; intro h1; case_bool_decide; simpl in h; try lia; easy.
Qed.

Lemma possibleToFillBool_allConditionsSatisfied (withBlanks : list (option Bracket)) (h1 : (2 | length withBlanks)) (h2 : count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) <= length withBlanks / 2) (h3 : count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) <= length withBlanks / 2) : possibleToFillBool withBlanks <-> isBalancedBool (fillLeftToRight withBlanks (getWitness withBlanks)).
Proof.
  split; unfold possibleToFillBool in *; case_bool_decide; simpl; try case_bool_decide; simpl; try easy; case_bool_decide; easy.
Qed.

Lemma canAlwaysSwapCloseAndOpen (s1 s2 s3 : list Bracket) : isBalanced (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen] ++ s3) -> isBalanced (s1 ++ [BracketOpen] ++ s2 ++ [BracketClose] ++ s3).
Proof.
  intro h.
  pose proof isBalancedImpliesBalanceFactorBasedDefinition _ h as H.
  apply balanceFactorBasedDefinitionImpliesIsBalanced.
  destruct H as [h1 h2].
  split.
  - autorewrite with rewriteCount. autorewrite with rewriteCount in h1. lia.
  - intros prefix hPrefix. pose proof prefixAppCases _ _ _ hPrefix as H.
    destruct H.
    + epose proof h2 prefix ltac:(shelve). assumption.
    + destruct H as [l' h3]. rewrite h3 in hPrefix.
      pose proof prefix_app_inv s1 l' ([BracketOpen] ++ s2 ++ [BracketClose] ++ s3) hPrefix as hPrefix2.
      pose proof prefixAppCases _ _ _ hPrefix2 as H1.
      destruct H1.
      * rewrite h3. autorewrite with rewriteCount.
        destruct (prefixSingleton _ _ H).
        { rewrite H0. autorewrite with rewriteCount. rewrite ?Nat.add_0_r.
          epose proof h2 s1 ltac:(shelve). assumption. }
        { rewrite H0. autorewrite with rewriteCount. epose proof h2 s1 ltac:(shelve). lia. }
      * destruct H as [l0 H]. rewrite ?h3, ?H. autorewrite with rewriteCount.
        rewrite H in hPrefix2. pose proof prefix_app_inv _ _ _ hPrefix2 as H0.
        pose proof prefixAppCases _ _ _ H0 as H1. destruct H1.
        { epose proof h2 (s1 ++ [BracketClose] ++ l0) ltac:(shelve). autorewrite with rewriteCount in H2. lia. }
        { destruct H1 as [w H1]. rewrite H1 in H0. pose proof prefix_app_inv _ _ _ H0 as H2.
          pose proof prefixAppCases _ _ _ H2.
          destruct H3.
          - destruct (prefixSingleton _ _ H3).
            + rewrite H4 in H1. rewrite app_nil_r in H1. rewrite H1. epose proof h2 (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen]) ltac:(shelve) as H6. autorewrite with rewriteCount in H6. lia.
            + rewrite H4 in H1. rewrite H1. autorewrite with rewriteCount. epose proof h2 (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen]) ltac:(shelve) as H5. autorewrite with rewriteCount in H5. lia.
          - destruct H3 as [w' H3]. rewrite H3 in H2. pose proof prefix_app_inv _ _ _ H2 as H4.
            epose proof h2 (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen] ++ w') ltac:(shelve). autorewrite with rewriteCount in H5. rewrite H1, H3. autorewrite with rewriteCount. lia. }
  Unshelve.
  { destruct H as [w H]. exists (w ++ [BracketClose] ++ s2 ++ [BracketOpen] ++ s3). rewrite H. listsEqual. }
  { exists ([BracketClose] ++ s2 ++ [BracketOpen] ++ s3). reflexivity. }
  { exists ([BracketClose] ++ s2 ++ [BracketOpen] ++ s3). reflexivity. }
  { destruct H1 as [w H1]. exists (w ++ [BracketOpen] ++ s3). rewrite H1. listsEqual. }
  { exists s3. listsEqual. }
  { exists s3. listsEqual. }
  { destruct H4 as [w1 H4]. exists w1. rewrite H4. listsEqual. }
Qed.

Lemma fillLeftToRightPreservesLength (withBlanks : list (option Bracket)) (witness : list Bracket) (h : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : length (fillLeftToRight withBlanks witness) = length withBlanks.
Proof.
  revert witness h. induction withBlanks; intros.
  - easy.
  - destruct a; simpl.
    + simpl in h. rewrite (IHwithBlanks _ h). reflexivity.
    + destruct witness.
      * simpl in h. lia.
      * simpl. simpl in h. rewrite IHwithBlanks; lia.
Qed.

Lemma addThreeTypes (withBlanks : list (option Bracket)) : count_occ optionBracketEqualityDecidable withBlanks None + count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) = length withBlanks.
Proof.
  induction withBlanks.
  - easy.
  - destruct a.
    + destruct b; simpl; lia.
    + simpl. lia.
Qed.

Lemma subtractToCountNone (withBlanks : list (option Bracket)) : length withBlanks - (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)) = count_occ optionBracketEqualityDecidable withBlanks None.
Proof. pose proof addThreeTypes withBlanks. lia. Qed.

Lemma countSymbolAfterFill (withBlanks : list (option Bracket)) (toFill : list Bracket) (hValid : length toFill = count_occ optionBracketEqualityDecidable withBlanks None) (symbol : Bracket) : count_occ optionBracketEqualityDecidable withBlanks (Some symbol) + count_occ bracketEqualityDecidable toFill symbol = count_occ bracketEqualityDecidable (fillLeftToRight withBlanks toFill) symbol.
Proof.
  revert toFill hValid. induction withBlanks; intros toFill hValid.
  - simpl in *. rewrite (nil_length_inv _ hValid).
    easy.
  - destruct a.
    + destruct toFill.
      * pose proof IHwithBlanks [] ltac:(destruct b; simpl; easy) as H.
        simpl in H. rewrite Nat.add_0_r in H.
        assert (hCases : b = symbol \/ b <> symbol). { destruct b; destruct symbol; try (left; easy); try (right; easy). }
        destruct hCases as [hCases | hCases].
        { rewrite ?hCases. simpl. destruct symbol; simpl; rewrite H; lia. }
        { destruct b; destruct symbol; try easy; simpl; rewrite H; lia. }
      * simpl in hValid.
        assert (hCases : b = symbol \/ b <> symbol). { destruct b; destruct symbol; try (left; easy); try (right; easy). }
        destruct hCases as [hCases | hCases].
        { rewrite ?hCases. simpl. destruct symbol; destruct b0; simpl; rewrite <- IHwithBlanks; simpl; lia. }
        { destruct symbol; destruct b0; simpl in hCases; try easy; simpl; destruct b; simpl; rewrite <- IHwithBlanks; simpl; lia. }
    + assert (hSimplify : count_occ optionBracketEqualityDecidable (None :: withBlanks) (Some symbol) = count_occ optionBracketEqualityDecidable withBlanks (Some symbol)). { destruct symbol; easy. }
      rewrite hSimplify.
      destruct toFill.
      * simpl in hValid. lia.
      * simpl in hValid.
        assert (hCases : b = symbol \/ b <> symbol). { destruct b; destruct symbol; try (left; easy); try (right; easy). }
        destruct hCases as [hCases | hCases].
        { rewrite ?hCases. simpl. destruct symbol; simpl; rewrite <- IHwithBlanks; simpl; lia. }
        { destruct symbol; simpl in hCases; try easy; simpl; destruct b; simpl; rewrite <- IHwithBlanks; simpl; lia. }
Qed.

Lemma existingLeqAfterFill (withBlanks : list (option Bracket)) (toFill : list Bracket) (hValid : length toFill = count_occ optionBracketEqualityDecidable withBlanks None) (symbol : Bracket) : count_occ optionBracketEqualityDecidable withBlanks (Some symbol) <= count_occ bracketEqualityDecidable (fillLeftToRight withBlanks toFill) symbol.
Proof.
  pose proof countSymbolAfterFill withBlanks toFill hValid symbol.
  lia.
Qed.

Lemma alwaysSortedAux (closeCount : nat) : sorted BracketOpen compareSymbols (repeat BracketClose closeCount).
Proof.
  intros i j hI hJ.
  pose proof nth_repeat BracketClose closeCount j as h1.
  pose proof nth_repeat BracketClose closeCount i as h2.
  erewrite (nth_indep _ BracketOpen BracketClose ltac:(shelve)), (nth_indep _ BracketOpen BracketClose ltac:(shelve)), h1, h2.
  easy.
  Unshelve.
  - lia.
  - lia.
Qed.

Lemma alwaysSorted (openCount closeCount : nat) : sorted BracketOpen compareSymbols (repeat BracketOpen openCount ++ repeat BracketClose closeCount).
Proof.
  induction openCount.
  - simpl. apply alwaysSortedAux.
  - simpl. intros i j hI hJ.
    destruct i; destruct j; try easy.
    + simpl. remember (nth j (repeat BracketOpen openCount ++ repeat BracketClose closeCount) BracketOpen) as random.
      destruct random; easy.
    + pose proof IHopenCount i j ltac:(lia) ltac:(simpl in *; lia).
      simpl. assumption.
Qed.

Lemma possibleToFillIffPossibleToFillBool (withBlanks : list (option Bracket)) : possibleToFill withBlanks <-> possibleToFillBool withBlanks.
Proof.
  split.
  - intro hPossible. unfold possibleToFill in hPossible. unfold possibleToFillBool.
    case_bool_decide as hEven.
    + shelve.
    + destruct hPossible as [toFill [hLength hBalanced]].
      pose proof fillLeftToRightPreservesLength withBlanks toFill hLength as hPreserve.
      pose proof isBalancedEvenLength _ hBalanced.
      rewrite hPreserve in *. tauto.
    Unshelve.
    case_bool_decide as enoughBlanks1.
    * shelve.
    * destruct hPossible as [toFill [hLength hBalanced]].
      destruct (isBalancedImpliesBalanceFactorBasedDefinition _ hBalanced) as [hCount _].
      pose proof fillLeftToRightPreservesLength withBlanks toFill hLength as hPreserve.
      rewrite <- hPreserve, <- countOpenPlusCountClose, <- hCount in enoughBlanks1.
      assert (hSimplify : forall a : nat, (a + a) / 2 = a).
      { intro a.
        pose proof Nat.add_b2n_double_div2 false a.
        simpl in *. rewrite Nat.add_0_r in *. lia. }
      rewrite hSimplify in enoughBlanks1.
      pose proof existingLeqAfterFill withBlanks toFill ltac:(lia) BracketOpen as H.
      rewrite <- foldCountOpen in H. lia.
    Unshelve.
    case_bool_decide as enoughBlanks2; simpl.
    { shelve. }
    { destruct hPossible as [toFill [hLength hBalanced]].
      destruct (isBalancedImpliesBalanceFactorBasedDefinition _ hBalanced) as [hCount _].
      pose proof fillLeftToRightPreservesLength withBlanks toFill hLength as hPreserve.
      rewrite <- hPreserve, <- countOpenPlusCountClose, hCount in enoughBlanks2.
      assert (hSimplify : forall a : nat, (a + a) / 2 = a).
      { intro a.
        pose proof Nat.add_b2n_double_div2 false a.
        simpl in *. rewrite Nat.add_0_r in *. lia. }
      rewrite hSimplify in enoughBlanks2.
      pose proof existingLeqAfterFill withBlanks toFill ltac:(lia) BracketClose as H.
      rewrite <- foldCountClose in H. lia. }
    Unshelve.
    destruct hPossible as [toFill [hLength hBalanced]].
    remember (selectionSort BracketOpen (compare _ symbolComparator) toFill) as afterSorting.
    unfold getWitness.
    pose proof alwaysSorted (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)) as hWitnessSorted.
    pose proof selectionSortCorrect BracketOpen symbolComparator toFill as hSelectionSort.
    admit.
  - intro h. exists (getWitness withBlanks). split.
    + unfold getWitness. rewrite app_length, ?repeat_length.
      assert (H : length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)) = 2 * (length withBlanks / 2) - (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose))).
      { assert (H1 : length withBlanks / 2 >= count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)).
        { unfold possibleToFillBool in h; case_bool_decide; try case_bool_decide; easy. }
        assert (H2 : length withBlanks / 2 >= count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)).
        { unfold possibleToFillBool in h; case_bool_decide; try case_bool_decide; simpl in h; try case_bool_decide; easy. }
        lia. }
      rewrite H. rewrite <- (Nat.divide_div_mul_exact _ _ _).
      assert (H1 : (2 * length withBlanks) / 2 = length withBlanks).
      { rewrite Nat.mul_comm. apply Nat.div_mul. easy. }
      rewrite H1. rewrite subtractToCountNone. reflexivity.
      * easy.
      * unfold possibleToFillBool in h.
        case_bool_decide; easy.
    + unfold possibleToFillBool in h.
      case_bool_decide.
      * case_bool_decide; try case_bool_decide; simpl in h; try rewrite <- isBalancedIffIsBalancedBool in h; easy.
      * easy.
Admitted.
