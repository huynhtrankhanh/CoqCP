From stdpp Require Import numbers list.
From CoqCP Require Import Options RegularBracketString PrefixApp ListsEqual SelectionSort Comparator Sorted SortedProperties SelectionSortProperties PropertyPreservedAfterSorting Completion.

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

#[export] Instance optionBracketEqualityDecidable : EqDecision (option Bracket).
Proof. solve_decision. Defined.

Definition possibleToFill (withBlanks : list (option Bracket)) := exists toFill, length toFill = count_occ optionBracketEqualityDecidable withBlanks None /\ isBalanced (fill withBlanks toFill).

Definition possibleToFill2 (withBlanks : list (option Bracket)) := exists completed, isCompletion withBlanks completed /\ isBalanced completed.

Lemma possibleToFillIffPossibleToFill2 withBlanks : possibleToFill withBlanks <-> possibleToFill2 withBlanks.
Proof.
  induction withBlanks as [| [head |] tail IH].
  - unfold possibleToFill, possibleToFill2. split; exists []; simpl; split; try done; exact EmptyBalanced.
  - split; intros [w [h1 h2]].
    + exists (fill (Some head :: tail) w). split.
      * now apply fillIsCompletion.
      * assumption.
    + exists (extractAnswers (Some head :: tail) w). split.
      * now apply extractAnswersLength.
      * now (rewrite extractAnswersCorrect; try apply extractAnswersLength).
  - split; intros [w [h1 h2]].
    + exists (fill (None :: tail) w). split.
      * now apply fillIsCompletion.
      * assumption.
    + exists (extractAnswers (None :: tail) w). split.
      * now apply extractAnswersLength.
      * now (rewrite extractAnswersCorrect; try apply extractAnswersLength).
Qed.

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
    | true => isBalancedBool (fill withBlanks (getWitness withBlanks))
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

Lemma possibleToFillBool_allConditionsSatisfied (withBlanks : list (option Bracket)) (h1 : (2 | length withBlanks)) (h2 : count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) <= length withBlanks / 2) (h3 : count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) <= length withBlanks / 2) : possibleToFillBool withBlanks <-> isBalancedBool (fill withBlanks (getWitness withBlanks)).
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
    destruct H as [H | H].
    + epose proof h2 prefix _. assumption.
    + destruct H as [l' h3]. rewrite h3 in hPrefix.
      pose proof prefix_app_inv s1 l' ([BracketOpen] ++ s2 ++ [BracketClose] ++ s3) hPrefix as hPrefix2.
      pose proof prefixAppCases _ _ _ hPrefix2 as H1.
      destruct H1 as [H | H].
      * rewrite h3. autorewrite with rewriteCount.
        destruct (prefixSingleton _ _ H) as [H0 | H0].
        { rewrite H0. autorewrite with rewriteCount. rewrite ?Nat.add_0_r.
          epose proof h2 s1 _. assumption. }
        { rewrite H0. autorewrite with rewriteCount. epose proof h2 s1 _. lia. }
      * destruct H as [l0 H]. rewrite ?h3, ?H. autorewrite with rewriteCount.
        rewrite H in hPrefix2. pose proof prefix_app_inv _ _ _ hPrefix2 as H0.
        pose proof prefixAppCases _ _ _ H0 as H1. destruct H1 as [H1 | H1].
        { epose proof h2 (s1 ++ [BracketClose] ++ l0) _ as H2. autorewrite with rewriteCount in H2. lia. }
        { destruct H1 as [w H1]. rewrite H1 in H0. pose proof prefix_app_inv _ _ _ H0 as H2.
          pose proof prefixAppCases _ _ _ H2 as H3.
          destruct H3 as [H3 | H3].
          - destruct (prefixSingleton _ _ H3) as [H4 | H4].
            + rewrite H4 in H1. rewrite app_nil_r in H1. rewrite H1. epose proof h2 (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen]) _ as H6. autorewrite with rewriteCount in H6. lia.
            + rewrite H4 in H1. rewrite H1. autorewrite with rewriteCount. epose proof h2 (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen]) _ as H5. autorewrite with rewriteCount in H5. lia.
          - destruct H3 as [w' H3]. rewrite H3 in H2. pose proof prefix_app_inv _ _ _ H2 as H4.
            epose proof h2 (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen] ++ w') _ as H5. autorewrite with rewriteCount in H5. rewrite H1, H3. autorewrite with rewriteCount. lia. }
  Unshelve.
  { destruct H as [w H]. exists (w ++ [BracketClose] ++ s2 ++ [BracketOpen] ++ s3). rewrite H. listsEqual. }
  { exists ([BracketClose] ++ s2 ++ [BracketOpen] ++ s3). reflexivity. }
  { exists ([BracketClose] ++ s2 ++ [BracketOpen] ++ s3). reflexivity. }
  { destruct H1 as [w H1]. exists (w ++ [BracketOpen] ++ s3). rewrite H1. listsEqual. }
  { exists s3. listsEqual. }
  { exists s3. listsEqual. }
  { destruct H4 as [w1 H4]. exists w1. rewrite H4. listsEqual. }
Qed.

(* Paolo: I use a notation to avoid having to unfold this. *)
Notation right_len withBlanks s :=
  (count_occ optionBracketEqualityDecidable withBlanks None = length s) (only parsing).

Definition satisfactoryWitness (withBlanks : list (option Bracket)) (witness : list Bracket) :=
  right_len withBlanks witness /\
  isBalanced (fill withBlanks witness).

Lemma fillPreservesLength (withBlanks : list (option Bracket)) (witness : list Bracket) (h : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : length (fill withBlanks witness) = length withBlanks.
Proof.
  revert witness h. induction withBlanks as [| a withBlanks IHwithBlanks]; intros witness h.
  - easy.
  - destruct a; simpl.
    + simpl in h. rewrite (IHwithBlanks _ h). reflexivity.
    + destruct witness.
      * simpl in h. lia.
      * simpl. simpl in h. rewrite IHwithBlanks; lia.
Qed.

Section helpers.
  Implicit Type (s : list Bracket).

  Lemma fill_split {b s1 s2 withBlanks} :
    let s := s1 ++ [b] ++ s2 in
    right_len withBlanks s ->
    ∃ wb1 wb2,
      withBlanks = wb1 ++ [None] ++ wb2 /\
      right_len wb1 s1 /\
      right_len wb2 s2.
  Proof.
    simpl; rewrite !app_length; simpl; rewrite Nat.add_succ_r; simpl; clear b.
    induction withBlanks as [|[b'|] wb IHwb] in s1, s2 |- *; intros HL; simplify_eq/=. {
      destruct (IHwb s1 s2 HL) as (wb1 & wb2 & -> & ?); destruct_and!.
      by exists (Some b' :: wb1), wb2.
    }
    destruct s1 as [|b1 s1]; simplify_eq/=. { by exists [], wb. }
    destruct (IHwb s1 s2 HL) as (wb1 & wb2 & -> & ?); destruct_and!.
    by exists (None :: wb1), wb2; split_and!; simpl; try f_equiv.
  Qed.

  Lemma right_len_app w1 w2 s1 s2 :
    right_len w1 s1 ->
    right_len w2 s2 ->
    right_len (w1 ++ w2) (s1 ++ s2).
  Proof. rewrite count_occ_app, app_length. lia. Qed.

  Lemma fill_app w1 w2 s1 s2 :
    right_len w1 s1 ->
    right_len w2 s2 ->
    fill (w1 ++ w2) (s1 ++ s2) = fill w1 s1 ++ fill w2 s2.
  Proof.
    induction w1 as [|[b|] w1 IHw1] in s1, s2, w2 |- *; destruct s1 as [|b1 s1]; simpl in *;
      try (done || lia); intros H1 H2. {
      by rewrite <-(IHw1 w2 [] s2).
    }
    - by rewrite <-(IHw1 w2 (b1 :: s1) s2).
    - rewrite <-(IHw1 w2 s1 s2); try done; lia.
  Qed.
End helpers.

Lemma canAlwaysSwapCloseAndOpenInWitness (s1 s2 s3 : list Bracket) (withBlanks : list (option Bracket)) (hPrevious: satisfactoryWitness withBlanks (s1 ++ [BracketClose] ++ s2 ++ [BracketOpen] ++ s3)) : satisfactoryWitness withBlanks (s1 ++ [BracketOpen] ++ s2 ++ [BracketClose] ++ s3).
Proof.
  unfold satisfactoryWitness in *. destruct hPrevious as [HO HB].
  split.
  - rewrite HO, ?app_length. simpl. lia.
  - destruct (fill_split HO) as (wb1 & wb2' & -> & Hb1 & Hb2').
    destruct (fill_split Hb2') as (wb2 & wb3 & -> & Hb2 & Hb3); clear Hb2'.
    rewrite !fill_app in HB |- *; repeat apply right_len_app; simpl; try done.
    by apply canAlwaysSwapCloseAndOpen.
Qed.

Lemma addThreeTypes (withBlanks : list (option Bracket)) : count_occ optionBracketEqualityDecidable withBlanks None + count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) = length withBlanks.
Proof.
  induction withBlanks as [| a withBlanks].
  - easy.
  - destruct a as [b |].
    + destruct b; simpl; lia.
    + simpl. lia.
Qed.

Lemma subtractToCountNone (withBlanks : list (option Bracket)) : length withBlanks - (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)) = count_occ optionBracketEqualityDecidable withBlanks None.
Proof. pose proof addThreeTypes withBlanks. lia. Qed.

Lemma countSymbolAfterFill (withBlanks : list (option Bracket)) (toFill : list Bracket) (hValid : length toFill = count_occ optionBracketEqualityDecidable withBlanks None) (symbol : Bracket) : count_occ optionBracketEqualityDecidable withBlanks (Some symbol) + count_occ bracketEqualityDecidable toFill symbol = count_occ bracketEqualityDecidable (fill withBlanks toFill) symbol.
Proof.
  revert toFill hValid. induction withBlanks as [| a withBlanks IHwithBlanks]; intros toFill hValid.
  - simpl in *. rewrite (nil_length_inv _ hValid).
    easy.
  - destruct a as [b |].
    + destruct toFill as [| b0 toFill].
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
      destruct toFill as [| b toFill].
      * simpl in hValid. lia.
      * simpl in hValid.
        assert (hCases : b = symbol \/ b <> symbol). { destruct b; destruct symbol; try (left; easy); try (right; easy). }
        destruct hCases as [hCases | hCases].
        { rewrite ?hCases. simpl. destruct symbol; simpl; rewrite <- IHwithBlanks; simpl; lia. }
        { destruct symbol; simpl in hCases; try easy; simpl; destruct b; simpl; rewrite <- IHwithBlanks; simpl; lia. }
Qed.

Lemma existingLeqAfterFill (withBlanks : list (option Bracket)) (toFill : list Bracket) (hValid : length toFill = count_occ optionBracketEqualityDecidable withBlanks None) (symbol : Bracket) : count_occ optionBracketEqualityDecidable withBlanks (Some symbol) <= count_occ bracketEqualityDecidable (fill withBlanks toFill) symbol.
Proof.
  pose proof countSymbolAfterFill withBlanks toFill hValid symbol.
  lia.
Qed.

Lemma alwaysSortedAux (closeCount : nat) : sorted BracketOpen compareSymbols (repeat BracketClose closeCount).
Proof.
  intros i j hI hJ.
  pose proof nth_repeat BracketClose closeCount j as h1.
  pose proof nth_repeat BracketClose closeCount i as h2.
  erewrite (nth_indep _ BracketOpen BracketClose _), (nth_indep _ BracketOpen BracketClose _), h1, h2.
  easy.
  Unshelve.
  - lia.
  - lia.
Qed.

Lemma alwaysSorted (openCount closeCount : nat) : sorted BracketOpen (compare _ symbolComparator) (repeat BracketOpen openCount ++ repeat BracketClose closeCount).
Proof.
  induction openCount as [| openCount IHopenCount].
  - simpl. apply alwaysSortedAux.
  - simpl. intros i j hI hJ.
    destruct i as [| i]; destruct j as [| j]; try easy.
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
      pose proof fillPreservesLength withBlanks toFill hLength as hPreserve.
      pose proof isBalancedEvenLength _ hBalanced.
      rewrite hPreserve in *. tauto.
    Unshelve.
    case_bool_decide as enoughBlanks1.
    * shelve.
    * destruct hPossible as [toFill [hLength hBalanced]].
      destruct (isBalancedImpliesBalanceFactorBasedDefinition _ hBalanced) as [hCount _].
      pose proof fillPreservesLength withBlanks toFill hLength as hPreserve.
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
      pose proof fillPreservesLength withBlanks toFill hLength as hPreserve.
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
    pose proof selectionSortPermutation BracketOpen (compare _ symbolComparator) toFill as hPermutation1.
    assert (hSimplify : forall a : nat, (a + a) / 2 = a).
    { intro a.
      pose proof Nat.add_b2n_double_div2 false a.
      simpl in *. rewrite Nat.add_0_r in *. lia. }
    assert (hCountBalanced : forall x symbol, isBalanced x -> count_occ bracketEqualityDecidable x symbol = length x / 2).
    { intros x symbol h.
      destruct (isBalancedImpliesBalanceFactorBasedDefinition _ h) as [h1 h2].
      rewrite <- countOpenPlusCountClose, h1, hSimplify.
      destruct symbol; rewrite <- ?foldCountClose, <- ?foldCountOpen; lia. }
    assert (hPermutation2 : Permutation toFill (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)))).
    { rewrite (Permutation_count_occ bracketEqualityDecidable).
      intro x.
      rewrite count_occ_app.
      pose proof countSymbolAfterFill withBlanks toFill hLength x as H.
      destruct x; rewrite ?(@count_occ_repeat_neq Bracket bracketEqualityDecidable BracketOpen BracketClose), ?(@count_occ_repeat_neq Bracket bracketEqualityDecidable BracketClose BracketOpen), ?Nat.add_0_l, ?Nat.add_0_r; try easy; rewrite count_occ_repeat_eq; try reflexivity.
      - pose proof hCountBalanced (fill withBlanks toFill) BracketOpen ltac:(assumption) as H'.
        pose proof (fillPreservesLength withBlanks toFill ltac:(assumption)) as hRewrite.
        rewrite hRewrite in *. lia.
      - pose proof hCountBalanced (fill withBlanks toFill) BracketClose ltac:(assumption) as H'.
        pose proof (fillPreservesLength withBlanks toFill ltac:(assumption)) as hRewrite.
        rewrite hRewrite in *. lia. }
    symmetry in hPermutation2.
    pose proof (perm_trans hPermutation2 hPermutation1) as hPermutation.
    rewrite (sortedArraysEqual hPermutation hWitnessSorted ltac:(assumption) ltac:(intros a b; destruct a; destruct b; try (left; left; easy); try (left; right; easy); try (right; left; easy); try (right; right; easy); try (left; easy); try (right; easy))).
    epose proof propertyPreservedAfterSorting BracketOpen symbolComparator toFill (satisfactoryWitness withBlanks) _ _ as H.
    rewrite <- isBalancedIffIsBalancedBool.
    exact (proj2 H).
    Unshelve.
    { intros l1 l2 l3 a1 a2 h. destruct a1; destruct a2; try easy. apply canAlwaysSwapCloseAndOpenInWitness. }
    { split; [lia | assumption]. }
  - intro h. exists (getWitness withBlanks). split.
    + unfold getWitness. rewrite app_length, ?repeat_length.
      assert (H : length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)) = 2 * (length withBlanks / 2) - (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose))).
      { assert (H1 : length withBlanks / 2 >= count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)).
        { unfold possibleToFillBool in h; case_bool_decide; try case_bool_decide; easy. }
        assert (H2 : length withBlanks / 2 >= count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)).
        { unfold possibleToFillBool in h; case_bool_decide; try case_bool_decide; simpl in h; try case_bool_decide; easy. }
        lia. }
      assert (H1 : (2 * length withBlanks) / 2 = length withBlanks).
      { rewrite Nat.mul_comm. apply Nat.div_mul. easy. }
      rewrite H. rewrite <- (Lcm0.divide_div_mul_exact _ _ _).
      * rewrite H1. rewrite subtractToCountNone. reflexivity.
      * easy.
      * unfold possibleToFillBool in h.
        case_bool_decide; easy.
    + unfold possibleToFillBool in h.
      case_bool_decide.
      * case_bool_decide; try case_bool_decide; simpl in h; try rewrite <- isBalancedIffIsBalancedBool in h; easy.
      * easy.
Qed.

(* get a nice package of everything you'll ever need if you already have a witness *)
Lemma fromArbitraryWitness (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : isBalanced (fill withBlanks (getWitness withBlanks)) /\ (2 | length withBlanks) /\ (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) <= length withBlanks / 2) /\ (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) <= length withBlanks / 2) /\ length (getWitness withBlanks) = count_occ optionBracketEqualityDecidable withBlanks None.
Proof.
  pose proof proj1 (possibleToFillIffPossibleToFillBool withBlanks) (ex_intro _ witness (conj hCorrectLength hBalanced)) as h.
  unfold possibleToFillBool in h.
  case_bool_decide as hEven; try easy.
  repeat (case_bool_decide; try easy). simpl in h.
  rewrite <- isBalancedIffIsBalancedBool in h. intuition.
  unfold getWitness. destruct hEven as [w h']. rewrite app_length, ?repeat_length.
  pose proof addThreeTypes withBlanks.
  assert (hDiv : w * 2 / 2 = w). { now apply Nat.div_mul. } rewrite <- h' in hDiv. lia.
Qed.

Lemma fromArbitraryWitness_1 (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : isBalanced (fill withBlanks (getWitness withBlanks)).
Proof.
  pose proof fromArbitraryWitness withBlanks witness. intuition.
Qed.

Lemma fromArbitraryWitness_2 (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : (2 | length withBlanks).
Proof.
  pose proof fromArbitraryWitness withBlanks witness. intuition.
Qed.

Lemma fromArbitraryWitness_3 (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) <= length withBlanks / 2.
Proof.
  pose proof fromArbitraryWitness withBlanks witness. intuition.
Qed.

Lemma fromArbitraryWitness_4 (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) <= length withBlanks / 2.
Proof.
  pose proof fromArbitraryWitness withBlanks witness. intuition.
Qed.

Lemma fromArbitraryWitness_5 (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : length (getWitness withBlanks) = count_occ optionBracketEqualityDecidable withBlanks None.
Proof.
  pose proof fromArbitraryWitness withBlanks witness. intuition.
Qed.

Lemma fromArbitraryWitness_countOpen (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + count_occ bracketEqualityDecidable witness BracketOpen = length withBlanks / 2.
Proof.
  pose proof countOpenEqHalfLength (fill withBlanks witness) hBalanced as h.
  rewrite fillPreservesLength in h; try easy.
  rewrite <- h.
  induction withBlanks as [| [head |] tail IH] in hCorrectLength, witness |- *.
  - simpl in *. rewrite (nil_length_inv _ hCorrectLength). easy.
  - destruct head; simpl in *; rewrite ?countOpenConsOpen, ?countOpenConsClose, IH; try (lia || done).
  - destruct witness as [| head1 tail1]; simpl in *; try destruct head1; simpl in *; rewrite ?countOpenConsOpen, ?countOpenConsClose; try lia; pose proof IH tail1 ltac:(lia); lia.
Qed.

Lemma fromArbitraryWitness_countClose (withBlanks : list (option Bracket)) (witness : list Bracket) (hBalanced : isBalanced (fill withBlanks witness)) (hCorrectLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) + count_occ bracketEqualityDecidable witness BracketClose = length withBlanks / 2.
Proof.
  pose proof countCloseEqHalfLength (fill withBlanks witness) hBalanced as h.
  rewrite fillPreservesLength in h; try easy.
  rewrite <- h.
  induction withBlanks as [| [head |] tail IH] in hCorrectLength, witness |- *.
  - simpl in *. rewrite (nil_length_inv _ hCorrectLength). easy.
  - destruct head; simpl in *; rewrite ?countCloseConsOpen, ?countCloseConsClose, IH; try (done || lia).
  - destruct witness as [| head1 tail1]; simpl in *; try destruct head1; simpl in *; rewrite ?countCloseConsOpen, ?countCloseConsClose; try lia; pose proof IH tail1 ltac:(lia); lia.
Qed.
