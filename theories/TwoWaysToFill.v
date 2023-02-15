From CoqCP Require Import Options FillInTheBlanks Completion RegularBracketString SwapUpdate ListDecomposition.
From stdpp Require Import numbers list.

Definition getSecondWitness (withBlanks : list (option Bracket)) :=
  let count := length withBlanks / 2 in
  let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
  let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
  repeat BracketOpen (remainingOpenCount - 1) ++ [BracketClose; BracketOpen] ++ repeat BracketClose (remainingCloseCount - 1).

Lemma twoWaysToFillAux (withBlanks : list (option Bracket)) (witness : list Bracket) (hDiff : getWitness withBlanks <> witness) hRightLength (hWitnessValid : isBalanced (fill withBlanks witness hRightLength)) : isBalanced (fillLax withBlanks (getSecondWitness withBlanks)).
Proof.
  destruct (possibleToFillIffPossibleToFillBool withBlanks) as [H _].
  rewrite possibleToFillIffPossibleToFill2 in H.
  epose proof H _ as H'.
  unfold possibleToFillBool in H'.
  case_bool_decide as condition1; try easy.
  case_bool_decide as condition2; try easy.
  case_bool_decide as condition3; try easy.
  simpl in H'.
  rewrite <- isBalancedIffIsBalancedBool in H'.
  assert (hLength : length (getWitness withBlanks) = length witness).
  { unfold getWitness. rewrite ?app_length, ?repeat_length, hRightLength.
    pose proof addThreeTypes withBlanks.
    destruct condition1 as [w h].
    assert (length withBlanks / 2 = w). { now rewrite h, Nat.div_mul. }
    lia. }
  destruct (oneDifferentPlace (getWitness withBlanks) witness BracketOpen hDiff hLength) as [w [h1 h2]].
  destruct (decide (w < length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) as [hLeft | hLeft].
  - assert (hSymbol : nth w (getWitness withBlanks) BracketOpen = BracketOpen).
    { unfold getWitness.
      pose proof nthTake (repeat BracketOpen (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) ++ repeat BracketClose (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose))) BracketOpen w _ hLeft as hSimplify.
      pose proof take_app (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) as hPartial.
      rewrite repeat_length in hPartial.
      rewrite hPartial in hSimplify.
      rewrite hSimplify.
      now rewrite nth_repeat. }
    assert (hSymbol2 : nth w witness BracketOpen = BracketClose).
    { destruct (nth w (getWitness _) _); destruct (nth w witness _); easy. }
    assert (hDecompose : witness = take w witness ++ [BracketClose] ++ drop (S w) witness).
    { pose proof listDecompositionSingle witness w ltac:(lia) BracketOpen.
      now rewrite <- hSymbol2. }
    remember (<[getKthBlank withBlanks w := Some BracketClose]> withBlanks) as injected eqn:hInjected.
    admit.
  - assert (hSymbol : nth w (getWitness withBlanks) BracketOpen = BracketClose).
    { rewrite (nth_indep _ BracketOpen BracketClose h1). unfold getWitness.
      assert (hLengthRepeat : length (repeat BracketOpen (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) = length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)). { now rewrite repeat_length. }
      assert (hDelta : w = length (repeat BracketOpen (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) + (w - (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)))). { lia. }
      now rewrite hDelta, nthApp, nth_repeat. }
    assert (hSymbol2 : nth w witness BracketOpen = BracketOpen).
    { destruct (nth w (getWitness _) _); destruct (nth w witness _); easy. }
    assert (hDecompose : witness = take w witness ++ [BracketOpen] ++ drop (S w) witness).
    { pose proof listDecompositionSingle witness w ltac:(lia) BracketOpen.
      now rewrite <- hSymbol2. }
    remember (<[getKthBlank withBlanks w := Some BracketOpen]> withBlanks) as injected eqn:hInjected.
    admit.
  Unshelve.
  exists (fill withBlanks witness hRightLength).
  pose proof fillIsCompletion withBlanks witness hRightLength.
  tauto.
Admitted.

Lemma twoWaysToFill (withBlanks : list (option Bracket)) (witness1 witness2 : list Bracket) (hDiff : witness1 <> witness2) hRightLength1 hRightLength2 (hWitness1Valid : isBalanced (fill withBlanks witness1 hRightLength1)) (hWitness2Valid : isBalanced (fill withBlanks witness2 hRightLength2)) : isBalanced (fillLax withBlanks (getSecondWitness withBlanks)).
Proof.
  remember (bool_decide (witness1 = getWitness withBlanks)) as split eqn:hSplit.
  destruct split; symmetry in hSplit; rewrite <- ?Is_true_true, <- ?Is_true_false, bool_decide_spec in hSplit.
  - refine (twoWaysToFillAux withBlanks witness2 _ hRightLength2 _); try (congruence || done).
  - refine (twoWaysToFillAux withBlanks witness1 _ hRightLength1 _); try (congruence || done).
Qed.
