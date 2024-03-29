From CoqCP Require Import Options FillInTheBlanks Completion RegularBracketString SwapUpdate ListDecomposition ListsEqual PrefixApp.
From stdpp Require Import numbers list.

Definition getSecondWitness (withBlanks : list (option Bracket)) :=
  let count := length withBlanks / 2 in
  let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
  let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
  repeat BracketOpen (remainingOpenCount - 1) ++ [BracketClose; BracketOpen] ++ repeat BracketClose (remainingCloseCount - 1).

Lemma twoWaysToFillCountOccBounds (withBlanks : list (option Bracket)) (witness1 witness2 : list Bracket) (hDiff : witness1 <> witness2) (hRightLength1 : length witness1 = count_occ optionBracketEqualityDecidable withBlanks None) (hRightLength2 : length witness2 = count_occ optionBracketEqualityDecidable withBlanks None) (hValid1 : isBalanced (fill withBlanks witness1)) (hValid2 : isBalanced (fill withBlanks witness2)) : count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) < length withBlanks / 2 /\ count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) < length withBlanks / 2.
Proof.
  pose proof fromArbitraryWitness_3 withBlanks witness1 ltac:(assumption) ltac:(assumption).
  pose proof fromArbitraryWitness_4 withBlanks witness1 ltac:(assumption) ltac:(assumption).
  pose proof addThreeTypes withBlanks as hTotal.
  assert (hSumWitness : forall (witness : list Bracket), count_occ bracketEqualityDecidable witness BracketOpen + count_occ bracketEqualityDecidable witness BracketClose = length witness).
  { intro witness. induction witness as [| head tail IH].
    - easy.
    - destruct head; simpl; lia. }
  split.
  - destruct (decide (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) = length withBlanks / 2)) as [hContrary |]; try lia.
    pose proof fromArbitraryWitness_countOpen withBlanks witness1 ltac:(assumption) ltac:(assumption).
    pose proof fromArbitraryWitness_countOpen withBlanks witness2 ltac:(assumption) ltac:(assumption).
    pose proof (ltac:(lia) : count_occ bracketEqualityDecidable witness1 BracketOpen = 0) as h1.
    pose proof (ltac:(lia) : count_occ bracketEqualityDecidable witness2 BracketOpen = 0) as h2.
    pose proof (ltac:(lia) : length witness1 = length witness2) as hSameLength.
    assert (hEqual : witness1 = witness2).
    { induction witness1 as [| head tail IH] in h1, h2, witness2, hSameLength |- *.
      - simpl in hSameLength. symmetry in hSameLength. now pose proof nil_length_inv _ hSameLength.
      - destruct witness2 as [| head' tail']; try (simpl in *; easy). rewrite (IH tail'); try (destruct head; destruct head'; simpl in *; try destruct (decide _ _); try lia; try easy). }
    easy.
  - destruct (decide (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) = length withBlanks / 2)) as [hContrary |]; try lia.
    pose proof fromArbitraryWitness_countClose withBlanks witness1 ltac:(assumption) ltac:(assumption).
    pose proof fromArbitraryWitness_countClose withBlanks witness2 ltac:(assumption) ltac:(assumption).
    pose proof (ltac:(lia) : count_occ bracketEqualityDecidable witness1 BracketClose = 0) as h1.
    pose proof (ltac:(lia) : count_occ bracketEqualityDecidable witness2 BracketClose = 0) as h2.
    pose proof (ltac:(lia) : length witness1 = length witness2) as hSameLength.
    assert (hEqual : witness1 = witness2).
    { induction witness1 as [| head tail IH] in h1, h2, witness2, hSameLength |- *.
      - simpl in hSameLength. symmetry in hSameLength. now pose proof nil_length_inv _ hSameLength.
      - destruct witness2 as [| head' tail']; try (simpl in *; easy). rewrite (IH tail'); try (destruct head; destruct head'; simpl in *; try destruct (decide _ _); try lia; try easy). }
    easy.
Qed.

Lemma twoWaysToFillAux_differenceOnLeftSegment (withBlanks : list (option Bracket)) (witness : list Bracket) (position : nat) (hPosition : position < length (getWitness withBlanks)) (hSplit : position < length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) (hNth : nth position (getWitness withBlanks) BracketOpen <> nth position witness BracketOpen) (hRightLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) (hWitnessValid : isBalanced (fill withBlanks witness)) : isBalanced (fill withBlanks (getSecondWitness withBlanks)).
Proof.
  assert (hDiff : getWitness withBlanks <> witness).
  { remember (getWitness withBlanks) as witness'.
    destruct witness as [| head tail]; intro hContrary.
    - rewrite hContrary in hPosition. simpl in *. lia.
    - destruct witness' as [| head' tail']; try (simpl in *; lia).
      destruct position as [| position]; simpl in *; inversion hContrary; congruence. }
  assert (hLt : position < length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) -> nth position (getWitness withBlanks) BracketOpen = BracketOpen /\ nth position witness BracketOpen = BracketClose).
  { intro h. unfold getWitness in *. rewrite nthAppLt in *; try (rewrite repeat_length in *; lia).
  rewrite nth_repeat in *. destruct (nth position witness BracketOpen); intuition. }
  destruct (hLt ltac:(lia)) as [hNthGetWitness hNthWitness].
  destruct (fromArbitraryWitness withBlanks witness hWitnessValid hRightLength) as [hGetWitness [hEven [hCountLt1 [hCountLt2 hLengthGetWitness]]]].
  pose proof twoWaysToFillCountOccBounds withBlanks witness (getWitness withBlanks) ltac:(congruence) ltac:(assumption) ltac:(lia) ltac:(assumption) ltac:(assumption).
  pose proof updateKthPartialCompletion withBlanks position ltac:(lia) BracketClose as hPartial.
  pose proof listDecompositionSingle withBlanks (getKthBlank withBlanks position) ltac:(apply getKthBlankUpperBound; lia) None as hDecomp.
  assert (hPartial' : isPartialCompletion withBlanks (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) withBlanks)).
  { rewrite (ltac:(now rewrite <- hDecomp) : <[getKthBlank withBlanks position := Some BracketClose]> withBlanks = <[getKthBlank withBlanks position := Some BracketClose]> (take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None] ++ drop (S (getKthBlank withBlanks position)) withBlanks)) in hPartial.
    pose proof updateAppZero (take (getKthBlank withBlanks position) withBlanks) ([nth (getKthBlank withBlanks position) withBlanks None] ++ drop (S (getKthBlank withBlanks position)) withBlanks) (Some BracketClose) as hAux. rewrite take_length, (ltac:(pose proof getKthBlankUpperBound withBlanks position ltac:(lia); lia) : getKthBlank withBlanks position `min` length withBlanks = getKthBlank withBlanks position) in hAux. simpl in *. intuition congruence. }
  assert (hCanComplete : possibleToFill (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) withBlanks)).
  { exists (take position witness ++ drop (S position) witness). split.
    - rewrite app_length, !count_occ_app, takeKthBlankCountOcc, dropSuccKthBlankCountOcc, <- hRightLength, take_length, drop_length, (ltac:(lia) : position `min` length witness = position); try lia.
      simpl. lia.
    - rewrite (fillApp (take (getKthBlank withBlanks position) withBlanks) ([Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) withBlanks) (take position witness) (drop (S position) witness) ltac:(rewrite takeKthBlankCountOcc; rewrite ?take_length; lia) ltac:(rewrite count_occ_app, dropSuccKthBlankCountOcc, drop_length, <- hRightLength; simpl; lia)).
      pose proof fillApp [Some BracketClose] (drop (S (getKthBlank withBlanks position)) withBlanks) [] (drop (S position) witness) ltac:(now simpl) ltac:(rewrite dropSuccKthBlankCountOcc, drop_length, <- hRightLength; lia) as hIntermediate.
      rewrite app_nil_l in hIntermediate. rewrite hIntermediate. rewrite (ltac:(easy) : fill [Some BracketClose] [] = fill [None] [BracketClose]).
      rewrite <- (fillApp [None] (drop (S (getKthBlank withBlanks position)) withBlanks) [BracketClose] (drop (S position) witness) ltac:(easy) ltac:(rewrite dropSuccKthBlankCountOcc, drop_length, <- hRightLength; lia)).
      rewrite <- (fillApp (take (getKthBlank withBlanks position) withBlanks) ([None] ++ drop (S (getKthBlank withBlanks position)) withBlanks) (take position witness) ([BracketClose] ++ drop (S position) witness) ltac:(rewrite takeKthBlankCountOcc, take_length; lia) ltac:(rewrite app_length, drop_length, count_occ_app, dropSuccKthBlankCountOcc; simpl; lia)).
      rewrite <- (nthGetKthBlank withBlanks position None), <- hDecomp, <- hNthWitness, <- listDecompositionSingle; try lia. tauto. }
  destruct hCanComplete as [answers2 [hAnswers2a hAnswers2b]].
  pose proof fromArbitraryWitness_1 (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) withBlanks) answers2 ltac:(tauto) ltac:(tauto) as hIntermediate.
  unfold getWitness in hIntermediate.
  rewrite !app_length, take_length, (ltac:(pose proof getKthBlankUpperBound withBlanks position; lia) : getKthBlank withBlanks position `min` length withBlanks = getKthBlank withBlanks position), drop_length, (ltac:(intros; easy) : forall A (x : A), length [x] = 1), !count_occ_app, (ltac:(intro x; destruct x as [[|] |]; try easy) : forall x, count_occ optionBracketEqualityDecidable [x] x = 1), (ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] (Some BracketOpen) = 0) in hIntermediate.
  rewrite (ltac:(pose proof getKthBlankUpperBound withBlanks position; lia) : (getKthBlank withBlanks position + (1 + (length withBlanks - S (getKthBlank withBlanks position)))) = length withBlanks) in hIntermediate.
  assert (hCountOpen : count_occ optionBracketEqualityDecidable (take (getKthBlank withBlanks position) withBlanks) (Some BracketOpen) + (0 + count_occ optionBracketEqualityDecidable (drop (S (getKthBlank withBlanks position)) withBlanks) (Some BracketOpen)) = count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)).
  { pose proof nthGetKthBlank withBlanks position None ltac:(lia) as hStep.
    pose proof getKthBlankUpperBound withBlanks position.
    rewrite (ltac:(now rewrite hStep) : 0 = count_occ optionBracketEqualityDecidable [nth (getKthBlank withBlanks position) withBlanks None] (Some BracketOpen)), <- !count_occ_app, <- listDecompositionSingle; (done || lia). }
  rewrite hCountOpen in hIntermediate. clear hCountOpen.
  assert (hCountClose : count_occ optionBracketEqualityDecidable (take (getKthBlank withBlanks position) withBlanks) (Some BracketClose) + (1 + count_occ optionBracketEqualityDecidable (drop (S (getKthBlank withBlanks position)) withBlanks) (Some BracketClose)) = S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose))).
  { pose proof nthGetKthBlank withBlanks position None ltac:(lia) as hStep.
    pose proof getKthBlankUpperBound withBlanks position.
    rewrite (ltac:(now rewrite hStep) : 0 = count_occ optionBracketEqualityDecidable [nth (getKthBlank withBlanks position) withBlanks None] (Some BracketClose)), Nat.add_succ_l, Nat.add_succ_r, <- !count_occ_app, <- listDecompositionSingle; (done || lia). }
  rewrite hCountClose in hIntermediate. clear hCountClose.
  pose proof fillApp (take (getKthBlank withBlanks position) withBlanks) ([Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) withBlanks) (repeat BracketOpen position) (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)))) ltac:(rewrite repeat_length, takeKthBlankCountOcc; lia) ltac:(rewrite !app_length, !repeat_length, !count_occ_app, dropSuccKthBlankCountOcc, (ltac:(intros; reflexivity) : count_occ optionBracketEqualityDecidable [Some BracketClose] None = 0); destruct hEven as [w hEven]; pose proof (ltac:(apply Nat.div_mul; easy) : w * 2 / 2 = w) as hDiv; pose proof addThreeTypes withBlanks as hAdd; rewrite <- hEven in hDiv; lia) as hStep.
  rewrite (ltac:(intros; listsEqual) : forall a b, repeat BracketOpen position ++ repeat BracketOpen a ++ repeat BracketClose b = (repeat BracketOpen position ++ repeat BracketOpen a) ++ repeat BracketClose b), <- repeat_app, (ltac:(lia) : position + (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) in hStep.
  rewrite hStep in hIntermediate. clear hStep.
  pose proof fillApp [Some BracketClose] (drop (S (getKthBlank withBlanks position)) withBlanks) [] (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)))) ltac:(easy) ltac:(rewrite !app_length, !repeat_length, dropSuccKthBlankCountOcc; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia) as hStep.
  rewrite app_nil_l in hStep. rewrite hStep, (ltac:(easy) : fill [Some BracketClose] [] = fill [None] [BracketClose]), <- fillApp in hIntermediate; try (simpl in *; easy); try (rewrite !app_length, !repeat_length, dropSuccKthBlankCountOcc; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia). clear hStep.
  rewrite <- fillApp in hIntermediate; try (rewrite repeat_length, takeKthBlankCountOcc; lia); try (rewrite !app_length, !repeat_length, count_occ_app, (ltac:(easy) : count_occ optionBracketEqualityDecidable [None] None = 1), dropSuccKthBlankCountOcc, !(ltac:(easy) : length [BracketClose] = 1); pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia).
  rewrite <- (nthGetKthBlank withBlanks position None), <- listDecompositionSingle in hIntermediate; try (pose proof getKthBlankUpperBound withBlanks position; lia).
  remember (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)))) as x eqn:hX.
  assert (hLeft : nth position x BracketOpen = BracketClose).
  { subst x.
    assert (hStep : forall x, nth position x BracketOpen = nth (length (repeat BracketOpen position)) x BracketOpen). { intros. now rewrite repeat_length. }
    now rewrite hStep, nthAppZero. }
  assert (hRight : nth (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) x BracketOpen = BracketOpen).
  { subst x.
    assert (hRebracket' : (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1)) ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose))) = repeat BracketOpen position ++ [BracketClose] ++ (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1) ++ [BracketOpen]) ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)))). { listsEqual. }
    assert (hArith : (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) = S (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1)). { lia. }
    assert (hRepeat : repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) = repeat BracketOpen (S (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1))). { auto. }
    assert (hRebracket : repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position) ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose))) = (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1)) ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - S (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose)))).
    { now rewrite hRebracket', <- repeat_cons, hRepeat. }
    rewrite hRebracket.
    assert (hLength : length (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1)) = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)).
    { rewrite !app_length, !repeat_length, (ltac:(easy) : length [BracketClose] = 1). lia. }
    assert (hRewrite : forall x, nth (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) x BracketOpen = nth (length (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - position - 1))) x BracketOpen). { congruence. }
    rewrite hRewrite, nthAppZero. easy. }
  assert (hLength : length x = length witness).
  { subst x. rewrite !app_length, !repeat_length, (ltac:(easy) : length [BracketClose] = 1); pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia. }
  rewrite (listDecompositionSingle x (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) ltac:(pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia) BracketOpen) in hIntermediate.
  rewrite (listDecompositionSingle (take (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) x) position ltac:(rewrite take_length; lia) BracketOpen), take_take in hIntermediate.
  rewrite (ltac:(lia) : position `min` (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) = position), hRight in hIntermediate.
  pose proof nthAppLt BracketOpen (take (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) x) (drop (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) x) position ltac:(rewrite take_length; lia) as hExtend.
  rewrite take_drop in hExtend.
  rewrite <- hExtend, hLeft in hIntermediate.
  pose proof listDecomposition withBlanks (getKthBlank withBlanks position) (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) ltac:(apply getKthBlankLt; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia) ltac:(apply getKthBlankUpperBound; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia) None as hDecomp'.
  assert (hFillWithBlanks : forall stuff, fill withBlanks stuff = fill (take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None] ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks) ++ [nth (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks None] ++ drop (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 1) withBlanks) stuff). { now rewrite <- hDecomp'. }
  rewrite hFillWithBlanks in hIntermediate. clear hFillWithBlanks hDecomp'.
  rewrite !nthGetKthBlank in hIntermediate; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia).
  rewrite <- !app_assoc, !fillApp in hIntermediate; try (simpl in *; lia); try (rewrite ?drop_length, ?take_length, ?app_length, ?count_occ_app, ?takeKthBlankCountOcc, ?Nat.add_1_r, ?dropSuccKthBlankCountOcc); try lia; try (rewrite ?(ltac:(easy) : length [BracketOpen] = 1), ?(ltac:(easy) : length [BracketClose] = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [None] None = 1)); try (rewrite ?drop_length, ?take_length); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia).
  rewrite !(ltac:(easy) : forall x : Bracket, fill [None] [x] = fill [Some x] []), <- !fillApp in hIntermediate; try (simpl in *; lia); try (rewrite ?drop_length, ?take_length, ?app_length, ?(ltac:(easy) : length ([] : list Bracket) = 0), ?count_occ_app, ?takeKthBlankCountOcc, ?Nat.add_1_r, ?dropSuccKthBlankCountOcc); try lia; try (rewrite ?(ltac:(easy) : length [BracketOpen] = 1), ?(ltac:(easy) : length [BracketClose] = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [None] None = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketOpen] None = 0), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] None = 0)); try (rewrite ?drop_length, ?take_length); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia).
  pose proof fromArbitraryWitness_1 (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks) ++ [Some BracketOpen] ++ drop (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 1) withBlanks) (take position x ++ [] ++ drop (S position) (take (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) x) ++ [] ++ drop (S (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) x) ltac:(assumption) ltac:(try (simpl in *; lia); try (rewrite ?drop_length, ?take_length, ?app_length, ?(ltac:(easy) : length ([] : list Bracket) = 0), ?count_occ_app, ?takeKthBlankCountOcc, ?Nat.add_1_r, ?dropSuccKthBlankCountOcc); try lia; try (rewrite ?(ltac:(easy) : length [BracketOpen] = 1), ?(ltac:(easy) : length [BracketClose] = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [None] None = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketOpen] None = 0), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] None = 0)); try (rewrite ?drop_length, ?take_length); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) as hAlmostDone.
  unfold getWitness in hAlmostDone.
  assert (hImpenetrable1 : count_occ optionBracketEqualityDecidable (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks) ++ [Some BracketOpen] ++ drop (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 1) withBlanks) (Some BracketOpen) = count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + 1).
  { rewrite ?count_occ_app, (ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] (Some BracketOpen) = count_occ optionBracketEqualityDecidable [None] (Some BracketOpen)), (ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketOpen] (Some BracketOpen) = S (count_occ optionBracketEqualityDecidable [None] (Some BracketOpen))).
    pose proof nthGetKthBlank withBlanks position None ltac:(lia).
    pose proof nthGetKthBlank withBlanks (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) None ltac:(try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) as hAnotherBlank.
    rewrite !Nat.add_assoc, !Nat.add_succ_r, <- !count_occ_app, (ltac:(congruence) : (take (getKthBlank withBlanks position) withBlanks ++ [None]) = (take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None])), (ltac:(congruence) : S (count_occ optionBracketEqualityDecidable (((take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None]) ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks)) ++ [None]) (Some BracketOpen)) + count_occ optionBracketEqualityDecidable (drop (S (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 0)) withBlanks)  (Some BracketOpen) = S (count_occ optionBracketEqualityDecidable (((take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None]) ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks)) ++ [nth (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks None]) (Some BracketOpen)) + count_occ optionBracketEqualityDecidable (drop (S (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 0)) withBlanks) (Some BracketOpen)), <- !app_assoc, Nat.add_0_r.
    pose proof listDecomposition_rhsSucc withBlanks (getKthBlank withBlanks position) (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) ltac:(apply getKthBlankLt; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) ltac:(pose proof getKthBlankUpperBound withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) None as hFold. rewrite Nat.add_succ_l, <- count_occ_app, <- !app_assoc, <- hFold. lia. }
  rewrite hImpenetrable1 in hAlmostDone.
  assert (hImpenetrable2 : count_occ optionBracketEqualityDecidable (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks) ++ [Some BracketOpen] ++ drop (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 1) withBlanks) (Some BracketClose) = count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) + 1).
  { rewrite ?count_occ_app, (ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketOpen] (Some BracketClose) = count_occ optionBracketEqualityDecidable [None] (Some BracketClose)), (ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] (Some BracketClose) = S (count_occ optionBracketEqualityDecidable [None] (Some BracketClose))).
    pose proof nthGetKthBlank withBlanks position None ltac:(lia).
    pose proof nthGetKthBlank withBlanks (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) None ltac:(try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) as hAnotherBlank.
    rewrite !Nat.add_assoc, !Nat.add_succ_r, <- !count_occ_app, (ltac:(congruence) : (take (getKthBlank withBlanks position) withBlanks ++ [None]) = (take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None])), (ltac:(congruence) : count_occ optionBracketEqualityDecidable [None] (Some BracketClose) = count_occ optionBracketEqualityDecidable [nth (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks None] (Some BracketClose)), !Nat.add_succ_l, <- !count_occ_app, <- !app_assoc, !Nat.add_0_r.
    pose proof listDecomposition_rhsSucc withBlanks (getKthBlank withBlanks position) (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) ltac:(apply getKthBlankLt; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) ltac:(pose proof getKthBlankUpperBound withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) None as hFold. rewrite <- hFold. lia. }
  rewrite hImpenetrable2 in hAlmostDone.
  assert (hUnwieldy1: (length (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks) ++ [Some BracketOpen] ++ drop (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 1) withBlanks) / 2 - (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) + 1)) = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1).
  { rewrite !app_length, (ltac:(easy) : length [Some BracketClose] = length [nth (getKthBlank withBlanks position) withBlanks None]), (ltac:(easy) : length [Some BracketOpen] = length [nth (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks None]), <- !app_length, <- listDecomposition; try (pose proof getKthBlankUpperBound withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try apply getKthBlankLt; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia). }
  rewrite hUnwieldy1 in hAlmostDone.
  assert (hUnwieldy2 : (length (take (getKthBlank withBlanks position) withBlanks ++ [Some BracketClose] ++ drop (S (getKthBlank withBlanks position)) (take (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks) ++ [Some BracketOpen] ++ drop (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) + 1) withBlanks) / 2 - (count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) + 1)) = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1).
  { rewrite !app_length, (ltac:(easy) : length [Some BracketClose] = length [nth (getKthBlank withBlanks position) withBlanks None]), (ltac:(easy) : length [Some BracketOpen] = length [nth (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks None]), <- !app_length, <- listDecomposition; try (pose proof getKthBlankUpperBound withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try apply getKthBlankLt; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia). }
  rewrite hUnwieldy2 in hAlmostDone.
  rewrite (ltac:(rewrite app_nil_l, <- repeat_app; apply (ltac:(congruence) : forall a b, a = b -> repeat BracketOpen a = repeat BracketOpen b); lia) : repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1) = repeat BracketOpen position ++ [] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1 - position)), (ltac:(easy) : repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1) = [] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1)), <- !app_assoc, !fillApp in hAlmostDone; try (simpl in *; lia); try (rewrite ?drop_length, ?take_length, ?app_length, ?repeat_length, ?(ltac:(easy) : length ([] : list Bracket) = 0), ?count_occ_app, ?takeKthBlankCountOcc, ?Nat.add_1_r, ?dropSuccKthBlankCountOcc); try lia; try (rewrite ?(ltac:(easy) : length [BracketOpen] = 1), ?(ltac:(easy) : length [BracketClose] = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [None] None = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketOpen] None = 0), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] None = 0)); try (rewrite ?drop_length, ?take_length); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia).
  rewrite <- !(ltac:(easy) : forall x : Bracket, fill [None] [x] = fill [Some x] []), <- !fillApp in hAlmostDone; try (simpl in *; lia); try (rewrite ?drop_length, ?take_length, ?app_length, ?repeat_length, ?(ltac:(easy) : length ([] : list Bracket) = 0), ?count_occ_app, ?takeKthBlankCountOcc, ?Nat.add_1_r, ?dropSuccKthBlankCountOcc); try lia; try (rewrite ?(ltac:(easy) : length [BracketOpen] = 1), ?(ltac:(easy) : length [BracketClose] = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [None] None = 1), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketOpen] None = 0), ?(ltac:(easy) : count_occ optionBracketEqualityDecidable [Some BracketClose] None = 0)); try (rewrite ?drop_length, ?take_length); try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia).
  pose proof nthGetKthBlank withBlanks position None ltac:(lia).
  pose proof nthGetKthBlank withBlanks (length withBlanks `div` 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen)) None ltac:(try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia); rewrite ?dropSuccTakeKthBlankCountOcc; try (pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; lia)) as hAnotherBlank.
  rewrite app_assoc, (ltac:(congruence) : (take (getKthBlank withBlanks position) withBlanks ++ [None]) = (take (getKthBlank withBlanks position) withBlanks ++ [nth (getKthBlank withBlanks position) withBlanks None])), (ltac:(congruence) : [None] = [nth (getKthBlank withBlanks (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) withBlanks None]), <- !app_assoc, <- listDecomposition in hAlmostDone; try apply getKthBlankLt; pose proof addThreeTypes withBlanks; destruct hEven as [w hEven]; pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv; rewrite <- hEven in hDiv; try apply getKthBlankUpperBound; try lia.
  destruct (decide (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1 - position = 0)) as [hMiddle | hMiddle]; unfold getSecondWitness.
  - now rewrite hMiddle, (ltac:(lia) : position = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1) in *.
  - pose proof canAlwaysSwapCloseAndOpenInWitness (repeat BracketOpen position) (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position)) ([BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1)) withBlanks as hSwap.
    assert (hRewriteHyp : (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position) ++ [BracketOpen] ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1)) = (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1 - position) ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1))).
    { now rewrite (ltac:(listsEqual) : (repeat BracketOpen position ++ [BracketClose] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position) ++ [BracketOpen] ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1)) = (repeat BracketOpen position ++ [BracketClose] ++ (repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position) ++ [BracketOpen]) ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1))), (ltac:(easy) : [BracketOpen] = repeat BracketOpen 1), <- repeat_app, (ltac:(lia) : length withBlanks / 2 -
    count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position + 1 = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1 - position). }
    rewrite hRewriteHyp in hSwap.
    assert (hMassage : repeat BracketOpen position ++ [BracketOpen] ++ repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position) ++ [BracketClose] ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1) = repeat BracketOpen (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1) ++ [BracketClose] ++ [BracketOpen] ++ repeat BracketClose (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) - 1)).
    { now rewrite !app_assoc, (ltac:(now rewrite <- repeat_cons) : repeat BracketOpen position ++ [BracketOpen] = repeat BracketOpen (S position)), <- repeat_app, <- !app_assoc, (ltac:(lia) : S position + (length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 2 - position) = length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) - 1). }
    rewrite hMassage in hSwap.
    unfold satisfactoryWitness in *. epose proof hSwap _. easy.
    Unshelve.
    intuition. rewrite !app_length, !repeat_length, !(ltac:(easy) : forall x : Bracket, length [x] = 1). lia.
Qed.

Fixpoint mirror (s : list Bracket) := match s with
  | [] => []
  | (BracketOpen :: tail) => mirror tail ++ [BracketClose]
  | (BracketClose :: tail) => mirror tail ++ [BracketOpen]
  end.

Fixpoint mirrorWithBlanks (s : list (option Bracket)) := match s with
  | [] => []
  | (Some BracketOpen :: tail) => mirrorWithBlanks tail ++ [Some BracketClose]
  | (Some BracketClose :: tail) => mirrorWithBlanks tail ++ [Some BracketOpen]
  | (None :: tail) => mirrorWithBlanks tail ++ [None]
  end.

Lemma mirrorPreservesLength s : length (mirror s) = length s.
Proof.
  induction s as [| [|] tail IH]; try easy; simpl in *; rewrite app_length, IH; simpl; lia.
Qed.

Lemma mirrorWithBlanksPreservesLength s : length (mirrorWithBlanks s) = length s.
Proof.
  induction s as [| [[|]|] tail IH]; try easy; simpl in *; rewrite app_length, IH; simpl; lia.
Qed.

Lemma mirrorCountOpen (s : list Bracket) : countOpen (mirror s) = countClose s.
Proof.
  induction s as [| [|] tail IH]; simpl in *; autorewrite with rewriteCount; lia.
Qed.

Lemma mirrorCountClose (s : list Bracket) : countClose (mirror s) = countOpen s.
Proof.
  induction s as [| [|] tail IH]; simpl in *; autorewrite with rewriteCount; lia.
Qed.

Lemma mirrorOpenCountEqualCloseCount (s : list Bracket) (h : countOpen s = countClose s) : countOpen (mirror s) = countClose (mirror s).
Proof.
  pose (mirrorCountOpen s).
  pose (mirrorCountClose s).
  congruence.
Qed.

Lemma mirrorApp s1 s2 : mirror (s1 ++ s2) = mirror s2 ++ mirror s1.
Proof.
  induction s1 as [| head tail IH].
  - simpl. now rewrite app_nil_r.
  - rewrite <- app_comm_cons. destruct head; simpl; now rewrite IH, <- !app_assoc.
Qed.

Lemma mirrorStillBalanced (s : list Bracket) (hBalanced : isBalanced s) : isBalanced (mirror s).
Proof.
  induction hBalanced as [| s IH |].
  - apply EmptyBalanced.
  - assert (h1 : forall s, mirror (s ++ [BracketClose]) = [BracketOpen] ++ mirror s).
    { intro l. induction l as [| head tail IH'].
      - easy.
      - rewrite <- app_comm_cons. destruct head; simpl in *; now rewrite IH'. }
    assert (h2 : forall s, mirror ([BracketOpen] ++ s ++ [BracketClose]) = [BracketOpen] ++ mirror s ++ [BracketClose]).
    { intro l. rewrite app_assoc, h1. easy. }
    rewrite h2. now apply WrapBalanced.
  - rewrite mirrorApp. now apply JoinBalanced.
Qed.

Lemma mirrorWithBlanksCountOpen (s : list (option Bracket)) : count_occ optionBracketEqualityDecidable (mirrorWithBlanks s) (Some BracketOpen) = count_occ optionBracketEqualityDecidable s (Some BracketClose).
Proof.
  induction s as [| [[|]|] tail IH]; simpl in *. { easy. }
  #[local] Hint Resolve Nat.add_1_r : core.
  all: now rewrite count_occ_app, IH.
Qed.

Lemma mirrorWithBlanksCountClose (s : list (option Bracket)) : count_occ optionBracketEqualityDecidable (mirrorWithBlanks s) (Some BracketClose) = count_occ optionBracketEqualityDecidable s (Some BracketOpen).
Proof.
  induction s as [| [[|]|] tail IH]; simpl in *. { easy. }
  #[local] Hint Resolve Nat.add_1_r : core.
  all: now rewrite count_occ_app, IH.
Qed.

Lemma mirrorWithBlanksCountNone (s : list (option Bracket)) : count_occ optionBracketEqualityDecidable (mirrorWithBlanks s) None = count_occ optionBracketEqualityDecidable s None.
Proof.
  induction s as [| [[|]|] tail IH]; simpl in *. { easy. }
  #[local] Hint Resolve Nat.add_1_r : core.
  all: now rewrite count_occ_app, IH.
Qed.

Lemma mirrorRepeatOpen (n : nat) : mirror (repeat BracketOpen n) = repeat BracketClose n.
Proof.
  induction n as [| n IH]. { easy. }
  simpl. now rewrite IH, repeat_cons.
Qed.

Lemma mirrorRepeatClose (n : nat) : mirror (repeat BracketClose n) = repeat BracketOpen n.
Proof.
  induction n as [| n IH]. { easy. }
  simpl. now rewrite IH, repeat_cons.
Qed.

Lemma getWitnessMirror (s : list (option Bracket)) : getWitness (mirrorWithBlanks s) = mirror (getWitness s).
Proof.
  unfold getWitness in *. now rewrite mirrorWithBlanksPreservesLength, mirrorApp, mirrorRepeatClose, mirrorRepeatOpen, mirrorWithBlanksCountClose, mirrorWithBlanksCountOpen.
Qed.

Lemma getSecondWitnessMirror (s : list (option Bracket)) : getSecondWitness (mirrorWithBlanks s) = mirror (getSecondWitness s).
Proof.
  unfold getSecondWitness in *. rewrite mirrorWithBlanksPreservesLength, !mirrorApp, mirrorRepeatClose, mirrorRepeatOpen, mirrorWithBlanksCountClose, mirrorWithBlanksCountOpen. simpl. listsEqual.
Qed.

Definition oppositeSign (x : Bracket) := match x with
  | BracketOpen => BracketClose
  | BracketClose => BracketOpen
  end.

Lemma nthMirror (s : list Bracket) (position : nat) (h : position < length s) default : nth position s default = oppositeSign (nth (length s - position - 1) (mirror s) default).
Proof.
  induction s as [| head tail IH] in position, h |- *. { easy. }
  destruct position as [| position].
  { simpl in *. rewrite Nat.sub_0_r in *.
    rewrite <- mirrorPreservesLength.
    destruct head; now rewrite (nthAppZero (mirror tail)). }
  simpl in *.
  destruct head; rewrite nthAppLt, IH; try (rewrite mirrorPreservesLength); (done || lia).
Qed.

Lemma nthMirror2 (s : list Bracket) (position : nat) (h : position < length s) default : oppositeSign (nth position s default) = nth (length s - position - 1) (mirror s) default.
Proof.
  induction s as [| head tail IH] in position, h |- *. { easy. }
  destruct position as [| position].
  { simpl in *. rewrite Nat.sub_0_r in *.
    rewrite <- mirrorPreservesLength.
    destruct head; now rewrite (nthAppZero (mirror tail)). }
  simpl in *.
  destruct head; rewrite nthAppLt, IH; try (rewrite mirrorPreservesLength); (done || lia).
Qed.

Lemma mirrorMirror (s : list Bracket) : mirror (mirror s) = s.
Proof.
  induction s as [| [|] tail IH]. { easy. }
  all: simpl; now rewrite mirrorApp, IH.
Qed.

Lemma fillMirror (withBlanks : list (option Bracket)) witness (hRightLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) : mirror (fill withBlanks witness) = fill (mirrorWithBlanks withBlanks) (mirror witness).
Proof.
  induction withBlanks as [| [[|] |] tail IH] in witness, hRightLength |- *. { easy. }
  - simpl in *. rewrite (ltac:(now rewrite app_nil_r) : mirror witness = mirror witness ++ []), fillApp, IH; try easy. now rewrite mirrorPreservesLength, mirrorWithBlanksCountNone.
  - simpl in *. rewrite (ltac:(now rewrite app_nil_r) : mirror witness = mirror witness ++ []), fillApp, IH; try easy. now rewrite mirrorPreservesLength, mirrorWithBlanksCountNone.
  - destruct witness as [| head' tail']; simpl in *; try lia.
    destruct head'; rewrite fillApp; try (rewrite mirrorPreservesLength, mirrorWithBlanksCountNone; lia); try easy; rewrite IH; (done || lia).
Qed.

Lemma twoWaysToFillAux (withBlanks : list (option Bracket)) (witness : list Bracket) (hDiff : getWitness withBlanks <> witness) (hRightLength : length witness = count_occ optionBracketEqualityDecidable withBlanks None) (hWitnessValid : isBalanced (fill withBlanks witness)) : isBalanced (fill withBlanks (getSecondWitness withBlanks)).
Proof.
  destruct (fromArbitraryWitness withBlanks witness hWitnessValid hRightLength) as [hGetWitness [hEven [hCountLt1 [hCountLt2 hLengthGetWitness]]]].
  pose proof twoWaysToFillCountOccBounds withBlanks witness (getWitness withBlanks) ltac:(congruence) ltac:(assumption) ltac:(lia) ltac:(assumption) ltac:(assumption).
  destruct (oneDifferentPlace (getWitness withBlanks) witness BracketOpen hDiff ltac:(congruence)) as [position [hPosition hNth]].
  assert (hLt : position < length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) -> nth position (getWitness withBlanks) BracketOpen = BracketOpen /\ nth position witness BracketOpen = BracketClose).
  { intro h. unfold getWitness in *. rewrite nthAppLt in *; try (rewrite repeat_length in *; lia).
    rewrite nth_repeat in *. destruct (nth position witness BracketOpen); intuition. }
  assert (hGeq : length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) <= position -> nth position (getWitness withBlanks) BracketOpen = BracketClose /\ nth position witness BracketOpen = BracketOpen).
  { intro h. unfold getWitness in *. rewrite nthAppGeq in *; try (rewrite repeat_length in *; lia).
    rewrite (nth_indep _ BracketOpen BracketClose), nth_repeat in *; try (rewrite ?app_length, ?repeat_length in *; lia). destruct (nth position witness BracketOpen); intuition. }
  destruct (decide (position < length withBlanks / 2 - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen))) as [hSplit | hSplit].
  - apply (twoWaysToFillAux_differenceOnLeftSegment withBlanks witness position); try (lia || done).
  - destruct (hGeq ltac:(lia)) as [hNthGetWitness hNthWitness].
    destruct hEven as [w hEven].
    pose proof (ltac:(now apply Nat.div_mul) : w * 2 / 2 = w) as hDiv. rewrite <- hEven in hDiv.
    pose proof addThreeTypes withBlanks.
    assert (hOppositeSignDiff : forall a b, a <> b -> oppositeSign a <> oppositeSign b).
    { intros a b h. destruct a; destruct b; easy. }
    assert (hGetWitnessLength : length (getWitness (mirrorWithBlanks withBlanks)) = length (getWitness withBlanks)).
    { unfold getWitness. rewrite !app_length, !repeat_length, !mirrorWithBlanksPreservesLength, !mirrorWithBlanksCountClose, !mirrorWithBlanksCountOpen. lia. }
    epose proof twoWaysToFillAux_differenceOnLeftSegment (mirrorWithBlanks withBlanks) (mirror witness) (length witness - position - 1) ltac:(lia) ltac:(rewrite mirrorWithBlanksPreservesLength, mirrorWithBlanksCountOpen; lia) ltac:(rewrite getWitnessMirror, nthMirror; rewrite mirrorPreservesLength, ?mirrorMirror; try lia; rewrite (ltac:(lia) : (length (getWitness withBlanks) - (length witness - position - 1) - 1) = position), <- nthMirror2; try lia; now apply hOppositeSignDiff) ltac:(now rewrite mirrorPreservesLength, mirrorWithBlanksCountNone) ltac:(rewrite <- fillMirror; now try apply mirrorStillBalanced) as hDestination.
    rewrite getSecondWitnessMirror, <- fillMirror in hDestination.
    + pose proof mirrorStillBalanced _ hDestination. now rewrite mirrorMirror in *.
    + unfold getSecondWitness. rewrite !app_length, !repeat_length, (ltac:(easy) : length [BracketClose; BracketOpen] = 2). lia.
Qed.

Lemma twoWaysToFill (withBlanks : list (option Bracket)) (witness1 witness2 : list Bracket) (hDiff : witness1 <> witness2) (hRightLength1 : length witness1 = count_occ optionBracketEqualityDecidable withBlanks None) (hRightLength2 : length witness2 = count_occ optionBracketEqualityDecidable withBlanks None) (hWitness1Valid : isBalanced (fill withBlanks witness1)) (hWitness2Valid : isBalanced (fill withBlanks witness2)) : isBalanced (fill withBlanks (getSecondWitness withBlanks)).
Proof.
  destruct (decide (witness1 = getWitness withBlanks)).
  - refine (twoWaysToFillAux withBlanks witness2 _ hRightLength2 _); (congruence || done).
  - refine (twoWaysToFillAux withBlanks witness1 _ hRightLength1 _); (congruence || done).
Qed.
