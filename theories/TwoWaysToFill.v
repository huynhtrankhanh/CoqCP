From CoqCP Require Import Options FillInTheBlanks Completion RegularBracketString SwapUpdate ListDecomposition ListsEqual.
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
  - destruct (hLt ltac:(lia)) as [hNthGetWitness hNthWitness].
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
    rewrite <- (nthGetKthBlank withBlanks position None), <- listDecompositionSingle in hIntermediate; try (pose proof getKthBlankUpperBound withBlanks position; lia). admit.
  - destruct (hGeq ltac:(lia)) as [hNthGetWitness hNthWitness]. admit.
    (* I'd take advantage of symmetry. there's no way I'd go through this grueling proof ever again *)
Admitted.

Lemma twoWaysToFill (withBlanks : list (option Bracket)) (witness1 witness2 : list Bracket) (hDiff : witness1 <> witness2) (hRightLength1 : length witness1 = count_occ optionBracketEqualityDecidable withBlanks None) (hRightLength2 : length witness2 = count_occ optionBracketEqualityDecidable withBlanks None) (hWitness1Valid : isBalanced (fill withBlanks witness1)) (hWitness2Valid : isBalanced (fill withBlanks witness2)) : isBalanced (fill withBlanks (getSecondWitness withBlanks)).
Proof.
  destruct (decide (witness1 = getWitness withBlanks)).
  - refine (twoWaysToFillAux withBlanks witness2 _ hRightLength2 _); (congruence || done).
  - refine (twoWaysToFillAux withBlanks witness1 _ hRightLength1 _); (congruence || done).
Qed.
