From CoqCP Require Import Options ListsEqual ListDecomposition SwapUpdate.
From stdpp Require Import numbers list.

Section Completion.
Context {A : Type} `{EqDecision A} `{decide : EqDecision (option A)}.

Section Definitions.
Context (withBlanks partialFilled : list (option A)) (filled : list A) (answers : list A).

Fixpoint isCompletion (withBlanks : list (option A)) (filled : list A) :=
  match withBlanks, filled with
  | [], [] => true
  | [], (x :: _) => false
  | (_ :: _), [] => false
  | (Some a :: tail1), (b :: tail2) => bool_decide (a = b) && isCompletion tail1 tail2
  | (None :: tail1), (b :: tail2) => isCompletion tail1 tail2
  end.

Fixpoint isPartialCompletion (withBlanks partialFilled : list (option A)) :=
  match withBlanks, partialFilled with
  | [], [] => true
  | [], (_ :: _) => false
  | (_ :: _), [] => false
  | (Some a :: tail1), (None :: tail2) => false
  | (Some a :: tail1), (Some b :: tail2) => bool_decide (a = b) && isPartialCompletion tail1 tail2
  | (None :: tail1), (_ :: tail2) => isPartialCompletion tail1 tail2
  end.

Lemma isCompletionMeansLengthEqual : forall withBlanks, isCompletion withBlanks filled -> length withBlanks = length filled.
Proof.
  induction filled as [| head tail IH];
  intros [| [head1 |] tail1] h; simpl in *;
  try apply eq_S, IH; now try case_bool_decide.
Qed.

Lemma isPartialCompletionMeansLengthEqual : forall withBlanks, isPartialCompletion withBlanks partialFilled -> length withBlanks = length partialFilled.
Proof.
  induction partialFilled as [| [head |] tail IH];
  intros [| [head1 |] tail1] h; simpl in *;
  try apply eq_S, IH; now try case_bool_decide.
Qed.

Fixpoint fillPartial (withBlanks : list (option A)) (answers : list A) :=
  match withBlanks, answers with
  | [], _ => []
  | (Some a :: tail), x => Some a :: fillPartial tail x
  | (None :: tail), (x :: tail') => Some x :: fillPartial tail tail'
  | (None :: tail), [] => None :: tail
  end.

Lemma fillPartialPreservesLength : forall answers, length (fillPartial withBlanks answers) = length withBlanks.
Proof.
  induction withBlanks as [| [head |] tail IH];
  intros [| head1 tail1]; simpl in *; now try apply eq_S.
Qed.

Lemma stripOptions (l : list (option A)) (hNoOptions : Forall is_Some l) : list A.
Proof.
  induction l as [| head tail IH].
  - exact [].
  - refine (_ :: (IH _)).
    + destruct head as [head |].
      * exact head.
      * exfalso. exact (is_Some_None (proj1 (Forall_cons_1 _ _ _ hNoOptions))).
    + exact (proj2 (Forall_cons_1 _ _ _ hNoOptions)).
Defined.

Lemma stripOptionsPreservesLength (l : list (option A)) (hNoOptions : Forall is_Some l) : length l = length (stripOptions l hNoOptions).
Proof.
  induction l as [| head tail IH]; simpl; now try apply eq_S, IH.
Qed.

Lemma noNoneIfCorrectLength (h : length answers = count_occ decide withBlanks None) : Forall is_Some (fillPartial withBlanks answers).
Proof.
  revert answers h. induction withBlanks as [| [head |] tail IH]; intros [| head1 tail1] h; try simpl; try now try lia.
  - apply Forall_cons. split; try easy. rewrite count_occ_cons_neq in h; try easy. exact (IH _ h).
  - apply Forall_cons. split; try easy. rewrite count_occ_cons_neq in h; try easy. exact (IH _ h).
  - rewrite count_occ_cons_eq in h; easy.
  - apply Forall_cons. split; try easy. rewrite count_occ_cons_eq in h; try easy. exact (IH tail1 ltac:(simpl in *; lia)).
Qed.

Definition fill (h : length answers = count_occ decide withBlanks None) : list A :=
  (stripOptions (fillPartial withBlanks answers) (noNoneIfCorrectLength h)).
End Definitions.

Lemma rightLengthApp (w1 w2 : list (option A)) (s1 s2 : list A) :
  length s1 = count_occ decide w1 None ->
  length s2 = count_occ decide w2 None ->
  length (s1 ++ s2) = count_occ decide (w1 ++ w2) None.
Proof. rewrite count_occ_app, app_length. lia. Qed.

Fixpoint fillLax (withBlanks : list (option A)) (toFill : list A) : list A :=
  match withBlanks, toFill with
  | [], _ => []
  | (None :: tail), (toFill :: remaining) => toFill :: fillLax tail remaining
  | (None :: tail), [] => []
  | (Some stuff :: tail), remaining => stuff :: fillLax tail remaining
  end.

Lemma stripOptionsProofIndependent (l : list (option A)) (h1 h2 : Forall is_Some l) : stripOptions l h1 = stripOptions l h2.
Proof.
  induction l as [| [head |] tail IH]; try easy.
  - simpl. erewrite IH. reflexivity.
  - exfalso. exact (is_Some_None (proj1 (proj1 (Forall_cons is_Some None tail) h1))).
Qed.

Lemma foldFill (withBlanks : list (option A)) (toFill : list A) h h' : fill withBlanks toFill h = stripOptions (fillPartial withBlanks toFill) h'.
Proof.
  unfold fill. now rewrite (stripOptionsProofIndependent _ _ h').
Qed.

Lemma fillLaxEqFill (withBlanks : list (option A)) (toFill : list A) h : fillLax withBlanks toFill = fill withBlanks toFill h.
Proof.
  induction withBlanks as [| [head |] tail IH] in toFill, h |- *.
  - unfold fill. now simpl.
  - unfold fill. simpl.
    assert (h1 : length toFill = count_occ decide tail None).
    { rewrite count_occ_cons_neq in h; easy. }
    now rewrite <- (foldFill tail toFill h1), (IH _ h1).
  - destruct toFill as [| head1 tail1].
    + exfalso. rewrite count_occ_cons_eq in h; easy.
    + unfold fill. simpl.
      assert (h1 : length tail1 = count_occ decide tail None).
      { rewrite count_occ_cons_eq in h; [simpl in *; lia | easy]. }
      now rewrite <- (foldFill tail tail1 h1), (IH _ h1).
Qed.

Lemma fillLaxApp (w1 w2 : list (option A)) (s1 s2 : list A)
  (h1 : length s1 = count_occ decide w1 None)
  (h2 : length s2 = count_occ decide w2 None) :
  fillLax (w1 ++ w2) (s1 ++ s2) = fillLax w1 s1 ++ fillLax w2 s2.
Proof.
  revert s1 h1; induction w1 as [| [b |] w1 IHw1]; intros s1 h1; destruct s1 as [| b1 s1];
  simpl in *; try destruct (decide _ _); try rewrite <- IHw1; try (done || lia).
Qed.

Lemma fillApp (w1 w2 : list (option A)) (s1 s2 : list A) h1 h2 h3 :
  fill (w1 ++ w2) (s1 ++ s2) h3 = fill w1 s1 h1 ++ fill w2 s2 h2.
Proof.
  now rewrite <- (fillLaxEqFill _ _ h1), <- (fillLaxEqFill _ _ h2), <- (fillLaxEqFill _ _ h3), fillLaxApp.
Qed.

Lemma partialCompletionTransitive (s1 s2 s3 : list (option A)) (h1 : isPartialCompletion s1 s2) (h2 : isPartialCompletion s2 s3) : isPartialCompletion s1 s3.
Proof.
  induction s1 as [| [b1 |] s1 IH] in s2, s3, h1, h2 |- *; destruct s2 as [| [head2 |] tail2]; destruct s3 as [| [head3 |] tail3]; simpl in *; rewrite ?andb_True in *; try destruct h1; try destruct h2; rewrite ?bool_decide_spec in *; try split; try apply (IH tail2 _); try (congruence || tauto).
Qed.

Fixpoint extractAnswersLax (s : list (option A)) (completed : list A) :=
  match s, completed with
  | (Some _ :: tail1), (head2 :: tail2) => extractAnswersLax tail1 tail2
  | (None :: tail1), (head2 :: tail2) => head2 :: extractAnswersLax tail1 tail2
  | [], _ => []
  | _, [] => []
  end.

Definition extractAnswers (s : list (option A)) (completed : list A) (hCompletion : isCompletion s completed) := extractAnswersLax s completed.

Lemma extractAnswersLength (s : list (option A)) (completed : list A) h : length (extractAnswers s completed h) = count_occ decide s None.
Proof.
  induction s as [| [head |] tail IH] in completed, h |- *; destruct completed as [| head1 tail1]; unfold extractAnswers; simpl in *; try destruct (decide _ _); try (done || lia); rewrite ?andb_True in *.
  - now rewrite <- (IH _ (proj2 h)).
  - now rewrite <- (IH _ h).
Qed.

Lemma extractAnswersCorrect (s : list (option A)) (completed : list A) (h : isCompletion s completed) (h1 : length (extractAnswers s completed h) = count_occ decide s None) h2 : fill s (extractAnswers s completed h2) h1 = completed.
Proof.
  unfold extractAnswers in *. rewrite <- fillLaxEqFill.
  induction s as [| [head |] tail IH] in completed, h, h1, h2 |- *;
  destruct completed as [| head1 tail1];
  unfold extractAnswers; simpl in *;
  try destruct (decide _ _); try done;
  rewrite ?andb_True, ?bool_decide_spec in *;
  try (destruct h2 as [h2a h2]; rewrite h2a); rewrite ?IH; (done || lia).
Qed.

Lemma fillIsCompletion (withBlanks : list (option A)) (answers : list A) h : isCompletion withBlanks (fill withBlanks answers h).
Proof.
  rewrite <- fillLaxEqFill.
  induction withBlanks as [| [head |] tail IH] in answers, h |- *.
  - easy.
  - destruct answers as [| head1 tail1]; simpl; case_bool_decide; try easy; simpl in *; destruct (decide _ _); now apply IH.
  - destruct answers as [| head1 tail1]; simpl in *; destruct (decide _ _); try easy. apply IH. lia.
Qed.

Fixpoint getKthBlank (withBlanks : list (option A)) (k : nat) :=
  match withBlanks, k with
  | [], _ => 0 (* who cares *)
  | (Some _ :: tail), k => S (getKthBlank tail k)
  | (None :: tail), 0 => 0
  | (None :: tail), S k => S (getKthBlank tail k)
  end.

Lemma nthGetKthBlank (withBlanks : list (option A)) (k : nat) (default : option A) (hReasonable : k < count_occ decide withBlanks None) : nth (getKthBlank withBlanks k) withBlanks default = None.
Proof.
  induction withBlanks as [| [head |] tail IH] in k, hReasonable |- *.
  - simpl in *. lia.
  - simpl in hReasonable. destruct (decide (Some head) None); destruct k; simpl in *; rewrite IH; (lia || done).
  - simpl in hReasonable. destruct (decide None None); destruct k; simpl in *; try rewrite IH; (lia || done).
Qed.

Lemma getKthBlankUpperBound (withBlanks : list (option A)) (k : nat) (hReasonable : k < count_occ decide withBlanks None) : getKthBlank withBlanks k < length withBlanks.
Proof.
  induction withBlanks as [| head tail IH] in k, hReasonable |- *.
  - simpl in *. lia.
  - destruct head; simpl in hReasonable; destruct (decide _ _); destruct k as [| k]; simpl in *; try apply Arith_prebase.lt_n_S_stt; try refine (IH _ _); (done || lia).
Qed.

Lemma fillSplit (b : A) (s1 s2 : list A) (withBlanks : list (option A)) k (hK : k = length s1) : length (s1 ++ [b] ++ s2) = count_occ decide withBlanks None -> withBlanks = take (getKthBlank withBlanks k) withBlanks ++ [None] ++ drop (S (getKthBlank withBlanks k)) withBlanks /\ length s1 = count_occ decide (take (getKthBlank withBlanks k) withBlanks) None /\ length s2 = count_occ decide (drop (S (getKthBlank withBlanks k)) withBlanks) None.
Proof.
  intro hLength.
  pose proof ltac:(rewrite !app_length in hLength; simpl in *; lia) : k < count_occ decide withBlanks None as hReasonable.
  pose proof getKthBlankUpperBound withBlanks k ltac:(lia).
  assert (hCountOcc1 : count_occ decide (take (getKthBlank withBlanks k) withBlanks) None = k).
  { induction withBlanks as [| head tail IH] in k, hReasonable |- *.
    - simpl in *. lia.
    - destruct k; destruct head; simpl in *; destruct (decide _ _); try rewrite IH; (lia || done). }
  repeat split.
  - now rewrite <- (nthGetKthBlank withBlanks k None), <- listDecompositionSingle.
  - congruence.
  - pose proof nthGetKthBlank withBlanks k None hReasonable.
    assert (hIntermediate : count_occ decide (take (getKthBlank withBlanks k) withBlanks) None + count_occ decide [nth (getKthBlank withBlanks k) withBlanks None] None + count_occ decide (drop (S (getKthBlank withBlanks k)) withBlanks) None = count_occ decide withBlanks None).
    { now rewrite <- !count_occ_app, (ltac:(intros; listsEqual) : forall (A : Type) (a b c : list A), (a ++ b) ++ c = a ++ b ++ c), <- listDecompositionSingle. }
    simpl in hIntermediate. destruct (decide _ _); try easy.
    rewrite !app_length in hLength. simpl in *. lia.
Qed.

Lemma fillInOneBlank_h1Parameter (withBlanks : list (option A)) (k : nat) (hReasonable: k < count_occ decide withBlanks None) (value : A) (answers : list A) (h : length answers + 1 = count_occ decide withBlanks None) : length (take k answers ++ [value] ++ drop k answers) = count_occ decide withBlanks None.
Proof.
  rewrite !app_length. simpl. rewrite Nat.add_succ_r, <- app_length, take_drop. lia.
Qed.

Lemma fillInOneBlank_h2Parameter (withBlanks : list (option A)) (k : nat) (hReasonable: k < count_occ decide withBlanks None) (value : A) (answers : list A) (h : length answers + 1 = count_occ decide withBlanks None) : length answers = count_occ decide (<[getKthBlank withBlanks k:= Some value]> withBlanks) None.
Proof.
  pose proof getKthBlankUpperBound _ _ hReasonable as hUpperBound.
  pose proof updateAppZero (take (getKthBlank withBlanks k) withBlanks) ([nth (getKthBlank withBlanks k) withBlanks None] ++ drop (S (getKthBlank withBlanks k)) withBlanks) (Some value) as H.
  rewrite <- (listDecompositionSingle withBlanks (getKthBlank withBlanks k) hUpperBound None) in *.
  rewrite take_length in H.
  assert (hMin : getKthBlank withBlanks k `min` length withBlanks = getKthBlank withBlanks k). { lia. }
  rewrite hMin in *. rewrite H.
  simpl.
  rewrite (ltac:(now intros) : forall (A : Type) (head : A) (tail : list A), head :: tail = [head] ++ tail), !count_occ_app.
  simpl. destruct (decide _ _); try easy.
  rewrite Nat.add_0_l.
  rewrite (listDecompositionSingle withBlanks (getKthBlank withBlanks k) hUpperBound None), !count_occ_app in h.
  simpl in *. destruct (decide _ _) as [| h'].
  - lia.
  - rewrite nthGetKthBlank in h'; (lia || done).
Qed.

Lemma fillInOneBlank (withBlanks : list (option A)) (k : nat) (hReasonable : k < count_occ decide withBlanks None) (value : A) (answers : list A) h1 h2 : fill withBlanks (take k answers ++ [value] ++ drop k answers) h1 = fill (<[getKthBlank withBlanks k := Some value]> withBlanks) answers h2.
Proof.
  rewrite <- !fillLaxEqFill.
  destruct (fillSplit value (take k answers) (drop k answers) withBlanks k) as [H1 [H2 H3]].
  { rewrite !app_length in h1. simpl in h1. rewrite Nat.add_succ_r, <- app_length, take_drop in h1. rewrite take_length. lia. }
  { assumption. }
  pose proof fillLaxApp (take (getKthBlank withBlanks k) withBlanks) ([None] ++ (drop (S (getKthBlank withBlanks k)) withBlanks)) (take k answers) ([value] ++ drop k answers) H2 ltac:(rewrite !app_length, !count_occ_app; simpl; destruct (decide _ _); (lia || done)) as step1.
  rewrite <- H1 in step1.
  rewrite step1.
  simpl.
  pose proof getKthBlankUpperBound _ _ hReasonable as hUpperBound.
  pose proof updateAppZero (take (getKthBlank withBlanks k) withBlanks) ([nth (getKthBlank withBlanks k) withBlanks None] ++ drop (S (getKthBlank withBlanks k)) withBlanks) (Some value) as H.
  rewrite <- (listDecompositionSingle withBlanks (getKthBlank withBlanks k) hUpperBound None) in *.
  rewrite take_length in H.
  assert (hMin : getKthBlank withBlanks k `min` length withBlanks = getKthBlank withBlanks k). { lia. }
  rewrite hMin in *. rewrite H. simpl.
  assert (hCountOcc1 : count_occ decide (take (getKthBlank withBlanks k) withBlanks) None = k).
  { induction withBlanks as [| head tail IH] in k, hReasonable |- *.
    - simpl in *. lia.
    - destruct k; destruct head; simpl in *; destruct (decide _ _); try rewrite IH; (lia || done). }
  pose proof fillLaxApp (take (getKthBlank withBlanks k) withBlanks) (Some value :: drop (S (getKthBlank withBlanks k)) withBlanks) (take k answers) (drop k answers) ltac:(simpl in *; rewrite hCountOcc1, take_length, !app_length in *; simpl in *; rewrite Nat.add_succ_r, <- app_length, take_drop in *; lia) ltac:(simpl; now destruct (decide _ _)) as hPartial.
  rewrite take_drop in hPartial.
  rewrite hPartial. simpl. reflexivity.
Qed.

End Completion.
