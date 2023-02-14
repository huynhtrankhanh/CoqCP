From CoqCP Require Import Options ListsEqual.
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

Lemma fillSplit (b : A) (s1 s2 : list A) (withBlanks : list (option A)) : length (s1 ++ [b] ++ s2) = count_occ decide withBlanks None -> exists wb1 wb2, withBlanks = wb1 ++ [None] ++ wb2 /\ length s1 = count_occ decide wb1 None /\ length s2 = count_occ decide wb2 None.
Proof.
  simpl; rewrite !app_length; simpl; rewrite Nat.add_succ_r; simpl; clear b.
  induction withBlanks as [|[b'|] wb IHwb] in s1, s2 |- *; intros HL; simplify_eq/=; try destruct (decide _ _); try done. {
    destruct (IHwb s1 s2 HL) as (wb1 & wb2 & -> & ?); destruct_and!.
    exists (Some b' :: wb1), wb2. simpl. now destruct (decide _ _).
  }
  destruct s1 as [|b1 s1]; simplify_eq/=. { by exists [], wb. }
  destruct (IHwb s1 s2 HL) as (wb1 & wb2 & -> & ?); destruct_and!.
  exists (None :: wb1), wb2; split_and!; simpl; try destruct (decide _ _); (done || lia).
Qed.

Lemma fillIsCompletion (withBlanks : list (option A)) (answers : list A) h : isCompletion withBlanks (fill withBlanks answers h).
Proof.
  rewrite <- fillLaxEqFill.
  induction withBlanks as [| [head |] tail IH] in answers, h |- *.
  - easy.
  - destruct answers as [| head1 tail1]; simpl; case_bool_decide; try easy; simpl in *; destruct (decide _ _); now apply IH.
  - destruct answers as [| head1 tail1]; simpl in *; destruct (decide _ _); try easy. apply IH. lia.
Qed.

End Completion.
