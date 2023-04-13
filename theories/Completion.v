From CoqCP Require Import Options ListsEqual ListDecomposition SwapUpdate.
From stdpp Require Import numbers list.

Section Completion.
Context {A : Type} `{EqDecision A} `{decide : EqDecision (option A)}.

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

Lemma isCompletionMeansLengthEqual : forall withBlanks filled, isCompletion withBlanks filled -> length withBlanks = length filled.
Proof.
  intros withBlanks filled. revert withBlanks.
  induction filled as [| head tail IH];
  intros [| [head1 |] tail1] h; simpl in *;
  try apply eq_S, IH; now try case_bool_decide.
Qed.

Lemma isPartialCompletionMeansLengthEqual : forall withBlanks partialFilled, isPartialCompletion withBlanks partialFilled -> length withBlanks = length partialFilled.
Proof.
  intros withBlanks partialFilled. revert withBlanks.
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

Lemma fillPartialPreservesLength withBlanks : forall answers, length (fillPartial withBlanks answers) = length withBlanks.
Proof.
  induction withBlanks as [| [head |] tail IH];
  intros [| head1 tail1]; simpl in *; now try apply eq_S.
Qed.

Fixpoint stripOptions (l : list (option A)) (default : A) : list A :=
  match l with
  | [] => []
  | (Some head :: tail) => head :: stripOptions tail default
  | (None :: tail) => default :: stripOptions tail default
  end.

Lemma stripOptionsPreservesLength (l : list (option A)) (default : A) : length l = length (stripOptions l default).
Proof.
  induction l as [| [head |] tail IH]; simpl; now try apply eq_S, IH.
Qed.

Lemma noNoneIfCorrectLength withBlanks answers (h : length answers = count_occ decide withBlanks None) : Forall is_Some (fillPartial withBlanks answers).
Proof.
  revert answers h. induction withBlanks as [| [head |] tail IH]; intros [| head1 tail1] h; try simpl; try now try lia.
  - apply Forall_cons. split; try easy. rewrite count_occ_cons_neq in h; try easy. exact (IH _ h).
  - apply Forall_cons. split; try easy. rewrite count_occ_cons_neq in h; try easy. exact (IH _ h).
  - rewrite count_occ_cons_eq in h; easy.
  - apply Forall_cons. split; try easy. rewrite count_occ_cons_eq in h; try easy. exact (IH tail1 ltac:(simpl in *; lia)).
Qed.

Lemma rightLengthApp (w1 w2 : list (option A)) (s1 s2 : list A) :
  length s1 = count_occ decide w1 None ->
  length s2 = count_occ decide w2 None ->
  length (s1 ++ s2) = count_occ decide (w1 ++ w2) None.
Proof. rewrite count_occ_app, app_length. lia. Qed.

Fixpoint fill (withBlanks : list (option A)) (toFill : list A) : list A :=
  match withBlanks, toFill with
  | [], _ => []
  | (None :: tail), (toFill :: remaining) => toFill :: fill tail remaining
  | (None :: tail), [] => []
  | (Some stuff :: tail), remaining => stuff :: fill tail remaining
  end.

Lemma fillApp (w1 w2 : list (option A)) (s1 s2 : list A)
  (h1 : length s1 = count_occ decide w1 None)
  (h2 : length s2 = count_occ decide w2 None) :
  fill (w1 ++ w2) (s1 ++ s2) = fill w1 s1 ++ fill w2 s2.
Proof.
  revert s1 h1; induction w1 as [| [b |] w1 IHw1]; intros s1 h1; destruct s1 as [| b1 s1];
  simpl in *; try destruct (decide _ _); try rewrite <- IHw1; try (done || lia).
Qed.

Lemma partialCompletionTransitive (s1 s2 s3 : list (option A)) (h1 : isPartialCompletion s1 s2) (h2 : isPartialCompletion s2 s3) : isPartialCompletion s1 s3.
Proof.
  induction s1 as [| [b1 |] s1 IH] in s2, s3, h1, h2 |- *; destruct s2 as [| [head2 |] tail2]; destruct s3 as [| [head3 |] tail3]; simpl in *; rewrite ?andb_True in *; try destruct h1; try destruct h2; rewrite ?bool_decide_spec in *; try split; try apply (IH tail2 _); try (congruence || tauto).
Qed.

Fixpoint extractAnswers (s : list (option A)) (completed : list A) :=
  match s, completed with
  | (Some _ :: tail1), (head2 :: tail2) => extractAnswers tail1 tail2
  | (None :: tail1), (head2 :: tail2) => head2 :: extractAnswers tail1 tail2
  | [], _ => []
  | _, [] => []
  end.

Lemma extractAnswersLength (s : list (option A)) (completed : list A) (h : isCompletion s completed): length (extractAnswers s completed) = count_occ decide s None.
Proof.
  induction s as [| [head |] tail IH] in completed, h |- *; destruct completed as [| head1 tail1]; simpl in *; try destruct (decide _ _); try (done || lia); rewrite ?andb_True in *.
  - now rewrite <- (IH _ (proj2 h)).
  - now rewrite <- (IH _ h).
Qed.

Lemma extractAnswersCorrect (s : list (option A)) (completed : list A) (h : isCompletion s completed) (h1 : length (extractAnswers s completed) = count_occ decide s None) : fill s (extractAnswers s completed) = completed.
Proof.
  induction s as [| [head |] tail IH] in completed, h, h1 |- *;
  destruct completed as [| head1 tail1];
  simpl in *;
  try destruct (decide _ _); try done;
  rewrite ?andb_True, ?bool_decide_spec in *;
  rewrite ?IH; intuition congruence.
Qed.

Lemma fillIsCompletion (withBlanks : list (option A)) (answers : list A) (h : length answers = count_occ decide withBlanks None) : isCompletion withBlanks (fill withBlanks answers).
Proof.
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

Lemma takeKthBlankCountOcc (withBlanks : list (option A)) (k : nat) (hReasonable : k < count_occ decide withBlanks None) : count_occ decide (take (getKthBlank withBlanks k) withBlanks) None = k.
  induction withBlanks as [| head tail IH] in k, hReasonable |- *.
  - simpl in *. lia.
  - destruct k; destruct head; simpl in *; destruct (decide _ _); try rewrite IH; (lia || done).
Qed.

Lemma dropKthBlankCountOcc (withBlanks : list (option A)) (k : nat) : count_occ decide (drop (getKthBlank withBlanks k) withBlanks) None = count_occ decide withBlanks None - k.
  induction withBlanks as [| head tail IH] in k |- *.
  - simpl in *. lia.
  - destruct k; destruct head; simpl in *; destruct (decide _ _); try rewrite IH; (lia || done).
Qed.

Lemma dropSuccKthBlankCountOcc (withBlanks : list (option A)) (k : nat) : count_occ decide (drop (S (getKthBlank withBlanks k)) withBlanks) None = count_occ decide withBlanks None - k - 1.
  induction withBlanks as [| head tail IH] in k |- *.
  - simpl in *. lia.
  - destruct k; destruct head; simpl in *; destruct (decide _ _); try rewrite IH; try rewrite drop_0; try (lia || done).
Qed.

Lemma dropSuccTakeKthBlankCountOcc (withBlanks : list (option A)) (i j : nat) (hLt : i <= j) (hReasonable : j < count_occ decide withBlanks None) : count_occ decide (drop (S (getKthBlank withBlanks i)) (take (getKthBlank withBlanks j) withBlanks)) None = j - i - 1.
Proof.
  induction withBlanks as [| [head |] tail IH] in i, j, hLt, hReasonable |- *; try easy;
  destruct i as [| i]; destruct j as [| j]; simpl in *; try rewrite IH; try destruct (decide _ _); try (done || lia).
  rewrite drop_0, takeKthBlankCountOcc; lia.
Qed.

Lemma dropTakeKthBlankCountOcc (withBlanks : list (option A)) (i j : nat) (hLt : i <= j) (hReasonable : j < count_occ decide withBlanks None) : count_occ decide (drop (getKthBlank withBlanks i) (take (getKthBlank withBlanks j) withBlanks)) None = j - i.
Proof.
  induction withBlanks as [| [head |] tail IH] in i, j, hLt, hReasonable |- *; try easy;
  destruct i as [| i]; destruct j as [| j]; simpl in *; try rewrite IH; try destruct (decide _ _); try (done || lia).
  rewrite takeKthBlankCountOcc; lia.
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

Lemma fillInOneBlank_h2Parameter (withBlanks : list (option A)) (k : nat) (hReasonable: k < count_occ decide withBlanks None) (value : A) (answers : list A) (h : length answers + 1 = count_occ decide withBlanks None) : length answers = count_occ decide (<[getKthBlank withBlanks k := Some value]> withBlanks) None.
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

Lemma fillInOneBlank (withBlanks : list (option A)) (k : nat) (hReasonable : k < count_occ decide withBlanks None) (value : A) (answers : list A) (h : length answers + 1 = count_occ decide withBlanks None) : fill withBlanks (take k answers ++ [value] ++ drop k answers) = fill (<[getKthBlank withBlanks k := Some value]> withBlanks) answers.
Proof.
  destruct (fillSplit value (take k answers) (drop k answers) withBlanks k) as [H1 [H2 H3]].
  { rewrite take_length. lia. }
  { now apply fillInOneBlank_h1Parameter. }
  pose proof fillApp (take (getKthBlank withBlanks k) withBlanks) ([None] ++ (drop (S (getKthBlank withBlanks k)) withBlanks)) (take k answers) ([value] ++ drop k answers) H2 ltac:(rewrite !app_length, !count_occ_app; simpl; destruct (decide _ _); (lia || done)) as step1.
  rewrite <- H1 in step1.
  rewrite step1.
  simpl.
  pose proof getKthBlankUpperBound _ _ hReasonable as hUpperBound.
  pose proof updateAppZero (take (getKthBlank withBlanks k) withBlanks) ([nth (getKthBlank withBlanks k) withBlanks None] ++ drop (S (getKthBlank withBlanks k)) withBlanks) (Some value) as H.
  rewrite <- (listDecompositionSingle withBlanks (getKthBlank withBlanks k) hUpperBound None) in *.
  rewrite take_length in H.
  assert (hMin : getKthBlank withBlanks k `min` length withBlanks = getKthBlank withBlanks k). { lia. }
  rewrite hMin in *. rewrite H. simpl.
  pose proof fillApp (take (getKthBlank withBlanks k) withBlanks) (Some value :: drop (S (getKthBlank withBlanks k)) withBlanks) (take k answers) (drop k answers) ltac:(rewrite take_length, takeKthBlankCountOcc; simpl in *; lia) ltac:(simpl; now destruct (decide _ _)) as hPartial.
  rewrite take_drop in hPartial.
  rewrite hPartial. simpl. reflexivity.
Qed.

Lemma partialCompletionSelf (x : list (option A)) : isPartialCompletion x x.
Proof.
  induction x as [| [head |] tail IH]; simpl; now rewrite ?andb_True, ?bool_decide_spec.
Qed.

Lemma updateKthPartialCompletion (withBlanks : list (option A)) (k : nat) (hReasonable : k < count_occ decide withBlanks None) (value : A) : isPartialCompletion withBlanks (<[getKthBlank withBlanks k := Some value]> withBlanks).
Proof.
  induction withBlanks as [| [head |] tail IH] in k, hReasonable |- *; try easy;
  destruct k; simpl in *; rewrite ?andb_True, ?bool_decide_spec;
  ((try split; try tauto; apply IH; destruct (decide _ _); (done || lia)) || apply partialCompletionSelf).
Qed.

Lemma getKthBlankLt (withBlanks : list (option A)) (i j : nat) (hReasonable : j < count_occ decide withBlanks None) (hLt : i < j) : getKthBlank withBlanks i < getKthBlank withBlanks j.
Proof.
  induction withBlanks as [| [head |] tail IH] in i, j, hReasonable, hLt |- *; try easy; destruct i as [| i]; destruct j as [| j]; simpl in *; destruct (decide _ _); try (done || lia); apply Arith_prebase.lt_n_S_stt, IH; (done || lia).
Qed.

End Completion.
