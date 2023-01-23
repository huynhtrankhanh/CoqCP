From stdpp Require Import numbers list.
From CoqCP Require Import RegularBracketString PrefixApp ListsEqual.

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

Definition possibleToFillBool (withBlanks : list (option Bracket)) :=
  let count := length withBlanks / 2 in
  let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
  let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
  isBalancedBool (fillLeftToRight withBlanks (repeat BracketOpen remainingOpenCount ++ repeat BracketClose remainingCloseCount)).

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

Lemma possibleToFillIffPossibleToFillBool (withBlanks : list (option Bracket)) : possibleToFill withBlanks <-> possibleToFillBool withBlanks.
Proof.
  (* dear the Coq community, I can't prove this *)
  (* can you help me out? pretty please with a cherry on top *)
Admitted.
