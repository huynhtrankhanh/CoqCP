From CoqCP Require Import Options.
From Submission Require Import KthHighestScore KthHighestScoreCode
  KthHighestScoreIO KthHighestScorePrinter KthHighestScoreEndToEnd KthHighestScoreExamples.
From Stdlib Require Import Lia Lists.List.
Require Trusted.Spec.

Lemma above_ext n F G score
  (hEqual : forall i, (1 <= i <= n)%nat -> F i = G i) :
  above F n score = above G n score.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [above]. rewrite IH.
    + rewrite (hEqual (S n)) by lia. reflexivity.
    + intros i hi. apply hEqual. lia.
Qed.

Lemma kth_highest_ext n k F S score :
  kth_highest n k (extend n F) (extend n S) score ->
  kth_highest n k F S score.
Proof.
  unfold kth_highest. intros [[ [i [hi heq]] | [j [hj heq]] ] hcount].
  - split; [left; exists i; split; [exact hi | rewrite extend_real in heq by exact hi; exact heq] |].
    rewrite (above_ext n (extend n F) F score (fun i hi => extend_real n F i hi)),
      (above_ext n (extend n S) S score (fun i hi => extend_real n S i hi)) in hcount.
    exact hcount.
  - split; [right; exists j; split; [exact hj | rewrite extend_real in heq by exact hj; exact heq] |].
    rewrite (above_ext n (extend n F) F score (fun i hi => extend_real n F i hi)),
      (above_ext n (extend n S) S score (fun i hi => extend_real n S i hi)) in hcount.
    exact hcount.
Qed.

Lemma mathematical_correct n k F S
  (hn : (1 <= n)%nat) (hk : (1 <= k <= 2*n)%nat) (hSize : (n <= 100000)%nat)
  (hF : Trusted.Spec.valid_scores n F) (hS : Trusted.Spec.valid_scores n S)
  (hDistinct : forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> F i <> S j) :
  Trusted.Spec.kth_highest n k F S (answer n k (extend n F) (extend n S)).
Proof.
  destruct hF as [hF_bounds hF_sorted], hS as [hS_bounds hS_sorted].
  assert (hExtendedDistinct : forall i j, (1 <= i <= n)%nat ->
    (1 <= j <= n)%nat -> extend n F i <> extend n S j).
  { intros i j hi hj. rewrite !extend_real by assumption. apply hDistinct; assumption. }
  apply kth_highest_ext.
  exact (@answer_correct n k (extend n F) (extend n S) hn hk
    (extend_valid n F hF_bounds hF_sorted)
    (extend_valid n S hS_bounds hS_sorted)
    hExtendedDistinct hSize).
Qed.

Module Implementation.
  Definition program : Trusted.Spec.Program := Trusted.Spec.program.

  Theorem correct : Trusted.Spec.required program.
  Proof.
    split; [reflexivity |]. intros n k F S hn hk hSize hF hS hDistinct.
    pose proof (mathematical_correct n k F S hn hk hSize hF hS hDistinct) as hAnswer.
    exists (allQueries n k F S), (answer n k (extend n F) (extend n S)).
    assert (hFe : country_valid n (extend n F)).
    { apply extend_valid; [exact (proj1 hF) | exact (proj2 hF)]. }
    assert (hSe : country_valid n (extend n S)).
    { apply extend_valid; [exact (proj1 hS) | exact (proj2 hS)]. }
    split.
    - rewrite allQueries_trace. unfold wireQueries. rewrite Forall_map.
      change (Forall (valid_query n) (query_trace n k (extend n F) (extend n S))).
      apply queries_legal; assumption.
    - split.
      + rewrite allQueries_trace. unfold wireQueries. rewrite length_map. apply query_limit.
      + split; [exact hAnswer |].
        apply generated_end_to_end; try assumption; [lia |].
        apply bounded_fits. destruct (proj1 hAnswer) as [[i [hi equal]] | [j [hj equal]]].
        * rewrite <- equal. exact (proj2 (proj1 hF i hi)).
        * rewrite <- equal. exact (proj2 (proj1 hS j hj)).
  Qed.
End Implementation.
Print Assumptions Implementation.correct.
