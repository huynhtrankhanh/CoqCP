From CoqCP Require Import Options.
From Submission Require Import KthHighestScore KthHighestScoreCode.
From Stdlib Require Import Lia.
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

Module Implementation.
  Definition program (n k : nat) (F S : nat -> nat) :=
    answer n k (extend n F) (extend n S).

  Lemma correct : Trusted.Spec.required program.
  Proof.
    unfold Trusted.Spec.required, program.
    intros n k F S hn hk hSize hF hS hDistinct.
    destruct hF as [hF_bounds hF_sorted].
    destruct hS as [hS_bounds hS_sorted].
    assert (hExtendedDistinct : forall i j, (1 <= i <= n)%nat ->
      (1 <= j <= n)%nat -> extend n F i <> extend n S j).
    { intros i j hi hj. rewrite !extend_real by assumption. apply hDistinct; assumption. }
    apply kth_highest_ext.
    exact (@answer_correct n k (extend n F) (extend n S) hn hk
      (extend_valid n F hF_bounds hF_sorted)
      (extend_valid n S hS_bounds hS_sorted)
      hExtendedDistinct hSize).
  Qed.

  (* The generated-code refinement is checked alongside the semantic contract. *)
  Definition generated_code_correct := generated_search_correct.
End Implementation.
