From CoqCP Require Import Options.
From Submission Require Import KthHighestScore KthHighestScoreCode.
Require Trusted.Spec.

Module Implementation.
  Definition program : Trusted.Spec.Program := Trusted.Spec.generatedSearchLoop.
  Lemma correct : Trusted.Spec.required program.
  Proof. split; [reflexivity | exact generated_search_correct]. Qed.
End Implementation.
