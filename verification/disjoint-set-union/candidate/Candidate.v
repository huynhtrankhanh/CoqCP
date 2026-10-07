From CoqCP Require Import Options.
From Submission Require Import DisjointSetUnionCode2 DisjointSetUnionCode3.
Require Trusted.Spec.

Module Implementation.
  Definition program := Trusted.Spec.mergeAction.
  Lemma correct : Trusted.Spec.required program.
  Proof. split; [reflexivity | exact competitiveMergeRefinesModel]. Qed.
  Lemma score_max : Trusted.Spec.scoreBound.
  Proof.
    intros interactions bounds. apply maxScoreIsMax.
    intros a b hIn. specialize (bounds a b hIn). tauto.
  Qed.
  Lemma score_attainable : Trusted.Spec.scoreAttainable.
  Proof. exact maxScoreIsAttainable. Qed.
End Implementation.
