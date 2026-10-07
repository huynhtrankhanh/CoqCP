From CoqCP Require Import Options.
From Submission Require Import PermutedBinaryStringsProtocol PermutedBinaryStringsEndToEnd.
Require Trusted.Spec.

Module Implementation.
  Definition program : Trusted.Spec.Program :=
    Trusted.Spec.program.
  Lemma correct : Trusted.Spec.required program.
  Proof. split; [reflexivity | exact generated_end_to_end]. Qed.
End Implementation.
