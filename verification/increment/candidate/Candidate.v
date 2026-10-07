From CoqCP Require Import Options.

Require Trusted.Spec.

Module Implementation.
  Definition program : nat -> nat := S.
  Lemma correct : Trusted.Spec.required program.
  Proof. intro input. reflexivity. Qed.
End Implementation.
