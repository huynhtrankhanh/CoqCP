From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import ArrayLengthFrame InternLengths RenameMemoLengths.
From stdpp Require Import numbers list.
Module ClassCertifyLengths.
Import ArrayLengthFrame.
Local Opaque funcdef_0__predicate funcdef_0__intern.
Theorem setness_ro watched : RenameMemoLengths.protected watched -> forall bs ns,
  array_ro watched (funcdef_0__setness bs ns).
Proof.
  intros Hprotected bs ns. pose proof (RenameMemoLengths.predicate_ro watched Hprotected) as Hpredicate.
  destruct Hprotected as [Hm [Hs [Hf [Hb [Hfs Hl]]]]].
  pose proof (InternLengths.intern_ro watched Hb Hfs Hl) as Hintern.
  unfold funcdef_0__setness. apply eliminate_ro. unfold funcdef_0__setness_body. ro.
Qed.
Theorem setness_length s bs ns observations final after watched : RenameMemoLengths.protected watched ->
  execObserved (funcdef_0__setness bs ns) (s,observations)=Some (tt,(final,after)) ->
  length (memory final watched)=length (memory s watched).
Proof. intro Hprotected. apply observed_preserves. now apply setness_ro. Qed.
End ClassCertifyLengths.
