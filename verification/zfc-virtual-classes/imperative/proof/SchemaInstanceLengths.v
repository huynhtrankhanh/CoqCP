From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayLengthFrame SchemaEvaluationFrames RenameMemoLengths AxiomLengths InternLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaInstanceLengths.
Import IndexExecution SipHashExecution.
Definition protected watched := SchemaEvaluationFrames.protected watched /\ watched<>arraydef_0__schemaMarks /\ watched<>arraydef_0__schemaValues.
Lemma mark_lengths watched bs ns : ArrayLengthFrame.array_ro watched (funcdef_0__schemaMark bs ns).
Proof. unfold funcdef_0__schemaMark. apply ArrayLengthFrame.eliminate_ro. unfold funcdef_0__schemaMark_body. ArrayLengthFrame.ro. Qed.
Local Opaque funcdef_0__schemaMark funcdef_0__schemaClass funcdef_0__schemaShiftClass funcdef_0__classEqual funcdef_0__classMember funcdef_0__intern funcdef_0__axiom.
Theorem generated_ro watched : protected watched -> forall bs ns,
 ArrayLengthFrame.array_ro watched (funcdef_0__schemaInstance bs ns).
Proof.
 intros [Hprotected [Hmarks Hvalues]] bs ns.
 pose proof (mark_lengths watched) as Hmark.
 pose proof (SchemaEvaluationFrames.schemaShift_lengths watched Hprotected) as Hshift.
 pose proof (SchemaEvaluationFrames.schemaClass_lengths watched (proj2 Hprotected)) as Hclass.
 pose proof (SchemaEvaluationFrames.classEqual_lengths watched (proj1 Hprotected)) as Hequal.
 pose proof (SchemaEvaluationFrames.classMember_lengths watched (proj1 Hprotected)) as Hmember.
 pose proof (AxiomLengths.axiom_ro watched (proj1 Hprotected)) as Haxiom.
 destruct Hprotected as [[Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]] Hclasses].
 pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
 unfold funcdef_0__schemaInstance. apply ArrayLengthFrame.eliminate_ro. unfold funcdef_0__schemaInstance_body. ArrayLengthFrame.ro.
Qed.
Theorem generated watched s bs ns final observations after : protected watched ->
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,after)) ->
 length (memory final watched)=length (memory s watched).
Proof. intros Hprotected Hrun. exact (ArrayLengthFrame.observed_preserves watched _ s observations tt final after (generated_ro watched Hprotected bs ns) Hrun). Qed.
Lemma meta_protected : protected arraydef_0__meta.
Proof. unfold protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected. repeat split;discriminate. Qed.
Lemma print_protected : protected arraydef_0__printBuffer.
Proof. unfold protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected. repeat split;discriminate. Qed.
End SchemaInstanceLengths.
