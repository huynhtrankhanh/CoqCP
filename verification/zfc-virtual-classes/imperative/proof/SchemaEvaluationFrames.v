From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal SchemaEvaluation SchemaPair
 ArrayLengthFrame EffectFrame MetaCellFrame InternLengths RenameMemoLengths AxiomLengths RenameStorage AxiomStorage.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationFrames.
Import IndexExecution SipHashExecution ObservedLocal.
Definition protected watched := RenameMemoLengths.protected watched /\ watched<>arraydef_0__classes.
Theorem local_lengths {V} `{EqDecision V} {R} watched
 (code:Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V) withLocalVariablesReturnValue R)
 f observations result final after :
 ArrayLengthFrame.local_ro watched code -> execLocalObserved code (f,observations)=Some (result,(final,after)) ->
 length (memory (machine final) watched)=length (memory (machine f) watched).
Proof.
 intros Hro Hrun. destruct f as [s bs ns].
 set (discard:=code >>= fun _=>Done _ _ _ tt).
 assert (Hdiscard:ArrayLengthFrame.local_ro watched discard).
 { apply ArrayLengthFrame.local_bind;[exact Hro|]. intro;exact I. }
 assert (Hexec:execObserved (eliminateLocalVariables bs ns discard) (s,observations)=Some (tt,(machine final,after))).
 { rewrite eliminate_correct. unfold discard. rewrite local_bind,Hrun. reflexivity. }
 exact (ArrayLengthFrame.observed_preserves watched _ s observations tt (machine final) after
   (ArrayLengthFrame.eliminate_ro watched discard bs ns Hdiscard) Hexec).
Qed.
Theorem local_arrays {V} `{EqDecision V} {R} watched
 (code:Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V) withLocalVariablesReturnValue R)
 f observations result final after :
 EffectFrame.local_ro watched code -> execLocalObserved code (f,observations)=Some (result,(final,after)) ->
 memory (machine final) watched=memory (machine f) watched.
Proof.
 intros Hro Hrun. destruct f as [s bs ns].
 set (discard:=code >>= fun _=>Done _ _ _ tt).
 assert (Hdiscard:EffectFrame.local_ro watched discard).
 { apply EffectFrame.local_bind;[exact Hro|]. intro;exact I. }
 assert (Hexec:execObserved (eliminateLocalVariables bs ns discard) (s,observations)=Some (tt,(machine final,after))).
 { rewrite eliminate_correct. unfold discard. rewrite local_bind,Hrun. reflexivity. }
 exact (EffectFrame.observed_preserves watched _ s observations tt (machine final) after
   (EffectFrame.eliminate_ro watched discard bs ns Hdiscard) Hexec).
Qed.
Theorem schemaClass_lengths watched : watched<>arraydef_0__classes -> forall bs ns,
 ArrayLengthFrame.array_ro watched (funcdef_0__schemaClass bs ns).
Proof. intros Hclass bs ns. unfold funcdef_0__schemaClass. apply ArrayLengthFrame.eliminate_ro. unfold funcdef_0__schemaClass_body. ArrayLengthFrame.ro. Qed.
Local Opaque funcdef_0__schemaClass funcdef_0__intern funcdef_0__rename funcdef_0__predicate funcdef_0__axiom.
Theorem schemaShift_lengths watched : protected watched -> forall bs ns,
 ArrayLengthFrame.array_ro watched (funcdef_0__schemaShiftClass bs ns).
Proof.
 intros [Hrename Hclass] bs ns.
 pose proof (schemaClass_lengths watched Hclass) as Hschema.
 pose proof (RenameMemoLengths.rename_ro watched Hrename) as Hrename_ro.
 unfold funcdef_0__schemaShiftClass. apply ArrayLengthFrame.eliminate_ro. unfold funcdef_0__schemaShiftClass_body. ArrayLengthFrame.ro.
Qed.
Theorem classEqual_lengths watched : RenameMemoLengths.protected watched -> forall bs ns,
 ArrayLengthFrame.array_ro watched (funcdef_0__classEqual bs ns).
Proof.
 intros Hprotected bs ns.
 pose proof (RenameMemoLengths.predicate_ro watched Hprotected) as Hpredicate.
 destruct Hprotected as [Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]].
 pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
 unfold funcdef_0__classEqual. apply ArrayLengthFrame.eliminate_ro. unfold funcdef_0__classEqual_body. ArrayLengthFrame.ro.
Qed.
Theorem classMember_lengths watched : RenameMemoLengths.protected watched -> forall bs ns,
 ArrayLengthFrame.array_ro watched (funcdef_0__classMember bs ns).
Proof.
 intros Hprotected bs ns.
 pose proof (RenameMemoLengths.predicate_ro watched Hprotected) as Hpredicate.
 pose proof (RenameMemoLengths.rename_ro watched Hprotected) as Hrename.
 destruct Hprotected as [Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]].
 pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
 unfold funcdef_0__classMember. apply ArrayLengthFrame.eliminate_ro. unfold funcdef_0__classMember_body. ArrayLengthFrame.ro.
Qed.
Local Opaque funcdef_0__schemaShiftClass funcdef_0__classEqual funcdef_0__classMember.
Theorem selected_ro which width remaining outer_remaining watched : protected watched ->
 ArrayLengthFrame.local_ro watched (dropWithinLoop (SchemaPair.selected which width remaining outer_remaining)).
Proof.
 intro Hprotected.
 pose proof (schemaShift_lengths watched Hprotected) as Hshift.
 pose proof (schemaClass_lengths watched (proj2 Hprotected)) as Hclass.
 pose proof (classEqual_lengths watched (proj1 Hprotected)) as Hequal.
 pose proof (classMember_lengths watched (proj1 Hprotected)) as Hmember.
 pose proof (AxiomLengths.axiom_ro watched (proj1 Hprotected)) as Haxiom.
 destruct Hprotected as [[Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]] Hclasses].
 pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
 destruct which;cbn [SchemaPair.selected];unfold SchemaPair.raw_meta,SchemaPair.raw_literal,SchemaPair.raw_abstract,
 SchemaPair.raw_binary,SchemaPair.raw_all,SchemaPair.raw_axiom;ArrayLengthFrame.ro.
Qed.
Theorem selected_lengths which width remaining outer_remaining watched f observations final after : protected watched ->
 execLocalObserved (dropWithinLoop (SchemaPair.selected which width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,after)) ->
 length (memory (machine final) watched)=length (memory (machine f) watched).
Proof. intros Hprotected Hrun. eapply local_lengths;[apply selected_ro;exact Hprotected|exact Hrun]. Qed.
Definition persistent watched := RenameStorage.Arrays.persistent_array watched /\ arraydef_0__classes<>watched.
Local Transparent funcdef_0__schemaClass.
Theorem schemaClass_arrays watched : arraydef_0__meta<>watched -> arraydef_0__classes<>watched -> forall bs ns,
 EffectFrame.array_ro watched (funcdef_0__schemaClass bs ns).
Proof. intros Hmeta Hclass bs ns. unfold funcdef_0__schemaClass. apply EffectFrame.eliminate_ro. unfold funcdef_0__schemaClass_body. EffectFrame.ro. Qed.
Local Opaque funcdef_0__schemaClass.
Local Transparent funcdef_0__schemaShiftClass.
Theorem schemaShift_arrays watched : persistent watched -> forall bs ns,
 EffectFrame.array_ro watched (funcdef_0__schemaShiftClass bs ns).
Proof.
 intros [Hprotected Hclass] bs ns. pose proof (schemaClass_arrays watched (proj1 Hprotected) Hclass) as Hschema.
 pose proof (RenameStorage.Arrays.rename_ro watched Hprotected) as Hrename.
 unfold RenameStorage.Arrays.persistent_array in Hprotected.
 unfold funcdef_0__schemaShiftClass. apply EffectFrame.eliminate_ro. unfold funcdef_0__schemaShiftClass_body. EffectFrame.ro.
Qed.
Local Opaque funcdef_0__schemaShiftClass.
Local Transparent funcdef_0__classEqual.
Theorem classEqual_arrays watched : RenameStorage.Arrays.persistent_array watched -> forall bs ns,
 EffectFrame.array_ro watched (funcdef_0__classEqual bs ns).
Proof.
 intros Hprotected bs ns.
 pose proof (RenameStorage.Arrays.predicate_ro watched Hprotected) as Hpredicate.
 pose proof (RenameStorage.Arrays.intern_ro watched Hprotected) as Hintern.
 unfold RenameStorage.Arrays.persistent_array in Hprotected.
 unfold funcdef_0__classEqual. apply EffectFrame.eliminate_ro. unfold funcdef_0__classEqual_body. EffectFrame.ro.
Qed.
Local Opaque funcdef_0__classEqual.
Local Transparent funcdef_0__classMember.
Theorem classMember_arrays watched : RenameStorage.Arrays.persistent_array watched -> forall bs ns,
 EffectFrame.array_ro watched (funcdef_0__classMember bs ns).
Proof.
 intros Hprotected bs ns.
 pose proof (RenameStorage.Arrays.predicate_ro watched Hprotected) as Hpredicate.
 pose proof (RenameStorage.Arrays.rename_ro watched Hprotected) as Hrename.
 pose proof (RenameStorage.Arrays.intern_ro watched Hprotected) as Hintern.
 unfold RenameStorage.Arrays.persistent_array in Hprotected.
 unfold funcdef_0__classMember. apply EffectFrame.eliminate_ro. unfold funcdef_0__classMember_body. EffectFrame.ro.
Qed.
Local Opaque funcdef_0__classMember.
Theorem selected_array_ro which width remaining outer_remaining watched : persistent watched ->
 EffectFrame.local_ro watched (dropWithinLoop (SchemaPair.selected which width remaining outer_remaining)).
Proof.
 intro Hprotected.
 pose proof (schemaShift_arrays watched Hprotected) as Hshift.
 pose proof (schemaClass_arrays watched (proj1 (proj1 Hprotected)) (proj2 Hprotected)) as Hclass.
 pose proof (classEqual_arrays watched (proj1 Hprotected)) as Hequal.
 pose proof (classMember_arrays watched (proj1 Hprotected)) as Hmember.
 pose proof (AxiomStorage.arrays_ro watched (proj1 Hprotected)) as Haxiom.
 pose proof (RenameStorage.Arrays.intern_ro watched (proj1 Hprotected)) as Hintern.
 destruct Hprotected as [Hprotected Hclasses]. unfold RenameStorage.Arrays.persistent_array in Hprotected.
 destruct which;cbn [SchemaPair.selected];unfold SchemaPair.raw_meta,SchemaPair.raw_literal,SchemaPair.raw_abstract,
 SchemaPair.raw_binary,SchemaPair.raw_all,SchemaPair.raw_axiom;EffectFrame.ro.
Qed.
Theorem selected_arrays which width remaining outer_remaining watched f observations final after : persistent watched ->
 execLocalObserved (dropWithinLoop (SchemaPair.selected which width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,after)) ->
 memory (machine final) watched=memory (machine f) watched.
Proof. intros Hprotected Hrun. eapply local_arrays;[apply selected_array_ro;exact Hprotected|exact Hrun]. Qed.
Theorem marked_length_ro width remaining outer_remaining watched : protected watched ->
 ArrayLengthFrame.local_ro watched (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)).
Proof.
 intro Hprotected.
 pose proof (schemaShift_lengths watched Hprotected) as Hshift.
 pose proof (schemaClass_lengths watched (proj2 Hprotected)) as Hclass.
 pose proof (classEqual_lengths watched (proj1 Hprotected)) as Hequal.
 pose proof (classMember_lengths watched (proj1 Hprotected)) as Hmember.
 pose proof (AxiomLengths.axiom_ro watched (proj1 Hprotected)) as Haxiom.
 destruct Hprotected as [[Hmemo [Hscratch [Hframes [Hbuckets [Hformulas Hlinks]]]]] Hclasses].
 pose proof (InternLengths.intern_ro watched Hbuckets Hformulas Hlinks) as Hintern.
 unfold SchemaEvaluation.marked_body. ArrayLengthFrame.ro.
Qed.
Theorem marked_lengths width remaining outer_remaining watched f observations final after : protected watched ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,after)) ->
 length (memory (machine final) watched)=length (memory (machine f) watched).
Proof. intros Hprotected Hrun. eapply local_lengths;[apply marked_length_ro;exact Hprotected|exact Hrun]. Qed.
Theorem marked_array_ro width remaining outer_remaining watched : persistent watched -> arraydef_0__schemaValues<>watched ->
 EffectFrame.local_ro watched (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)).
Proof.
 intros Hprotected Hvalues.
 pose proof (schemaShift_arrays watched Hprotected) as Hshift.
 pose proof (schemaClass_arrays watched (proj1 (proj1 Hprotected)) (proj2 Hprotected)) as Hclass.
 pose proof (classEqual_arrays watched (proj1 Hprotected)) as Hequal.
 pose proof (classMember_arrays watched (proj1 Hprotected)) as Hmember.
 pose proof (AxiomStorage.arrays_ro watched (proj1 Hprotected)) as Haxiom.
 pose proof (RenameStorage.Arrays.intern_ro watched (proj1 Hprotected)) as Hintern.
 destruct Hprotected as [Hprotected Hclasses]. unfold RenameStorage.Arrays.persistent_array in Hprotected.
 unfold SchemaEvaluation.marked_body. EffectFrame.ro.
Qed.
Theorem marked_arrays width remaining outer_remaining watched f observations final after : persistent watched -> arraydef_0__schemaValues<>watched ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.marked_body width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(final,after)) ->
 memory (machine final) watched=memory (machine f) watched.
Proof. intros Hprotected Hvalues Hrun. eapply local_arrays;[apply marked_array_ro;assumption|exact Hrun]. Qed.
End SchemaEvaluationFrames.
