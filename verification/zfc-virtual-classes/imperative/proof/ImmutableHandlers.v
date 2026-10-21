From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import EffectFrame ImmutableStorage ObservedLocal CommandStructure.
From stdpp Require Import numbers list.

Module ImmutableHandlers.
Import EffectFrame ImmutableStorage.
Local Opaque funcdef_0__ok funcdef_0__no funcdef_0__intern funcdef_0__readNat
  funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize
  funcdef_0__classEqual funcdef_0__classMember funcdef_0__axiom.
Section LocalSemantics.
Context {V : Type} `{EqDecision V}.
Theorem local_observed_preserves watched
  (code : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) V) withLocalVariablesReturnValue unit)
  (f final : @Execution.Frame arrayIndex1 (arrayType _ environment1) V) observations after_observations :
  local_ro watched code -> ObservedLocal.execLocalObserved code (f,observations) = Some (tt,(final,after_observations)) ->
  memory (machine final) watched = memory (machine f) watched.
Proof.
  intros Hro Hrun. destruct f as [s bs ns].
  apply (EffectFrame.observed_preserves watched (eliminateLocalVariables bs ns code) s observations tt (machine final) after_observations).
  - now apply eliminate_ro.
  - rewrite ObservedLocal.eliminate_correct, Hrun. reflexivity.
Qed.
End LocalSemantics.
Theorem handler_1_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_1 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_1. ro.
Qed.
Theorem handler_2_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_2 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_2. ro.
Qed.
Theorem handler_3_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_3 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_3. ro.
Qed.
Theorem handler_4_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_4 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_4. ro.
Qed.
Theorem handler_5_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_5 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_5. ro.
Qed.
Theorem handler_6_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_6 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_6. ro.
Qed.
Theorem handler_7_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_7 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_7. ro.
Qed.
Theorem handler_8_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_8 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_8. ro.
Qed.
Theorem handler_11_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_11 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_11. ro.
Qed.
Theorem handler_12_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_12 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_12. ro.
Qed.
Theorem handler_13_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_13 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_13. ro.
Qed.
Theorem handler_16_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_16 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_16. ro.
Qed.
Theorem handler_17_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_17 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_17. ro.
Qed.
Theorem handler_18_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_18 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_18. ro.
Qed.
Theorem handler_19_ro watched (Hprotected : persistent_array watched) : local_ro watched (CommandStructure.handler_19 funcdef_0__readNat).
Proof.
  pose proof (readNat_ro watched Hprotected) as H_readNat.
  pose proof (ok_ro watched Hprotected) as H_ok.
  pose proof (no_ro watched Hprotected) as H_no.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (modusPonens_ro watched Hprotected) as H_modusPonens.
  pose proof (generalize_ro watched Hprotected) as H_generalize.
  pose proof (classEqual_ro watched Hprotected) as H_classEqual.
  pose proof (classMember_ro watched Hprotected) as H_classMember.
  pose proof (axiom_ro watched Hprotected) as H_axiom.
  unfold persistent_array in Hprotected. unfold CommandStructure.handler_19. ro.
Qed.
End ImmutableHandlers.
