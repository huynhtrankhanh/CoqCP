From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import EffectFrame PrintingFrame.
From stdpp Require Import numbers list.

Module ImmutableStorage.
Import EffectFrame.
(* The logical binding dictionary, its byte arena and immutable schema syntax
   are separate from scratch storage and the formula/class/history arenas. *)
Definition persistent_array watched :=
  arraydef_0__meta <> watched /\ arraydef_0__sipState <> watched /\
  arraydef_0__formulaBuckets <> watched /\ arraydef_0__formulaLinks <> watched /\
  arraydef_0__renameMemo <> watched /\ arraydef_0__renameMemoScratch <> watched /\
  arraydef_0__formulas <> watched /\ arraydef_0__classes <> watched /\
  arraydef_0__theorems <> watched /\ arraydef_0__frames <> watched /\
  arraydef_0__schemaValues <> watched /\ arraydef_0__schemaMarks <> watched /\
  arraydef_0__schemaArguments <> watched /\ arraydef_0__token <> watched /\ arraydef_0__printBuffer <> watched.
Lemma binding_array_persistent : persistent_array arraydef_0__bindings.
Proof. repeat split; discriminate. Qed.
Lemma name_array_persistent : persistent_array arraydef_0__names.
Proof. repeat split; discriminate. Qed.
Lemma schema_array_persistent : persistent_array arraydef_0__schemaNodes.
Proof. repeat split; discriminate. Qed.
Lemma print_ro {R} watched (code : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :
  arraydef_0__printBuffer <> watched ->
  array_ro watched (PrintingFrame.translate_print code).
Proof.
  intro Hname. induction code as [value|effect cont IH]; [constructor|].
  destruct effect as [effect|array slot|array slot value|array size zero].
  - cbn [PrintingFrame.translate_print translateArrays withArraysReturnValueDoBasicEffectArrayType array_ro].
    split; [destruct effect; constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [exact Hname|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [exact Hname|]. intro response. apply IH.
Qed.
#[local] Hint Resolve print_ro : effect_frames.
Theorem sipRound_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__sipRound bs ns).
Proof. unfold persistent_array in Hprotected. unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__sipWord bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (sipRound_ro watched Hprotected) as Hround. unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__formulaHash bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (sipRound_ro watched Hprotected) as Hround. pose proof (sipWord_ro watched Hprotected) as Hword.
  unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehash_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__rehashFormulas bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (formulaHash_ro watched Hprotected) as Hhash. unfold funcdef_0__rehashFormulas.
  apply eliminate_ro. unfold funcdef_0__rehashFormulas_body. ro.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__intern bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (formulaHash_ro watched Hprotected) as Hhash. pose proof (rehash_ro watched Hprotected) as Hresize.
  unfold funcdef_0__intern. apply eliminate_ro. unfold funcdef_0__intern_body. ro.
Qed.

Local Opaque funcdef_0__intern.
Theorem push_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__push bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__push. apply eliminate_ro. unfold funcdef_0__push_body. ro.
Qed.
Local Opaque funcdef_0__push.
Theorem tokenByte_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__tokenByte bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__readToken bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (tokenByte_ro watched Hprotected) as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__readNat bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (readToken_ro watched Hprotected) as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__lookup bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro.
Qed.
Local Opaque funcdef_0__lookup.
Theorem renameIndex_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameIndex bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__renameIndex. apply eliminate_ro. unfold funcdef_0__renameIndex_body. ro.
Qed.
Local Opaque funcdef_0__renameIndex.
Theorem renameCacheGet_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameCacheGet bs ns).
Proof. unfold persistent_array in Hprotected. pose proof (formulaHash_ro watched Hprotected) as Hhash. unfold funcdef_0__renameCacheGet. apply eliminate_ro. unfold funcdef_0__renameCacheGet_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem renameCacheGrow_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameCacheGrow bs ns).
Proof. unfold persistent_array in Hprotected. pose proof (formulaHash_ro watched Hprotected) as Hhash. unfold funcdef_0__renameCacheGrow. apply eliminate_ro. unfold funcdef_0__renameCacheGrow_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem renameCachePut_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__renameCachePut bs ns).
Proof. unfold persistent_array in Hprotected. pose proof (formulaHash_ro watched Hprotected) as Hhash. pose proof (renameCacheGrow_ro watched Hprotected) as Hgrow. unfold funcdef_0__renameCachePut. apply eliminate_ro. unfold funcdef_0__renameCachePut_body. ro. Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem rename_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__rename bs ns).
Proof. pose proof (renameCacheGet_ro watched Hprotected) as HrenameCacheGet.  pose proof (renameCachePut_ro watched Hprotected) as HrenameCachePut.  unfold persistent_array in Hprotected.
  pose proof (push_ro watched Hprotected) as Hdep0.
  pose proof (renameIndex_ro watched Hprotected) as Hdep1.
  pose proof (intern_ro watched Hprotected) as Hdep2.
  unfold funcdef_0__rename. apply eliminate_ro. unfold funcdef_0__rename_body. ro.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__predicate bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (rename_ro watched Hprotected) as Hdep0.
  pose proof (intern_ro watched Hprotected) as Hdep1.
  unfold funcdef_0__predicate. apply eliminate_ro. unfold funcdef_0__predicate_body. ro.
Qed.
Local Opaque funcdef_0__predicate.
Theorem classEqual_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__classEqual bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (predicate_ro watched Hprotected) as Hdep0.
  pose proof (intern_ro watched Hprotected) as Hdep1.
  unfold funcdef_0__classEqual. apply eliminate_ro. unfold funcdef_0__classEqual_body. ro.
Qed.
Local Opaque funcdef_0__classEqual.
Theorem classMember_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__classMember bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (rename_ro watched Hprotected) as Hdep0.
  pose proof (predicate_ro watched Hprotected) as Hdep1.
  pose proof (intern_ro watched Hprotected) as Hdep2.
  unfold funcdef_0__classMember. apply eliminate_ro. unfold funcdef_0__classMember_body. ro.
Qed.
Local Opaque funcdef_0__classMember.
Theorem setness_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__setness bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (predicate_ro watched Hprotected) as Hdep0.
  pose proof (intern_ro watched Hprotected) as Hdep1.
  unfold funcdef_0__setness. apply eliminate_ro. unfold funcdef_0__setness_body. ro.
Qed.
Local Opaque funcdef_0__setness.
Theorem axiom_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__axiom bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (rename_ro watched Hprotected) as Hdep0.
  pose proof (intern_ro watched Hprotected) as Hdep1.
  unfold funcdef_0__axiom. apply eliminate_ro. unfold funcdef_0__axiom_body. ro.
Qed.
Local Opaque funcdef_0__axiom.
Theorem schemaCheck_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__schemaCheck bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__schemaCheck. apply eliminate_ro. unfold funcdef_0__schemaCheck_body. ro.
Qed.
Local Opaque funcdef_0__schemaCheck.
Theorem schemaClass_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__schemaClass bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__schemaClass. apply eliminate_ro. unfold funcdef_0__schemaClass_body. ro.
Qed.
Local Opaque funcdef_0__schemaClass.
Theorem schemaShiftClass_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__schemaShiftClass bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (schemaClass_ro watched Hprotected) as Hdep0.
  pose proof (rename_ro watched Hprotected) as Hdep1.
  unfold funcdef_0__schemaShiftClass. apply eliminate_ro. unfold funcdef_0__schemaShiftClass_body. ro.
Qed.
Local Opaque funcdef_0__schemaShiftClass.
Theorem schemaMark_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__schemaMark bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__schemaMark. apply eliminate_ro. unfold funcdef_0__schemaMark_body. ro.
Qed.
Local Opaque funcdef_0__schemaMark.
Theorem schemaInstance_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__schemaInstance bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (schemaMark_ro watched Hprotected) as Hdep0.
  pose proof (schemaShiftClass_ro watched Hprotected) as Hdep1.
  pose proof (schemaClass_ro watched Hprotected) as Hdep2.
  pose proof (classEqual_ro watched Hprotected) as Hdep3.
  pose proof (classMember_ro watched Hprotected) as Hdep4.
  pose proof (intern_ro watched Hprotected) as Hdep5.
  pose proof (axiom_ro watched Hprotected) as Hdep6.
  unfold funcdef_0__schemaInstance. apply eliminate_ro. unfold funcdef_0__schemaInstance_body. ro.
Qed.
Local Opaque funcdef_0__schemaInstance.
Theorem ok_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__ok bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body.
  apply local_bind.
  - apply string_ro. intro ch. ro.
  - intros [].
    change (local_ro watched
      ((numberLocalGet _ _ _ vardef_0__ok_value >>= fun value =>
        liftToWithLocalVariables (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned
          (fun _ => false) (update (fun _ => 0%Z) vardef_0_PrintInt64_unsigned_num value))))
      >>= fun _ => writeChar _ _ _ (coerceInt 10 8) >>= fun _ =>
        flush _ _ _ >>= fun _ => Done _ _ _ tt)).
    apply local_bind.
    + apply local_bind; [ro|intro value; apply local_lift; apply print_ro; tauto].
    + intros []. ro.
Qed.
Local Opaque funcdef_0__ok.
Theorem no_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__no bs ns).
Proof. unfold persistent_array in Hprotected.
  unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro.
Qed.
Local Opaque funcdef_0__no.
Theorem appendTheorem_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__appendTheorem bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (ok_ro watched Hprotected) as H_ok.
  unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem modusPonens_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__modusPonens bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  pose proof (no_ro watched Hprotected) as H_no.
  unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro.
Qed.
Local Opaque funcdef_0__modusPonens.
Theorem generalize_ro watched (Hprotected : persistent_array watched) bs ns : array_ro watched (funcdef_0__generalize bs ns).
Proof. unfold persistent_array in Hprotected.
  pose proof (intern_ro watched Hprotected) as H_intern.
  pose proof (appendTheorem_ro watched Hprotected) as H_appendTheorem.
  unfold funcdef_0__generalize. apply eliminate_ro. unfold funcdef_0__generalize_body. ro.
Qed.
Local Opaque funcdef_0__generalize.
End ImmutableStorage.
