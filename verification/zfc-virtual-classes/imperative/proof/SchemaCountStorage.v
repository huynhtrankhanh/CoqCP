From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import MetaCellFrame PrintingFrame.
From stdpp Require Import numbers list.
Module SchemaCountStorage.
Import MetaCellFrame.
Lemma print_ro {R} (code : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :
  array_ro 16%nat (PrintingFrame.translate_print code).
Proof.
  induction code as [value|effect cont IH]; [constructor|].
  destruct effect as [effect|array slot|array slot value|array size zero].
  - cbn [PrintingFrame.translate_print translateArrays withArraysReturnValueDoBasicEffectArrayType array_ro].
    split; [destruct effect; constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [constructor|]. intro response. apply IH.
  - destruct array. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split; [discriminate|]. intro response. apply IH.
Qed.
#[local] Hint Resolve print_ro : cell_frames.
Theorem sipRound_ro bs ns : array_ro 16%nat (funcdef_0__sipRound bs ns).
Proof.  unfold funcdef_0__sipRound. apply eliminate_ro. unfold funcdef_0__sipRound_body. ro. Qed.
Local Opaque funcdef_0__sipRound.
Theorem sipWord_ro bs ns : array_ro 16%nat (funcdef_0__sipWord bs ns).
Proof.
  pose proof (sipRound_ro) as Hround. unfold funcdef_0__sipWord. apply eliminate_ro. unfold funcdef_0__sipWord_body. ro.
Qed.
Local Opaque funcdef_0__sipWord.
Theorem formulaHash_ro bs ns : array_ro 16%nat (funcdef_0__formulaHash bs ns).
Proof.
  pose proof (sipRound_ro) as Hround. pose proof (sipWord_ro) as Hword.
  unfold funcdef_0__formulaHash. apply eliminate_ro. unfold funcdef_0__formulaHash_body. ro.
Qed.
Local Opaque funcdef_0__formulaHash.
Theorem rehash_ro bs ns : array_ro 16%nat (funcdef_0__rehashFormulas bs ns).
Proof.
  pose proof (formulaHash_ro) as Hhash. unfold funcdef_0__rehashFormulas.
  apply eliminate_ro. unfold funcdef_0__rehashFormulas_body. ro.
Qed.
Local Opaque funcdef_0__rehashFormulas.
Theorem intern_ro bs ns : array_ro 16%nat (funcdef_0__intern bs ns).
Proof.
  pose proof (formulaHash_ro) as Hhash. pose proof (rehash_ro) as Hresize.
  unfold funcdef_0__intern. apply eliminate_ro. unfold funcdef_0__intern_body. ro.
Qed.

Local Opaque funcdef_0__intern.
Theorem push_ro bs ns : array_ro 16%nat (funcdef_0__push bs ns).
Proof.
  unfold funcdef_0__push. apply eliminate_ro. unfold funcdef_0__push_body. ro.
Qed.
Local Opaque funcdef_0__push.
Theorem tokenByte_ro bs ns : array_ro 16%nat (funcdef_0__tokenByte bs ns).
Proof.
  unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro.
Qed.
Local Opaque funcdef_0__tokenByte.
Theorem readToken_ro bs ns : array_ro 16%nat (funcdef_0__readToken bs ns).
Proof.
  pose proof (tokenByte_ro) as Hdep0.
  unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro.
Qed.
Local Opaque funcdef_0__readToken.
Theorem readNat_ro bs ns : array_ro 16%nat (funcdef_0__readNat bs ns).
Proof.
  pose proof (readToken_ro) as Hdep0.
  unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro.
Qed.
Local Opaque funcdef_0__readNat.
Theorem lookup_ro bs ns : array_ro 16%nat (funcdef_0__lookup bs ns).
Proof.
  unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro.
Qed.
Local Opaque funcdef_0__lookup.
Theorem renameIndex_ro bs ns : array_ro 16%nat (funcdef_0__renameIndex bs ns).
Proof.
  unfold funcdef_0__renameIndex. apply eliminate_ro. unfold funcdef_0__renameIndex_body. ro.
Qed.
Local Opaque funcdef_0__renameIndex.
Theorem renameCacheGet_ro bs ns : array_ro 16%nat (funcdef_0__renameCacheGet bs ns).
Proof. pose proof (formulaHash_ro) as Hhash. unfold funcdef_0__renameCacheGet. apply eliminate_ro. unfold funcdef_0__renameCacheGet_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGet.
Theorem renameCacheGrow_ro bs ns : array_ro 16%nat (funcdef_0__renameCacheGrow bs ns).
Proof. pose proof (formulaHash_ro) as Hhash. unfold funcdef_0__renameCacheGrow. apply eliminate_ro. unfold funcdef_0__renameCacheGrow_body. ro. Qed.
Local Opaque funcdef_0__renameCacheGrow.
Theorem renameCachePut_ro bs ns : array_ro 16%nat (funcdef_0__renameCachePut bs ns).
Proof. pose proof (formulaHash_ro) as Hhash. pose proof (renameCacheGrow_ro) as Hgrow. unfold funcdef_0__renameCachePut. apply eliminate_ro. unfold funcdef_0__renameCachePut_body. ro. Qed.
Local Opaque funcdef_0__renameCachePut.
Theorem rename_ro bs ns : array_ro 16%nat (funcdef_0__rename bs ns).
Proof. pose proof (renameCacheGet_ro) as HrenameCacheGet.  pose proof (renameCachePut_ro) as HrenameCachePut.
  pose proof (push_ro) as Hdep0.
  pose proof (renameIndex_ro) as Hdep1.
  pose proof (intern_ro) as Hdep2.
  unfold funcdef_0__rename. apply eliminate_ro. unfold funcdef_0__rename_body. ro.
Qed.
Local Opaque funcdef_0__rename.
Theorem predicate_ro bs ns : array_ro 16%nat (funcdef_0__predicate bs ns).
Proof.
  pose proof (rename_ro) as Hdep0.
  pose proof (intern_ro) as Hdep1.
  unfold funcdef_0__predicate. apply eliminate_ro. unfold funcdef_0__predicate_body. ro.
Qed.
Local Opaque funcdef_0__predicate.
Theorem classEqual_ro bs ns : array_ro 16%nat (funcdef_0__classEqual bs ns).
Proof.
  pose proof (predicate_ro) as Hdep0.
  pose proof (intern_ro) as Hdep1.
  unfold funcdef_0__classEqual. apply eliminate_ro. unfold funcdef_0__classEqual_body. ro.
Qed.
Local Opaque funcdef_0__classEqual.
Theorem classMember_ro bs ns : array_ro 16%nat (funcdef_0__classMember bs ns).
Proof.
  pose proof (rename_ro) as Hdep0.
  pose proof (predicate_ro) as Hdep1.
  pose proof (intern_ro) as Hdep2.
  unfold funcdef_0__classMember. apply eliminate_ro. unfold funcdef_0__classMember_body. ro.
Qed.
Local Opaque funcdef_0__classMember.
Theorem setness_ro bs ns : array_ro 16%nat (funcdef_0__setness bs ns).
Proof.
  pose proof (predicate_ro) as Hdep0.
  pose proof (intern_ro) as Hdep1.
  unfold funcdef_0__setness. apply eliminate_ro. unfold funcdef_0__setness_body. ro.
Qed.
Local Opaque funcdef_0__setness.
Theorem axiom_ro bs ns : array_ro 16%nat (funcdef_0__axiom bs ns).
Proof.
  pose proof (rename_ro) as Hdep0.
  pose proof (intern_ro) as Hdep1.
  unfold funcdef_0__axiom. apply eliminate_ro. unfold funcdef_0__axiom_body. ro.
Qed.
Local Opaque funcdef_0__axiom.
Theorem schemaCheck_ro bs ns : array_ro 16%nat (funcdef_0__schemaCheck bs ns).
Proof.
  unfold funcdef_0__schemaCheck. apply eliminate_ro. unfold funcdef_0__schemaCheck_body. ro.
Qed.
Local Opaque funcdef_0__schemaCheck.
Theorem schemaClass_ro bs ns : array_ro 16%nat (funcdef_0__schemaClass bs ns).
Proof.
  unfold funcdef_0__schemaClass. apply eliminate_ro. unfold funcdef_0__schemaClass_body. ro.
Qed.
Local Opaque funcdef_0__schemaClass.
Theorem schemaShiftClass_ro bs ns : array_ro 16%nat (funcdef_0__schemaShiftClass bs ns).
Proof.
  pose proof (schemaClass_ro) as Hdep0.
  pose proof (rename_ro) as Hdep1.
  unfold funcdef_0__schemaShiftClass. apply eliminate_ro. unfold funcdef_0__schemaShiftClass_body. ro.
Qed.
Local Opaque funcdef_0__schemaShiftClass.
Theorem schemaMark_ro bs ns : array_ro 16%nat (funcdef_0__schemaMark bs ns).
Proof.
  unfold funcdef_0__schemaMark. apply eliminate_ro. unfold funcdef_0__schemaMark_body. ro.
Qed.
Local Opaque funcdef_0__schemaMark.
Theorem schemaInstance_ro bs ns : array_ro 16%nat (funcdef_0__schemaInstance bs ns).
Proof.
  pose proof (schemaMark_ro) as Hdep0.
  pose proof (schemaShiftClass_ro) as Hdep1.
  pose proof (schemaClass_ro) as Hdep2.
  pose proof (classEqual_ro) as Hdep3.
  pose proof (classMember_ro) as Hdep4.
  pose proof (intern_ro) as Hdep5.
  pose proof (axiom_ro) as Hdep6.
  unfold funcdef_0__schemaInstance. apply eliminate_ro. unfold funcdef_0__schemaInstance_body. ro.
Qed.
Local Opaque funcdef_0__schemaInstance.
Theorem ok_ro bs ns : array_ro 16%nat (funcdef_0__ok bs ns).
Proof.
  unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body.
  apply local_bind.
  - apply string_ro. intro ch. ro.
  - intros [].
    change (local_ro 16%nat
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
Theorem no_ro bs ns : array_ro 16%nat (funcdef_0__no bs ns).
Proof.
  unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro.
Qed.
Local Opaque funcdef_0__no.
Theorem appendTheorem_ro bs ns : array_ro 16%nat (funcdef_0__appendTheorem bs ns).
Proof.
  pose proof (ok_ro) as H_ok.
  unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro.
Qed.
Local Opaque funcdef_0__appendTheorem.
Theorem modusPonens_ro bs ns : array_ro 16%nat (funcdef_0__modusPonens bs ns).
Proof.
  pose proof (appendTheorem_ro) as H_appendTheorem.
  pose proof (no_ro) as H_no.
  unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro.
Qed.
Local Opaque funcdef_0__modusPonens.
Theorem generalize_ro bs ns : array_ro 16%nat (funcdef_0__generalize bs ns).
Proof.
  pose proof (intern_ro) as H_intern.
  pose proof (appendTheorem_ro) as H_appendTheorem.
  unfold funcdef_0__generalize. apply eliminate_ro. unfold funcdef_0__generalize_body. ro.
Qed.
Local Opaque funcdef_0__generalize.
Theorem bindName_ro bs ns : array_ro 16%nat (funcdef_0__bindName bs ns).
Proof.
  pose proof lookup_ro as Hlookup. pose proof ok_ro as Hok. pose proof no_ro as Hno.
  unfold funcdef_0__bindName. apply eliminate_ro. unfold funcdef_0__bindName_body. ro.
Qed.
End SchemaCountStorage.
