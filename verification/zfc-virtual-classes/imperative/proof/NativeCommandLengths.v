From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayLengthFrame PrintingFrame InternLengths RenameMemoLengths
 SchemaEvaluationFrames SchemaInstanceLengths AxiomLengths ClassCertifyLengths.
From Stdlib Require Import Lists.List Strings.String ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeCommandLengths.
Import IndexExecution SipHashExecution ArrayLengthFrame.
Definition protected watched := SchemaInstanceLengths.protected watched /\
 watched<>arraydef_0__names /\ watched<>arraydef_0__bindings /\ watched<>arraydef_0__theorems /\
 watched<>arraydef_0__schemaNodes /\ watched<>arraydef_0__schemaArguments.
Lemma print_source bs ns : array_ro arraydef_0_PrintInt64_buffer (funcdef_0_PrintInt64_unsigned bs ns).
Proof. unfold funcdef_0_PrintInt64_unsigned. apply eliminate_ro. unfold funcdef_0_PrintInt64_unsigned_body. ro. Qed.
Lemma translated_print {R} watched (code:Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue R) :
 array_ro arraydef_0_PrintInt64_buffer code -> array_ro watched (PrintingFrame.translate_print code).
Proof.
 intro Hro. induction code as [value|effect cont IH];[constructor|]. destruct Hro as [Hsafe Hcont].
 destruct effect as [effect|name slot|name slot value|name size zero].
 - cbn [PrintingFrame.translate_print translateArrays withArraysReturnValueDoBasicEffectArrayType array_ro].
   split;[destruct effect;constructor|]. intro response. apply IH,Hcont.
 - destruct name. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split;[constructor|]. intro response;apply IH,Hcont.
 - destruct name. cbn [PrintingFrame.translate_print translateArrays Action_rect array_ro]. split;[constructor|]. intro response;apply IH,Hcont.
 - destruct name. contradiction Hsafe;reflexivity.
Qed.
Lemma print_ro watched bs ns : array_ro watched (PrintingFrame.translate_print (funcdef_0_PrintInt64_unsigned bs ns)).
Proof. apply translated_print,print_source. Qed.
#[local] Hint Resolve print_ro : array_length_frames.
Lemma tokenByte_ro watched bs ns : array_ro watched (funcdef_0__tokenByte bs ns).
Proof. unfold funcdef_0__tokenByte. apply eliminate_ro. unfold funcdef_0__tokenByte_body. ro. Qed.
Local Opaque funcdef_0__tokenByte.
Lemma readToken_ro watched bs ns : array_ro watched (funcdef_0__readToken bs ns).
Proof. pose proof (tokenByte_ro watched) as H_tokenByte. unfold funcdef_0__readToken. apply eliminate_ro. unfold funcdef_0__readToken_body. ro. Qed.
Local Opaque funcdef_0__readToken.
Lemma readNat_ro watched bs ns : array_ro watched (funcdef_0__readNat bs ns).
Proof. pose proof (readToken_ro watched) as H_readToken. unfold funcdef_0__readNat. apply eliminate_ro. unfold funcdef_0__readNat_body. ro. Qed.
Local Opaque funcdef_0__readNat.
Lemma lookup_ro watched bs ns : array_ro watched (funcdef_0__lookup bs ns).
Proof. unfold funcdef_0__lookup. apply eliminate_ro. unfold funcdef_0__lookup_body. ro. Qed.
Local Opaque funcdef_0__lookup.
Lemma ok_ro watched bs ns : array_ro watched (funcdef_0__ok bs ns).
Proof. unfold funcdef_0__ok. apply eliminate_ro. unfold funcdef_0__ok_body. ro. Qed.
Local Opaque funcdef_0__ok.
Lemma no_ro watched bs ns : array_ro watched (funcdef_0__no bs ns).
Proof. unfold funcdef_0__no. apply eliminate_ro. unfold funcdef_0__no_body. ro. Qed.
Local Opaque funcdef_0__no.
Local Opaque funcdef_0__intern.
Section Protected.
Context (watched:arrayIndex1) (Hprotected:protected watched).
Ltac facts := let H:=fresh in pose proof Hprotected as H;
 unfold protected,SchemaInstanceLengths.protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected in H;
 decompose [and] H;clear H.
Lemma bindName_ro bs ns : array_ro watched (funcdef_0__bindName bs ns).
Proof. pose proof (lookup_ro watched) as H_lookup. pose proof (ok_ro watched) as H_ok. pose proof (no_ro watched) as H_no. facts. unfold funcdef_0__bindName. apply eliminate_ro. unfold funcdef_0__bindName_body. ro. Qed.
Local Opaque funcdef_0__bindName.
Lemma appendTheorem_ro bs ns : array_ro watched (funcdef_0__appendTheorem bs ns).
Proof. pose proof (ok_ro watched) as H_ok. facts. unfold funcdef_0__appendTheorem. apply eliminate_ro. unfold funcdef_0__appendTheorem_body. ro. Qed.
Local Opaque funcdef_0__appendTheorem.
Lemma modusPonens_ro bs ns : array_ro watched (funcdef_0__modusPonens bs ns).
Proof. pose proof (appendTheorem_ro) as H_appendTheorem. pose proof (no_ro watched) as H_no. facts. unfold funcdef_0__modusPonens. apply eliminate_ro. unfold funcdef_0__modusPonens_body. ro. Qed.
Local Opaque funcdef_0__modusPonens.
Lemma generalize_ro bs ns : array_ro watched (funcdef_0__generalize bs ns).
Proof. pose proof (appendTheorem_ro) as H_appendTheorem. facts. pose proof (InternLengths.intern_ro watched ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hintern. unfold funcdef_0__generalize. apply eliminate_ro. unfold funcdef_0__generalize_body. ro. Qed.
Local Opaque funcdef_0__generalize.
Lemma schemaCheck_ro bs ns : array_ro watched (funcdef_0__schemaCheck bs ns).
Proof. facts. unfold funcdef_0__schemaCheck. apply eliminate_ro. unfold funcdef_0__schemaCheck_body. ro. Qed.
Local Opaque funcdef_0__schemaCheck.
Lemma schemaNode_ro bs ns : array_ro watched (funcdef_0__schemaNode bs ns).
Proof. pose proof (schemaCheck_ro) as H_schemaCheck. pose proof (ok_ro watched) as Hok. pose proof (no_ro watched) as Hno. facts. unfold funcdef_0__schemaNode. apply eliminate_ro. unfold funcdef_0__schemaNode_body. ro. Qed.
Local Opaque funcdef_0__schemaNode.
Local Opaque funcdef_0__predicate funcdef_0__classEqual funcdef_0__classMember funcdef_0__setness funcdef_0__axiom funcdef_0__schemaInstance.
Theorem command_ro bs ns : array_ro watched (funcdef_0__command bs ns).
Proof.
 pose proof (readToken_ro watched) as Htoken. pose proof (readNat_ro watched) as Hnat.
 pose proof (lookup_ro watched) as Hlookup. pose proof (ok_ro watched) as Hok. pose proof (no_ro watched) as Hno.
 pose proof bindName_ro as Hbind. pose proof appendTheorem_ro as Happend. pose proof modusPonens_ro as Hmp.
 pose proof generalize_ro as Hgen. pose proof schemaCheck_ro as Hcheck. pose proof schemaNode_ro as Hnode.
 pose proof (SchemaInstanceLengths.generated_ro watched (proj1 Hprotected)) as Hinstance.
 assert (Hmemo:RenameMemoLengths.protected watched) by (facts;repeat split;assumption).
 pose proof (RenameMemoLengths.predicate_ro watched Hmemo) as Hpredicate.
 pose proof (SchemaEvaluationFrames.classEqual_lengths watched Hmemo) as Hequal.
 pose proof (SchemaEvaluationFrames.classMember_lengths watched Hmemo) as Hmember.
 pose proof (ClassCertifyLengths.setness_ro watched Hmemo) as Hsetness.
 pose proof (AxiomLengths.axiom_ro watched Hmemo) as Haxiom.
 facts. pose proof (InternLengths.intern_ro watched ltac:(assumption) ltac:(assumption) ltac:(assumption)) as Hintern.
 unfold funcdef_0__command. apply eliminate_ro. unfold funcdef_0__command_body. ro.
Qed.
End Protected.
Theorem generated watched s bs ns final observations after : protected watched ->
 execObserved (funcdef_0__command bs ns) (s,observations)=Some(tt,(final,after)) ->
 length (memory final watched)=length (memory s watched).
Proof. intros Hprotected Hrun. exact (observed_preserves watched _ s observations tt final after (command_ro watched Hprotected bs ns) Hrun). Qed.
Lemma meta_protected : protected arraydef_0__meta.
Proof. unfold protected,SchemaInstanceLengths.protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected;repeat split;discriminate. Qed.
Lemma sipState_protected : protected arraydef_0__sipState.
Proof. unfold protected,SchemaInstanceLengths.protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected;repeat split;discriminate. Qed.
Lemma token_protected : protected arraydef_0__token.
Proof. unfold protected,SchemaInstanceLengths.protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected;repeat split;discriminate. Qed.
Lemma printBuffer_protected : protected arraydef_0__printBuffer.
Proof. unfold protected,SchemaInstanceLengths.protected,SchemaEvaluationFrames.protected,RenameMemoLengths.protected;repeat split;discriminate. Qed.
End NativeCommandLengths.
