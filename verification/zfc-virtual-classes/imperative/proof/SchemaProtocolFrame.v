From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash SchemaRepresentation EffectFrame MetaCellFrame InternReserve.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaProtocolFrame.
Import IndexExecution SipHashExecution.
Definition prefixes before after :=
 (exists extra,Protocol.formulas after=Protocol.formulas before++extra) /\
 (exists extra,Protocol.classes after=Protocol.classes before++extra).
Lemma accepted_prefixes before request reply after : Protocol.accepted before request reply after -> prefixes before after.
Proof.
 intro Haccepted. inversion Haccepted;subst;unfold prefixes;cbn [Protocol.formulas Protocol.classes Protocol.with_history];split;
 first [exists [];now rewrite app_nil_r|eexists;reflexivity|
  match goal with H:Protocol.allocation _ _ _ _ _ |- _=>exact (proj1 H) end|
  match goal with H:Protocol.allocation _ _ _ _ _ |- _=>exact (proj2 (proj2 (proj2 H))) end].
Qed.
Lemma accepted_expressions before request reply after : Protocol.accepted before request reply after ->
 Protocol.opcode request<>22%nat -> Protocol.expressions after=Protocol.expressions before.
Proof.
 intros Haccepted HnotNode. inversion Haccepted;subst;cbn [Protocol.expressions Protocol.with_history];try reflexivity.
 exfalso. apply HnotNode. reflexivity.
Qed.
Lemma retained_prefixes before after : Protocol.retained_storage before after -> prefixes before after.
Proof. intros [Hfs [_ [Hclasses Hrest]]]. split;assumption. Qed.
Lemma prefixes_transitive before middle after : prefixes before middle -> prefixes middle after -> prefixes before after.
Proof.
 intros [[fs Hfs] [classes Hclasses]] [[moreFs HmoreFs] [moreClasses HmoreClasses]].
 split;[exists (fs++moreFs);rewrite HmoreFs,Hfs|exists (classes++moreClasses);rewrite HmoreClasses,Hclasses];now rewrite app_assoc.
Qed.
Theorem step_prefixes before request reply after : Protocol.step before request reply after -> prefixes before after.
Proof.
 intro Hstep. inversion Hstep;subst.
 - eapply prefixes_transitive;[eapply accepted_prefixes;eassumption|apply retained_prefixes;eassumption].
 - apply retained_prefixes;assumption.
Qed.
Theorem step_expressions before request reply after : Protocol.step before request reply after ->
 Protocol.opcode request<>22%nat -> Protocol.expressions after=Protocol.expressions before.
Proof.
 intros Hstep HnotNode. inversion Hstep;subst.
 - match goal with Hretained:Protocol.retained_storage ?middle after |- _=>
    destruct Hretained as [_ [_ [_ [_ [_ Hsame]]]]];rewrite Hsame end.
   eapply accepted_expressions;eassumption.
 - match goal with Hretained:Protocol.retained_storage before after |- _=>
    exact (proj2 (proj2 (proj2 (proj2 (proj2 Hretained))))) end.
Qed.
Theorem preserves s t before request reply after :
 SchemaRepresentation.represents s before -> Protocol.step before request reply after -> Protocol.opcode request<>22%nat ->
 meta_value t 16=meta_value s 16 -> memory t arraydef_0__schemaNodes=memory s arraydef_0__schemaNodes ->
 SchemaRepresentation.represents t after.
Proof.
 intros Hrep Hstep HnotNode Hcount Hnodes. destruct (step_prefixes _ _ _ _ Hstep) as [Hfs Hclasses].
 eapply SchemaRepresentation.extend;[exact Hrep|exact Hcount|exact Hnodes| | |exact (step_expressions _ _ _ _ Hstep HnotNode)].
 - intros index value Hlookup. eapply InternReserve.lookup_preserved;[exact Hfs|exact Hlookup].
 - intros index value Hlookup. eapply InternReserve.lookup_preserved;[exact Hclasses|exact Hlookup].
Qed.
Theorem generated_preserves {R} (code:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R)
 s observations result final afterObservations before request reply after :
 EffectFrame.array_ro arraydef_0__schemaNodes code -> MetaCellFrame.array_ro 16%nat code ->
 execObserved code (s,observations)=Some (result,(final,afterObservations)) ->
 SchemaRepresentation.represents s before -> Protocol.step before request reply after -> Protocol.opcode request<>22%nat ->
 SchemaRepresentation.represents final after.
Proof.
 intros Hnodes Hcount Hrun Hrep Hstep HnotNode. eapply preserves;[exact Hrep|exact Hstep|exact HnotNode| |].
 - eapply MetaCellFrame.observed_preserves;[exact Hcount|exact Hrun].
 - eapply EffectFrame.observed_preserves;[exact Hnodes|exact Hrun].
Qed.
End SchemaProtocolFrame.
