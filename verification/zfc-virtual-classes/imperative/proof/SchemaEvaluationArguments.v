From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaRepresentation SchemaMetadata SchemaGraph SchemaEvaluationArity SchemaEvaluationResources InternReserve.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationArguments.
Import IndexExecution SipHashExecution.
(** The supplied prefix is meaningful; unused capacity after it is irrelevant. *)
Definition represents (native:Machine) ids := forall index id,nth_error ids index=Some id ->
 nth_error (memory native arraydef_0__schemaArguments) index=Some (Z.of_nat id).
Lemma prefix_represents native ids :
 firstn (length ids) (memory native arraydef_0__schemaArguments)=map Z.of_nat ids -> represents native ids.
Proof.
 intros Hprefix index id Hlookup.
 assert (Hbound:(index<length ids)%nat) by (apply nth_error_Some;congruence).
 pose proof (f_equal (fun xs=>nth_error xs index) Hprefix) as Hvalue.
 cbn beta in Hvalue.
 rewrite List.nth_error_firstn,nth_error_map,Hlookup in Hvalue.
 assert (Hlt:(index<?length ids)%nat=true) by (apply Nat.ltb_lt;exact Hbound).
 rewrite Hlt in Hvalue. exact Hvalue.
Qed.
Lemma transport before after ids :
 memory after arraydef_0__schemaArguments=memory before arraydef_0__schemaArguments ->
 represents before ids -> represents after ids.
Proof. unfold represents. intros -> Hrep. exact Hrep. Qed.
Lemma lookup_word ids index id : Forall (fun value=>word (Z.of_nat value)) ids -> nth_error ids index=Some id -> word (Z.of_nat id).
Proof.
 intros Hwords. induction Hwords as [|head rest Hhead Hrest IH] in index|-*;[destruct index;discriminate|].
 destruct index;[intro Hlookup;injection Hlookup as <-;exact Hhead|apply IH].
Qed.
Theorem reachable_argument source native logical root cert node depth a ids actual extra_classes :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 SchemaGraph.reachable source root node depth ->
 nth_error (Protocol.expressions logical) node=Some (Protocol.CE (Schemata.metavariable a)) ->
 length ids=Schemata.proof_arity cert ->
 Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 Forall (fun id=>word (Z.of_nat id)) ids -> represents native ids ->
 SchemaEvaluationResources.argument native (Protocol.classes logical++extra_classes)
   (fun index=>List.nth index actual (VirtualClasses.set 0)) a.
Proof.
 intros Hrep Hroot Hreachable Hlookup Hlength Hactual Hwords Hnative.
 destruct (SchemaEvaluationArity.supplied_argument source logical root cert node depth a ids actual
   Hrep Hroot Hreachable Hlookup Hlength Hactual) as [id [cls [Hid [Hcls [Hclass Hrho]]]]].
 exists id. split;[exact (Hnative a id Hid)|]. split;[exact (lookup_word ids a id Hwords Hid)|].
 rewrite Hrho. unfold Protocol.class_at in Hclass.
 eapply InternReserve.lookup_preserved;[exists extra_classes;reflexivity|exact Hclass].
Qed.
End SchemaEvaluationArguments.
