From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaRepresentation SchemaMetadata SchemaGraph SchemaEvaluationDependencies.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationFailure.
Import IndexExecution SipHashExecution.
Definition evaluable rho depth expression := match expression with
| Protocol.PE cert=>exists formula,Schemata.infer rho depth cert=Some formula
| _=>True end.
Lemma mp_children rho depth implication antecedent :
 evaluable rho depth (Protocol.PE (Schemata.template_mp implication antecedent)) ->
 evaluable rho depth (Protocol.PE implication) /\ evaluable rho depth (Protocol.PE antecedent).
Proof.
 cbn [evaluable Schemata.infer]. intros [result Hresult].
 destruct (Schemata.infer rho depth implication) as [pi|] eqn:Hi;[|discriminate].
 destruct (Schemata.infer rho depth antecedent) as [pa|] eqn:Ha;
 destruct pi;try discriminate. split;[eexists;reflexivity|eexists;reflexivity].
Qed.
Lemma gen_child rho depth cert :
 evaluable rho depth (Protocol.PE (Schemata.template_gen cert)) ->
 evaluable rho (S depth) (Protocol.PE cert).
Proof.
 cbn [evaluable Schemata.infer]. intros [result Hresult].
 destruct (Schemata.infer rho (S depth) cert) as [p|];[eexists;reflexivity|discriminate].
Qed.
Lemma view_child fs classes expressions k a b c d expression child extra childExpression rho depth :
 SchemaEvaluationDependencies.view fs classes expressions k a b c d expression ->
 evaluable rho depth expression -> In (child,extra) (SchemaGraph.children_fields k a b c d) ->
 nth_error expressions child=Some childExpression -> evaluable rho (depth+extra) childExpression.
Proof.
 intros Hview Hsuccess Hin Hlookup.
 inversion Hview as [aa bb cc dd Hsmall|aa bb cc dd cls Hclass|aa bb cc dd p Hformula|
 aa bb cc dd p Hp|aa bb cc dd x y Hp Hq|aa bb cc dd x y Hp Hq|
 aa bb cc dd p q Hp Hq|aa bb cc dd p Hp|
 tag aa bb cc p q r Htag Hp Hq Hr|aa bb cc dd p q Hp Hq|
 aa bb cc dd p Hp|aa bb cc dd p checked Hformula];subst;
 cbn [SchemaGraph.children_fields] in Hin;try contradiction.
 - destruct Hin as [Heq|[]]. injection Heq as <- <-. rewrite Hp in Hlookup. injection Hlookup as <-. exact I.
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;exact I.
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;exact I.
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;exact I.
 - destruct Hin as [Heq|[]]. injection Heq as <- <-. rewrite Hp in Hlookup. injection Hlookup as <-. exact I.
 - repeat rewrite in_app_iff in Hin.
   destruct Hin as [Hin|[Hin|Hin]].
   + destruct (SchemaGraph.need_p a) eqn:Hneeded;[|contradiction]. destruct Hin as [Heq|[]]. injection Heq as <- <-.
     rewrite (Hp eq_refl) in Hlookup. injection Hlookup as <-. exact I.
   + destruct (SchemaGraph.need_q a) eqn:Hneeded;[|contradiction]. destruct Hin as [Heq|[]]. injection Heq as <- <-.
     rewrite (Hq eq_refl) in Hlookup. injection Hlookup as <-. exact I.
   + destruct (SchemaGraph.need_r a) eqn:Hneeded;[|contradiction]. destruct Hin as [Heq|[]]. injection Heq as <- <-.
     rewrite (Hr eq_refl) in Hlookup. injection Hlookup as <-. exact I.
 - destruct (mp_children rho depth p q Hsuccess) as [Hi Ha].
   destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;
   rewrite Nat.add_0_r;assumption.
 - destruct Hin as [Heq|[]]. injection Heq as <- <-. rewrite Hp in Hlookup. injection Hlookup as <-.
   rewrite Nat.add_1_r. exact (gen_child rho depth p Hsuccess).
Qed.
Theorem reachable_evaluable source logical root rootExpression rho node depth expression :
 SchemaRepresentation.represents source logical ->
 nth_error (Protocol.expressions logical) root=Some rootExpression -> evaluable rho 0 rootExpression ->
 SchemaGraph.reachable source root node depth -> nth_error (Protocol.expressions logical) node=Some expression ->
 evaluable rho depth expression.
Proof.
 intros Hrep Hroot Hsuccess Hreachable. induction Hreachable as [|parent depth child extra Hparent IH Hin] in expression|-*.
 - intros Hlookup. rewrite Hroot in Hlookup. injection Hlookup as <-. exact Hsuccess.
 - intro Hlookup.
   assert (Hrootbound:(root<length (memory source arraydef_0__schemaNodes))%nat).
   { rewrite (SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical Hrep)). apply nth_error_Some;congruence. }
   pose proof (SchemaGraph.represented_ordered source logical Hrep) as Hordered.
   destruct (SchemaGraph.reachable_bound source root parent depth Hordered Hrootbound Hparent) as [Hparentbound _].
   rewrite (SchemaMetadata.represents_length source _ (SchemaRepresentation.metadata source logical Hrep)) in Hparentbound.
   destruct (nth_error (Protocol.expressions logical) parent) as [parentExpression|] eqn:Hparentlookup;
     [|apply nth_error_None in Hparentlookup;lia].
   destruct (SchemaEvaluationDependencies.represented_view source logical parent parentExpression Hrep Hparentlookup)
    as (k & a & b & c & d & Hraw & Hfit & Hview).
   assert (Hat:SchemaMetadata.node_at source parent=SchemaRepresentation.encode k a b c d parentExpression).
   { unfold SchemaMetadata.node_at. exact (List.nth_error_nth _ _ _ Hraw). }
   rewrite Hat,SchemaGraph.children_encode in Hin.
   eapply view_child;[exact Hview|apply IH;reflexivity|exact Hin|exact Hlookup].
Qed.
Theorem reachable_failure source logical root rootCert rho node depth cert :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 SchemaGraph.reachable source root node depth -> nth_error (Protocol.expressions logical) node=Some (Protocol.PE cert) ->
 Schemata.infer rho depth cert=None -> Schemata.infer rho 0 rootCert=None.
Proof.
 intros Hrep Hroot Hreachable Hlookup Hfailure.
 destruct (Schemata.infer rho 0 rootCert) as [result|] eqn:Hresult;[|reflexivity].
 exfalso. destruct (reachable_evaluable source logical root (Protocol.PE rootCert) rho node depth (Protocol.PE cert)
   Hrep Hroot ltac:(exists result;exact Hresult) Hreachable Hlookup) as [childResult Hchild]. congruence.
Qed.
End SchemaEvaluationFailure.
