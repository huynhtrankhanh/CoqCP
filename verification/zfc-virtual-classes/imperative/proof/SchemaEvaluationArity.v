From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaRepresentation SchemaMetadata SchemaGraph SchemaEvaluationDependencies.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationArity.
Import IndexExecution SipHashExecution.
Lemma needed_p tag p q r i j k : SchemaGraph.need_p tag=true ->
 (Schemata.formula_arity p<=Schemata.axiom_arity (Schemata.template_axiom tag p q r i j k))%nat.
Proof.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
 all: cbn [SchemaGraph.need_p existsb Nat.eqb orb Schemata.axiom_arity];try discriminate;intro;lia.
Qed.
Lemma needed_q tag p q r i j k : SchemaGraph.need_q tag=true ->
 (Schemata.formula_arity q<=Schemata.axiom_arity (Schemata.template_axiom tag p q r i j k))%nat.
Proof.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 18%nat tag.
 all: cbn [SchemaGraph.need_q existsb Nat.eqb orb Schemata.axiom_arity];try discriminate;intro;lia.
Qed.
Lemma needed_r tag p q r i j k : SchemaGraph.need_r tag=true ->
 (Schemata.formula_arity r<=Schemata.axiom_arity (Schemata.template_axiom tag p q r i j k))%nat.
Proof.
 let rec cases count tag := lazymatch count with O=>idtac|S ?rest=>let next:=fresh "tag" in destruct tag as [|next];[idtac|cases rest next] end in cases 2%nat tag.
 all: cbn [SchemaGraph.need_r Nat.eqb Schemata.axiom_arity];try discriminate;intro;lia.
Qed.
Lemma view_child fs classes expressions k a b c d expression child extra childExpression :
 SchemaEvaluationDependencies.view fs classes expressions k a b c d expression ->
 In (child,extra) (SchemaGraph.children_fields k a b c d) ->
 nth_error expressions child=Some childExpression ->
 (SchemaMetadata.arity childExpression<=SchemaMetadata.arity expression)%nat.
Proof.
 intros Hview Hin Hlookup.
 inversion Hview as [aa bb cc dd Hsmall|aa bb cc dd cls Hclass|aa bb cc dd p Hformula|
 aa bb cc dd p Hp|aa bb cc dd x y Hp Hq|aa bb cc dd x y Hp Hq|
 aa bb cc dd p q Hp Hq|aa bb cc dd p Hp|
 tag aa bb cc p q r Htag Hp Hq Hr|aa bb cc dd p q Hp Hq|
 aa bb cc dd p Hp|aa bb cc dd p checked Hformula];subst;
 cbn [SchemaGraph.children_fields] in Hin;try contradiction.
 - destruct Hin as [Heq|[]]. injection Heq as <- <-. rewrite Hp in Hlookup. injection Hlookup as <-. reflexivity.
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;
   cbn [SchemaMetadata.arity Schemata.formula_arity];lia.
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;
   cbn [SchemaMetadata.arity Schemata.formula_arity];lia.
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;
   cbn [SchemaMetadata.arity Schemata.formula_arity];lia.
 - destruct Hin as [Heq|[]]. injection Heq as <- <-. rewrite Hp in Hlookup. injection Hlookup as <-. reflexivity.
 - repeat rewrite in_app_iff in Hin. destruct Hin as [Hin|[Hin|Hin]].
   + destruct (SchemaGraph.need_p a) eqn:Hneeded;[|contradiction]. destruct Hin as [Heq|[]]. injection Heq as <- <-.
     rewrite (Hp eq_refl) in Hlookup. injection Hlookup as <-. exact (needed_p a p q r b c d Hneeded).
   + destruct (SchemaGraph.need_q a) eqn:Hneeded;[|contradiction]. destruct Hin as [Heq|[]]. injection Heq as <- <-.
     rewrite (Hq eq_refl) in Hlookup. injection Hlookup as <-. exact (needed_q a p q r b c d Hneeded).
   + destruct (SchemaGraph.need_r a) eqn:Hneeded;[|contradiction]. destruct Hin as [Heq|[]]. injection Heq as <- <-.
     rewrite (Hr eq_refl) in Hlookup. injection Hlookup as <-. exact (needed_r a p q r b c d Hneeded).
 - destruct Hin as [Heq|[Heq|[]]];injection Heq as <- <-;
   first [rewrite Hp in Hlookup|rewrite Hq in Hlookup];injection Hlookup as <-;
   cbn [SchemaMetadata.arity Schemata.proof_arity];lia.
 - destruct Hin as [Heq|[]]. injection Heq as <- <-. rewrite Hp in Hlookup. injection Hlookup as <-. reflexivity.
Qed.
Theorem reachable_arity source logical root rootExpression node depth expression :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some rootExpression ->
 SchemaGraph.reachable source root node depth -> nth_error (Protocol.expressions logical) node=Some expression ->
 (SchemaMetadata.arity expression<=SchemaMetadata.arity rootExpression)%nat.
Proof.
 intros Hrep Hroot Hreachable. induction Hreachable as [|parent depth child extra Hparent IH Hin] in expression|-*.
 - intros Hlookup. rewrite Hroot in Hlookup. injection Hlookup as <-. reflexivity.
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
   eapply Nat.le_trans;[eapply view_child;[exact Hview|exact Hin|exact Hlookup]|apply IH;reflexivity].
Qed.
Theorem reachable_metavariable source logical root rootExpression node depth a :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some rootExpression ->
 SchemaGraph.reachable source root node depth ->
 nth_error (Protocol.expressions logical) node=Some (Protocol.CE (Schemata.metavariable a)) ->
 (a<SchemaMetadata.arity rootExpression)%nat.
Proof.
 intros Hrep Hroot Hreachable Hlookup.
 exact (reachable_arity source logical root rootExpression node depth (Protocol.CE (Schemata.metavariable a)) Hrep Hroot Hreachable Hlookup).
Qed.
Theorem supplied_argument source logical root cert node depth a ids actual :
 SchemaRepresentation.represents source logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 SchemaGraph.reachable source root node depth ->
 nth_error (Protocol.expressions logical) node=Some (Protocol.CE (Schemata.metavariable a)) ->
 length ids=Schemata.proof_arity cert -> Forall2 (fun id cls=>Protocol.class_at logical id=Some cls) ids actual ->
 exists id cls,nth_error ids a=Some id /\ nth_error actual a=Some cls /\ Protocol.class_at logical id=Some cls /\
 List.nth a actual (VirtualClasses.set 0)=cls.
Proof.
 intros Hrep Hroot Hreachable Hlookup Hlength Hactual.
 pose proof (reachable_metavariable source logical root (Protocol.PE cert) node depth a Hrep Hroot Hreachable Hlookup) as Hbound.
 change (a<Schemata.proof_arity cert)%nat in Hbound.
 assert (Hids:(a<length ids)%nat) by lia.
 destruct (nth_error ids a) as [id|] eqn:Hid;[|apply nth_error_None in Hid;lia].
 clear Hlength Hbound Hids Hrep Hroot Hreachable Hlookup.
 induction Hactual as [|headId headClass restIds restClasses Hclass Hrest IH] in a,id,Hid|-*;[destruct a;discriminate|].
 destruct a as [|a].
 - injection Hid as <-. exists headId,headClass. repeat split;assumption||reflexivity.
 - destruct (IH a id Hid) as [foundId [cls [Hfound [Hcls [Hlookup Hnth]]]]]. exists foundId,cls.
   repeat split;assumption.
Qed.
End SchemaEvaluationArity.
