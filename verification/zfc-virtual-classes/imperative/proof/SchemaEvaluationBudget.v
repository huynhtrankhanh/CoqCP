From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaRepresentation SchemaGraph SchemaEvaluationResources SchemaEvaluationRun.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationBudget.
Import IndexExecution SipHashExecution.
(** Literal syntax and saved-theorem modus ponens allocate no formula nodes.
    This fragment gives arbitrary-length, multi-cell witnesses for the finite
    resource condition without quantifying over executions. *)
Definition free_kind kind := kind=1%nat \/ kind=2%nat \/ kind=9%nat \/ kind=11%nat.
Definition free_reachable source root := forall node depth kind a b c d expression,
 SchemaGraph.reachable source root node depth ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 free_kind kind.
Lemma free_ready native fs classes rho depth kind a b c d :
 free_kind kind -> SchemaEvaluationResources.ready native fs classes rho depth kind a b c d.
Proof. intros [Hkind|[Hkind|[Hkind|Hkind]]];subst kind;exact I. Qed.
Lemma ready_at_free source logical root rho key fs classes f :
 free_reachable source root -> memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 SchemaEvaluationRun.ready_at source logical root rho key fs classes f.
Proof.
 intros Hfree Hnodes node depth expression kind a b c d Hkey Hreachable Hlookup Hraw.
 apply free_ready. apply (Hfree node depth kind a b c d expression Hreachable). now rewrite <-Hnodes.
Qed.
Theorem fits_free source logical root rho count key fs classes f :
 free_reachable source root -> memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 SchemaEvaluationRun.fits source logical root rho count key fs classes f.
Proof.
 intros Hfree. induction count as [|count IH] in key,fs,classes,f|-*;intro Hnodes;[exact I|].
 split;[now apply ready_at_free|]. intros next_fs next_classes after Hsuccessor.
 apply IH. destruct Hsuccessor as [_ [_ [Hframe _]]].
 rewrite (SchemaEvaluationRun.nodes_same f after Hframe). exact Hnodes.
Qed.
Definition raw_kind (raw:Z*Z*Z*Z*Z*Z*Z) := let '(kind,_,_,_,_,_,_):=raw in Z.to_nat kind.
Lemma free_table source root :
 Forall (fun raw=>free_kind (raw_kind raw)) (memory source arraydef_0__schemaNodes) -> free_reachable source root.
Proof.
 intros Htable node depth kind a b c d expression Hreachable Hraw.
 assert (Hentry:free_kind (raw_kind (SchemaRepresentation.encode kind a b c d expression))).
 { induction Htable as [|head rest Hhead Hrest IH] in node,Hraw|-*;[destruct node;discriminate|].
   destruct node as [|node];[injection Hraw as <-;exact Hhead|apply (IH node Hraw)]. }
 unfold raw_kind,SchemaRepresentation.encode in Hentry. now rewrite Nat2Z.id in Hentry.
Qed.
Theorem fits_free_table source logical root rho fs classes f :
 Forall (fun raw=>free_kind (raw_kind raw)) (memory source arraydef_0__schemaNodes) ->
 memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 SchemaEvaluationRun.fits source logical root rho (SchemaGraph.width root*SchemaGraph.width root) 0 fs classes f.
Proof. intros Htable Hnodes. apply fits_free;[now apply free_table|exact Hnodes]. Qed.
End SchemaEvaluationBudget.
