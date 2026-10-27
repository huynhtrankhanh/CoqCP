From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash SchemaRepresentation SchemaGraph SchemaEvaluationResources SchemaEvaluationRun InternReserve SchemaEvaluationInitial SchemaInstanceEntry SchemaMarking.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationGeneralBudget.
Import IndexExecution SipHashExecution.
(** A class-parametric fragment whose formula arena does not grow. Parameters
    may occur outside binders; comprehensions allocate at most one class each.
    The bound below counts every grid cell, including unmarked cells. *)
Definition supported kind depth :=
 (kind=0%nat /\ depth=0%nat) \/ kind=1%nat \/ kind=2%nat \/ kind=3%nat \/ kind=9%nat \/ kind=11%nat.
Definition fragment source root := forall node depth kind a b c d expression,
 SchemaGraph.reachable source root node depth ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 supported kind depth.
Definition parameters source root native classes rho := forall node depth a b c d expression,
 SchemaGraph.reachable source root node depth ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode 0 a b c d expression) ->
 SchemaEvaluationResources.argument native classes rho a.
Lemma argument_transport before after classes next_classes rho a :
 memory after arraydef_0__schemaArguments=memory before arraydef_0__schemaArguments ->
 (exists extra,next_classes=classes++extra) ->
 SchemaEvaluationResources.argument before classes rho a ->
 SchemaEvaluationResources.argument after next_classes rho a.
Proof.
 intros Harguments Hclasses (id & Hraw & Hword & Hclass).
 exists id. split;[now rewrite Harguments|]. split;[exact Hword|].
 eapply InternReserve.lookup_preserved;[exact Hclasses|exact Hclass].
Qed.
Lemma parameters_transport source root before after classes next_classes rho :
 memory after arraydef_0__schemaArguments=memory before arraydef_0__schemaArguments ->
 (exists extra,next_classes=classes++extra) ->
 parameters source root before classes rho -> parameters source root after next_classes rho.
Proof.
 intros Harguments Hclasses Hparameters node depth a b c d expression Hreachable Hraw.
 eapply argument_transport;[exact Harguments|exact Hclasses|]. eapply Hparameters;eassumption.
Qed.
Lemma ready_at_fragment source logical root rho key fs classes f :
 fragment source root -> parameters source root (machine f) classes rho ->
 memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 Z.of_nat (length classes+1)<=maximum ->
 SchemaEvaluationRun.ready_at source logical root rho key fs classes f.
Proof.
 intros Hfragment Hparameters Hnodes Hroom node depth expression kind a b c d Hkey Hreachable Hlookup Hraw.
 assert (Hsource:nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression))
   by now rewrite <-Hnodes.
 destruct (Hfragment node depth kind a b c d expression Hreachable Hsource)
   as [[Hkind Hdepth]|[Hkind|[Hkind|[Hkind|[Hkind|Hkind]]]]];subst kind.
 - subst depth. split.
   + eapply Hparameters;eassumption.
   + intros Hbad. contradiction.
 - exact I.
 - exact I.
 - exact Hroom.
 - exact I.
 - exact I.
Qed.
Theorem fits_fragment source logical root rho count key fs classes f :
 fragment source root -> parameters source root (machine f) classes rho ->
 memory (machine f) arraydef_0__schemaNodes=memory source arraydef_0__schemaNodes ->
 Z.of_nat (length classes+count)<=maximum ->
 SchemaEvaluationRun.fits source logical root rho count key fs classes f.
Proof.
 intros Hfragment. induction count as [|count IH] in key,fs,classes,f|-*;
   intros Hparameters Hnodes Hbudget;[exact I|].
 split.
 - apply ready_at_fragment;try assumption;lia.
 - intros next_fs next_classes after Hsuccessor.
   destruct Hsuccessor as [Hbefore [Hafter [Hframe [Hfs [Hclasses [Hgrowth Hrest]]]]]].
   apply IH.
   + eapply parameters_transport;[exact (SchemaEvaluationRun.arguments_same f after Hframe)|exact Hclasses|exact Hparameters].
   + rewrite (SchemaEvaluationRun.nodes_same f after Hframe). exact Hnodes.
   + lia.
Qed.
(** This discharges the resource premise of the complete native entry theorem;
    callers need only inspect the schema graph, supplied class arguments, and
    the single class-count inequality. *)
Theorem entry_resources s bs ns logical root rho :
 fragment s root -> parameters s root s (Protocol.classes logical) rho ->
 Z.of_nat (length (Protocol.classes logical)+SchemaMarking.size root)<=maximum ->
 SchemaInstanceEntry.resources s bs ns logical root rho.
Proof.
 intros Hfragment Hparameters Hbudget marked Hmarked.
 apply fits_fragment;[exact Hfragment| | |exact Hbudget].
 - eapply parameters_transport.
   + exact (SchemaEvaluationInitial.untouched _ _ _ Hmarked arraydef_0__schemaArguments ltac:(discriminate) ltac:(discriminate)).
   + exists [];now rewrite app_nil_r.
   + exact Hparameters.
 - exact (SchemaEvaluationInitial.untouched _ _ _ Hmarked arraydef_0__schemaNodes ltac:(discriminate) ltac:(discriminate)).
Qed.
End SchemaEvaluationGeneralBudget.
