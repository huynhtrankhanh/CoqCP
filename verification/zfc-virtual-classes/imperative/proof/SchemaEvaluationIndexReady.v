From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash SchemaEvaluation SchemaGraph SchemaRepresentation
 SchemaEvaluationRun SchemaEvaluationResources SchemaEvaluationBoundedCell SchemaEvaluationIndexCell
 SchemaEvaluationIndexRun SchemaEvaluationIndexBudget SchemaEvaluationGeneralBudget SchemaEvaluationIndexBounds
 RenameMemoResourceBounds.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaEvaluationIndexReady.
Import IndexExecution SipHashExecution.
Definition scalar ceiling index_ceiling source root class_base :=
 forall node depth kind a b c d expression,
 SchemaGraph.reachable source root node depth ->
 nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression) ->
 let key:=SchemaGraph.key root node depth in
 (ceiling key+SchemaEvaluationIndexBudget.cost (ceiling key) kind a depth<=ceiling (S key))%nat /\
 (SchemaEvaluationIndexBudget.renames kind a depth=true ->
   Z.of_nat (5*(ceiling key*ceiling key)+1)<=maximum) /\
 (SchemaEvaluationIndexBudget.needs_class kind depth=true -> Z.of_nat (class_base+key+1)<=maximum) /\
 (SchemaEvaluationIndexCell.successor kind (index_ceiling key) depth b c d<=index_ceiling (S key))%nat.
Lemma step_same kind bound depth b c d :
 SchemaEvaluationIndexBudget.index_step kind bound depth b c d=
 SchemaEvaluationIndexCell.successor kind bound depth b c d.
Proof.
 let rec cases count index := lazymatch count with
   O=>idtac | S ?rest=>destruct index as [|index];[reflexivity|cases rest index] end in cases 12%nat kind.
 reflexivity.
Qed.
Section Policy.
Variable ceiling index_ceiling:nat->nat.
Hypothesis ceiling_word:forall key,Z.of_nat (ceiling key)<=SchemaEvaluationBoundedCell.bound.
Hypothesis index_word:forall key,Z.of_nat (index_ceiling key)<=maximum.
Theorem ready_at source logical root rho key fs classes f class_base :
 SchemaEvaluationRun.domain source logical root rho fs classes f ->
 scalar ceiling index_ceiling source root class_base ->
 SchemaEvaluationGeneralBudget.parameters source root (machine f) classes rho ->
 (length fs<=ceiling key)%nat ->
 SchemaEvaluationIndexCell.bounded (machine f) fs classes (index_ceiling key) ->
 (length classes<=class_base+key)%nat ->
 SchemaEvaluationIndexRun.ready_at ceiling index_ceiling source logical root rho key fs classes f.
Proof.
 intros Hdomain Hscalar Hparameters Hcapacity Hbounded HclassCount.
 split;[exact Hcapacity|]. split;[exact Hbounded|].
 intros node depth expression kind a b c d Hkey Hreachable Hlookup Hraw.
 assert (Hsource:nth_error (memory source arraydef_0__schemaNodes) node=Some (SchemaRepresentation.encode kind a b c d expression)).
 { rewrite <- (SchemaEvaluationRun.source_nodes _ _ _ _ _ _ _ Hdomain). exact Hraw. }
 destruct (Hscalar node depth kind a b c d expression Hreachable Hsource) as (Hstep & Hfuel & Hclassroom & HindexStep).
 rewrite <-Hkey in Hstep,Hfuel,Hclassroom,HindexStep.
 assert (Hnumeric:SchemaEvaluationIndexBudget.numeric (ceiling key) (index_ceiling key) (class_base+key)
   (SchemaEvaluationIndexRun.reserve ceiling key) depth kind a b c d).
 { split.
   - pose proof (SchemaEvaluationIndexRun.reserve_spec ceiling ceiling_word key) as Hreserve.
     unfold SchemaEvaluationBoundedCell.bound,RenameMemoResourceBounds.doubling_limit in *.
     repeat rewrite Nat2Z.inj_add. apply Nat2Z.inj_le in Hstep. rewrite Nat2Z.inj_add in Hstep. lia.
   - split;[exact Hfuel|]. split;[exact Hclassroom|]. rewrite step_same.
     pose proof (index_word (S key)). lia. }
 split;[|exact HindexStep].
 eapply SchemaEvaluationIndexBudget.ready;try eassumption.
 - exact (SchemaEvaluationRun.arena _ _ _ _ _ _ _ Hdomain).
 - exact (SchemaEvaluationRun.topology _ _ _ _ _ _ _ Hdomain).
 - exact (SchemaEvaluationRun.class_meaning _ _ _ _ _ _ _ Hdomain).
 - exact (SchemaEvaluationRun.class_words _ _ _ _ _ _ _ Hdomain).
 - exact (proj1 Hbounded).
 - exact (proj2 Hbounded).
 - pose proof (SchemaEvaluationRun.falsity_zero _ _ _ _ _ _ _ Hdomain) as Hfalse.
   assert (Hzero:(0<length fs)%nat) by (apply nth_error_Some;congruence). exact Hzero.
 - intro Hkind. subst kind. exact (Hparameters node depth a b c d expression Hreachable Hsource).
Qed.
Theorem fits source logical root rho count key fs classes f class_base :
 SchemaEvaluationRun.domain source logical root rho fs classes f ->
 scalar ceiling index_ceiling source root class_base ->
 SchemaEvaluationGeneralBudget.parameters source root (machine f) classes rho ->
 (length fs<=ceiling key)%nat ->
 SchemaEvaluationIndexCell.bounded (machine f) fs classes (index_ceiling key) ->
 (length classes<=class_base+key)%nat ->
 SchemaEvaluationIndexRun.fits ceiling index_ceiling source logical root rho count key fs classes f.
Proof.
 induction count as [|count IH] in key,fs,classes,f|-*;
 intros Hdomain Hscalar Hparameters Hcapacity Hbounded HclassCount;[exact I|].
 split;[exact (ready_at source logical root rho key fs classes f class_base Hdomain Hscalar Hparameters Hcapacity Hbounded HclassCount)|].
 intros next_fs next_classes after [Hsuccessor [HnextCapacity HnextBounded]].
 destruct Hsuccessor as [Hbefore [Hafter [Hframe [Hfs [Hclasses [Hgrowth Hrest]]]]]].
 apply IH;try assumption.
 - eapply SchemaEvaluationGeneralBudget.parameters_transport;[exact (SchemaEvaluationRun.arguments_same f after Hframe)|exact Hclasses|exact Hparameters].
 - lia.
Qed.
End Policy.
End SchemaEvaluationIndexReady.
