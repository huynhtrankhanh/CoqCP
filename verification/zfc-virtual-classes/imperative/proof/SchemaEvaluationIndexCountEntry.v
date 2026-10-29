From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal SchemaRepresentation SchemaMarking SchemaEvaluation
 SchemaEvaluationRun SchemaEvaluationInitial SchemaEvaluationBoundedCell SchemaEvaluationIndexCountRun SchemaEvaluationIndexCell SchemaMetadata SchemaInstanceStorage SchemaInstanceCompletion Representation ClassStorage ClassLookup
 FormulaTopology HistoryRefinement NameRepresentation SemanticFrames InternalIO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexCountEntry.
Import IndexExecution SipHashExecution ObservedLocal.
Definition initial s bs ns : SchemaEvaluation.Frame := {|machine:=s;bools:=bs;nums:=ns|}.
Definition resources ceiling index_ceiling s bs ns logical root rho := forall marked,
 SchemaEvaluationInitial.marked_state (initial s bs ns) root marked ->
 SchemaEvaluationIndexCountRun.fits ceiling index_ceiling s logical root rho (SchemaMarking.size root) 0
   (Protocol.formulas logical) (Protocol.classes logical) marked.
(** Complete native evaluation under an explicit per-grid-key numeric ceiling.
    The finite resource tree refers only to typed semantic states and their
    cardinality envelope; it assumes no successful native run. *)
Theorem generated ceiling index_ceiling s bs ns logical root cert rho observations :
 (forall key,Z.of_nat (ceiling key)<=SchemaEvaluationBoundedCell.bound) ->
 (forall key,(ceiling key<=ceiling (S key))%nat) ->
 (forall key,Z.of_nat (index_ceiling key)<=maximum) ->
 (forall key,(index_ceiling key<=index_ceiling (S key))%nat) ->
 SchemaRepresentation.represents s logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> ns vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 meta_value s 8=0 -> meta_value s 18<>0 -> resources ceiling index_ceiling s bs ns logical root rho ->
 exists final fs classes,
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,observations)) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 HistoryRefinement.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 NameRepresentation.represents final (Protocol.bindings logical) /\
 SchemaRepresentation.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length fs) /\ meta_value final 8=0 /\
 InternalIO.preserves s final /\ (exists extra,fs=Protocol.formulas logical++extra) /\ (exists extra,classes=Protocol.classes logical++extra) /\
 (length classes<=length (Protocol.classes logical)+SchemaMarking.size root)%nat /\
 (length fs<=ceiling (SchemaMarking.size root))%nat /\
 SchemaEvaluationIndexCell.bounded final fs classes (index_ceiling (SchemaMarking.size root)) /\
 (Guarantees.safe logical -> Guarantees.safe (SchemaInstanceCompletion.prepared logical fs classes)) /\
 ((exists p,Schemata.infer rho 0 cert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value fs (meta_value final 0) p /\ meta_value final 18<>0) \/
  (Schemata.infer rho 0 cert=None /\ meta_value final 18=0)).
Proof.
 intros HceilingWord HceilingStep HindexWord HindexStep Hschema Hlookup Hroom Hroot Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid Hresources.
 assert (Hrootbound:(root<length (memory s arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length _ _ (SchemaRepresentation.metadata _ _ Hschema)). apply nth_error_Some;congruence. }
 destruct (SchemaEvaluationInitial.generated_marking (initial s bs ns) logical root rho observations Hschema Hrootbound Hroom Hroot
   Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror)
   as (marked & Hinitial & Hbodyeq & Hmarked & HmarkedDomain & HmarkedValid).
 destruct (SchemaEvaluationIndexCountRun.generated_evaluation ceiling HceilingWord HceilingStep index_ceiling HindexWord HindexStep s logical root cert rho (Protocol.formulas logical) (Protocol.classes logical)
   marked observations Hschema Hlookup HmarkedDomain ltac:(now rewrite HmarkedValid) Hroom (Hresources marked Hmarked))
   as (after & fs & classes & Hevaluation & Hdomain & Hframe & Hfs & Hcs & HclassCount & Hceiling & Hindices & Hresult).
 assert (Hbody:execLocalObserved funcdef_0__schemaInstance_body (initial s bs ns,observations)=Some (tt,(after,observations)))
   by (rewrite Hbodyeq;exact Hevaluation).
 assert (Hrun:execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(machine after,observations))).
 { change (execObserved (eliminateLocalVariables bs ns funcdef_0__schemaInstance_body) (s,observations)=Some (tt,(machine after,observations))).
   rewrite (ObservedLocal.eliminate_correct funcdef_0__schemaInstance_body bs ns s observations).
   change (optionBind (execLocalObserved funcdef_0__schemaInstance_body (initial s bs ns,observations))
    (fun response=>Some (fst response,(machine (fst (snd response)),snd (snd response))))=Some (tt,(machine after,observations))).
   now rewrite Hbody. }
 destruct (SchemaInstanceStorage.registries s bs ns (machine after) observations observations logical Hrun Hhistory Hnames)
   as [HnextHistory [HnextNames Hio]].
 exists (machine after),fs,classes. split;[exact Hrun|].
 split;[exact (SchemaEvaluationRun.arena _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.class_meaning _ _ _ _ _ _ _ Hdomain)|].
 split;[exact HnextHistory|]. split;[exact HnextNames|].
 split;[exact (SchemaEvaluationRun.schemas _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.class_words _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.topology _ _ _ _ _ _ _ Hdomain)|].
 split;[exact (SchemaEvaluationRun.error_clear _ _ _ _ _ _ _ Hdomain)|].
 split;[exact Hio|]. split;[exact Hfs|]. split;[exact Hcs|]. split;[exact HclassCount|]. split;[exact Hceiling|]. split;[exact Hindices|]. split;[|exact Hresult].
 apply Guarantees.retained. unfold Protocol.retained_storage,SchemaInstanceCompletion.prepared.
 cbn [Protocol.formulas Protocol.classes Protocol.history Protocol.bindings Protocol.expressions].
 split;[exact Hfs|]. split;[exact (SemanticFrames.arena_NoDup _ _ (SchemaEvaluationRun.arena _ _ _ _ _ _ _ Hdomain))|].
 split;[exact Hcs|]. repeat split;reflexivity.
Qed.
End SchemaEvaluationIndexCountEntry.
