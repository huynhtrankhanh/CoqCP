From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal SchemaRepresentation SchemaMarking SchemaEvaluation
 SchemaEvaluationRun SchemaEvaluationInitial SchemaInstanceStorage SchemaInstanceCompletion Representation ClassStorage ClassLookup
 FormulaTopology HistoryRefinement NameRepresentation SemanticFrames InternalIO SchemaEvaluationGeneralBudget SchemaInstanceEntry.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationClassEntry.
Import IndexExecution SipHashExecution ObservedLocal.
(** Exact native entry consequence of the class-count resource bound. The
    fragment permits CE graph parameters outside binders, but a PE root in this
    restricted fragment cannot depend on them: equality, membership, and axiom
    families remain outside this budget theorem. *)
Theorem generated s bs ns logical root cert rho observations :
 SchemaRepresentation.represents s logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 SchemaEvaluationGeneralBudget.fragment s root ->
 SchemaEvaluationGeneralBudget.parameters s root s (Protocol.classes logical) rho ->
 Z.of_nat (length (Protocol.classes logical)+SchemaMarking.size root)<=maximum -> ns vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 meta_value s 8=0 -> meta_value s 18<>0 ->
 exists final fs classes,
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,observations)) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 HistoryRefinement.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 NameRepresentation.represents final (Protocol.bindings logical) /\
 SchemaRepresentation.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length fs) /\ meta_value final 8=0 /\
 InternalIO.preserves s final /\ (exists extra,fs=Protocol.formulas logical++extra) /\ (exists extra,classes=Protocol.classes logical++extra) /\
 (Guarantees.safe logical -> Guarantees.safe (SchemaInstanceCompletion.prepared logical fs classes)) /\
 ((exists p,Schemata.infer rho 0 cert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value fs (meta_value final 0) p /\ meta_value final 18<>0) \/
  (Schemata.infer rho 0 cert=None /\ meta_value final 18=0)).
Proof.
 intros Hschema Hlookup Hfragment Hparameters Hbudget Hroot Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid.
 apply (SchemaInstanceEntry.generated s bs ns logical root cert rho observations Hschema Hlookup);
   try assumption.
 - lia.
 - now apply SchemaEvaluationGeneralBudget.entry_resources.
Qed.
End SchemaEvaluationClassEntry.
