From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal SchemaRepresentation SchemaMarking SchemaEvaluation
 SchemaEvaluationRun SchemaEvaluationIndexCountRun SchemaEvaluationInitial SchemaEvaluationBoundedCell SchemaEvaluationIndexRun SchemaEvaluationIndexCell SchemaMetadata SchemaInstanceStorage SchemaInstanceCompletion Representation ClassStorage ClassLookup
 SchemaEvaluationIndexReady SchemaEvaluationIndexBudget SchemaEvaluationGeneralBudget SchemaEvaluationIndexBounds SchemaEvaluationIndexCountEntry FormulaTopology HistoryRefinement NameRepresentation SemanticFrames InternalIO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationIndexCountPractical.
Import IndexExecution SipHashExecution ObservedLocal.
Theorem entry_resources (ceiling index_ceiling:nat->nat) s bs ns logical root rho :
 (forall key,Z.of_nat (ceiling key)<=SchemaEvaluationBoundedCell.bound) ->
 (forall key,Z.of_nat (index_ceiling key)<=maximum) ->
 SchemaRepresentation.represents s logical ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat -> meta_value s 8=0 ->
 (length (Protocol.formulas logical)<=ceiling 0%nat)%nat ->
 SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) (index_ceiling 0%nat) ->
 SchemaEvaluationGeneralBudget.parameters s root s (Protocol.classes logical) rho ->
 SchemaEvaluationIndexReady.scalar ceiling index_ceiling s root (length (Protocol.classes logical)) ->
 SchemaEvaluationIndexCountEntry.resources ceiling index_ceiling s bs ns logical root rho.
Proof.
 intros HceilingWord HindexWord Hschema Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror
   Hcapacity Hbounded Hparameters Hscalar marked Hmarked.
 pose proof (SchemaEvaluationInitial.marked_domain (SchemaEvaluationIndexCountEntry.initial s bs ns) logical root rho marked
   Hmarked Hschema Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror) as Hdomain.
 eapply SchemaEvaluationIndexCountRun.fits_from_index.
 apply (SchemaEvaluationIndexReady.fits ceiling index_ceiling HceilingWord HindexWord s logical root rho
   (SchemaMarking.size root) 0 (Protocol.formulas logical) (Protocol.classes logical) marked (length (Protocol.classes logical))
   Hdomain Hscalar).
 - eapply SchemaEvaluationGeneralBudget.parameters_transport.
   + exact (SchemaEvaluationInitial.untouched _ _ _ Hmarked arraydef_0__schemaArguments ltac:(discriminate) ltac:(discriminate)).
   + exists [];now rewrite app_nil_r.
   + exact Hparameters.
 - exact Hcapacity.
 - destruct Hbounded as [Hraw Hbounds]. split;[|exact Hbounds].
   eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact Hraw].
   exact (SchemaEvaluationInitial.untouched _ _ _ Hmarked arraydef_0__formulas ltac:(discriminate) ltac:(discriminate)).
 - lia.
Qed.
Theorem generated (ceiling index_ceiling:nat->nat) s bs ns logical root cert rho observations :
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
 meta_value s 8=0 -> meta_value s 18<>0 -> (length (Protocol.formulas logical)<=ceiling 0%nat)%nat ->
 SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) (index_ceiling 0%nat) ->
 SchemaEvaluationGeneralBudget.parameters s root s (Protocol.classes logical) rho ->
 SchemaEvaluationIndexReady.scalar ceiling index_ceiling s root (length (Protocol.classes logical)) ->
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
 intros HceilingWord HceilingStep HindexWord HindexStep Hschema Hlookup Hroom Hroot Harena Hclasses Hgood Htop Hfalse
   Hhistory Hnames Hmeta Hsip Herror Hvalid Hcapacity Hbounded Hparameters Hscalar.
 eapply SchemaEvaluationIndexCountEntry.generated;try eassumption.
 eapply entry_resources;eassumption.
Qed.
End SchemaEvaluationIndexCountPractical.
