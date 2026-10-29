From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata Guarantees.
From NativeProof Require Import Index SipHash ObservedLocal SchemaRepresentation SchemaMarking SchemaEvaluation
 SchemaEvaluationRun SchemaEvaluationInitial SchemaEvaluationBoundedCell SchemaEvaluationIndexRun SchemaEvaluationIndexCell SchemaMetadata SchemaInstanceStorage SchemaInstanceCompletion Representation ClassStorage ClassLookup
 SchemaEvaluationIndexReady SchemaEvaluationIndexBudget SchemaEvaluationGeneralBudget SchemaEvaluationIndexBounds SchemaEvaluationIndexCountEntry SchemaEvaluationIndexCountPractical SchemaUniformBudget SchemaGraph FormulaTopology HistoryRefinement NameRepresentation SemanticFrames InternalIO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationUniformEntry.
Import IndexExecution SipHashExecution ObservedLocal.
Theorem generated expression_cap field_cap initialF initialB initialC s bs ns logical root cert rho observations :
 SchemaRepresentation.represents s logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> ns vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 HistoryRefinement.represents s logical -> NameRepresentation.represents s (Protocol.bindings logical) ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 meta_value s 8=0 -> meta_value s 18<>0 -> (length (Protocol.formulas logical)<=initialF)%nat ->
 SchemaEvaluationIndexCell.bounded s (Protocol.formulas logical) (Protocol.classes logical) initialB ->
 SchemaEvaluationGeneralBudget.parameters s root s (Protocol.classes logical) rho ->
 (length (Protocol.expressions logical)<=expression_cap)%nat ->
 (length (Protocol.classes logical)<=initialC)%nat -> SchemaUniformBudget.encoded_fields s field_cap ->
 Z.of_nat (SchemaUniformBudget.formula_after initialF (SchemaUniformBudget.slots expression_cap))<=SchemaEvaluationBoundedCell.bound ->
 Z.of_nat (SchemaUniformBudget.index_after expression_cap field_cap initialB (SchemaUniformBudget.slots expression_cap))<=maximum ->
 Z.of_nat (5*(SchemaUniformBudget.formula_after initialF (SchemaUniformBudget.slots expression_cap)*SchemaUniformBudget.formula_after initialF (SchemaUniformBudget.slots expression_cap))+1)<=maximum ->
 Z.of_nat (initialC+SchemaUniformBudget.slots expression_cap+1)<=maximum ->
 exists final fs classes,
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,observations)) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 HistoryRefinement.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 NameRepresentation.represents final (Protocol.bindings logical) /\
 SchemaRepresentation.represents final (SchemaInstanceCompletion.prepared logical fs classes) /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length fs) /\ meta_value final 8=0 /\
 InternalIO.preserves s final /\ (exists extra,fs=Protocol.formulas logical++extra) /\ (exists extra,classes=Protocol.classes logical++extra) /\
 (length classes<=length (Protocol.classes logical)+SchemaMarking.size root)%nat /\
 (length classes<=initialC+SchemaUniformBudget.slots expression_cap)%nat /\
 (length fs<=SchemaUniformBudget.formula_after initialF (SchemaUniformBudget.slots expression_cap))%nat /\
 SchemaEvaluationIndexCell.bounded final fs classes (SchemaUniformBudget.index_after expression_cap field_cap initialB (SchemaUniformBudget.slots expression_cap)) /\
 (Guarantees.safe logical -> Guarantees.safe (SchemaInstanceCompletion.prepared logical fs classes)) /\
 ((exists p,Schemata.infer rho 0 cert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value fs (meta_value final 0) p /\ meta_value final 18<>0) \/
  (Schemata.infer rho 0 cert=None /\ meta_value final 18=0)).
Proof.
 intros Hschema Hlookup Hgrid Hroot Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid
   Hcapacity Hbounded Hparameters Hexpressions HclassCap Hfields HF HB Hfuel HC.
 assert (HrootBound:(root<length (memory s arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length s _ (SchemaRepresentation.metadata s logical Hschema)). apply nth_error_Some;congruence. }
 assert (Hwidth:(SchemaGraph.width root<=expression_cap)%nat).
 { assert (HlogicalRoot:(root<length (Protocol.expressions logical))%nat) by (apply nth_error_Some;congruence).
   unfold SchemaGraph.width;lia. }
 pose proof (SchemaUniformBudget.scalar s root expression_cap field_cap initialF initialB initialC (length (Protocol.classes logical))
   (SchemaGraph.represented_ordered s logical Hschema) HrootBound Hwidth Hfields HclassCap Hfuel HC) as Hscalar.
 destruct (SchemaEvaluationIndexCountPractical.generated (SchemaUniformBudget.formula_ceiling expression_cap initialF)
   (SchemaUniformBudget.index_ceiling expression_cap field_cap initialB) s bs ns logical root cert rho observations
   (SchemaUniformBudget.formula_ceiling_word expression_cap initialF HF) (SchemaUniformBudget.formula_ceiling_step expression_cap initialF)
   (SchemaUniformBudget.index_ceiling_word expression_cap field_cap initialB HB) (SchemaUniformBudget.index_ceiling_step expression_cap field_cap initialB)
   Hschema Hlookup Hgrid Hroot Harena Hclasses Hgood Htop Hfalse Hhistory Hnames Hmeta Hsip Herror Hvalid Hcapacity Hbounded Hparameters Hscalar)
   as (final & fs & classes & Hrun & HarenaNext & HclassNext & HhistoryNext & HnamesNext & HschemaNext & HgoodNext & HtopNext & HerrorNext & Hio & Hfs & Hcs & HclassCount & HformulaCount & HindexBound & Hsafe & Hresult).
 assert (Hsize:(SchemaMarking.size root<=SchemaUniformBudget.slots expression_cap)%nat).
 { unfold SchemaMarking.size,SchemaUniformBudget.slots,SchemaGraph.width in *;nia. }
 assert (HclassTotal:(length classes<=initialC+SchemaUniformBudget.slots expression_cap)%nat) by lia.
 pose proof (SchemaUniformBudget.formula_ceiling_terminal expression_cap initialF (SchemaMarking.size root)) as HFterminal.
 pose proof (SchemaUniformBudget.index_ceiling_terminal expression_cap field_cap initialB (SchemaMarking.size root)) as HBterminal.
 assert (HformulaTotal:(length fs<=SchemaUniformBudget.formula_after initialF (SchemaUniformBudget.slots expression_cap))%nat) by lia.
 assert (HindexTotal:SchemaEvaluationIndexCell.bounded final fs classes
   (SchemaUniformBudget.index_after expression_cap field_cap initialB (SchemaUniformBudget.slots expression_cap))).
 { exact (SchemaEvaluationIndexCell.bounded_mono final fs classes _ _ HBterminal HindexBound). }
 exists final,fs,classes. repeat first [assumption|split].
Qed.
End SchemaEvaluationUniformEntry.
