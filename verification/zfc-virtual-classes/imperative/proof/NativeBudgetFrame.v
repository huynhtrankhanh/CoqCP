From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash NativeState NativeSession NativeNameCompact
 NativeFullTapeStep NativeDialogueComposition NativeBasicDispatcher CommandLoop
 SchemaEvaluationIndexCell SchemaInstanceCheckedResources NativeSchemaFieldBounds
 NativeSchemaUniformBoundary FormulaTopology HashTable ClassLookup SchemaUniformBudget.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeBudgetFrame.
Import IndexExecution SipHashExecution.

(** Changing pending input or output leaves every permanent arena and registry
    unchanged. Metadata values may change, but allocation lengths do not. *)
Definition frame (before after:Machine) :=
 (forall watched,watched<>arraydef_0__meta -> memory after watched=memory before watched) /\
 length(memory after arraydef_0__meta)=length(memory before arraydef_0__meta).
Lemma input_frame native bytes : frame native (withInput native bytes).
Proof. split;reflexivity. Qed.
Lemma output_frame native bytes : frame native (withOutput native bytes).
Proof. split;reflexivity. Qed.
Lemma metadata_frame native slot value : frame native (store_meta native slot value).
Proof. split;[intros watched Hwatched;now apply store_meta_other|apply store_meta_length]. Qed.
Lemma frame_trans first middle last : frame first middle -> frame middle last -> frame first last.
Proof. intros [Hfirst HfirstLength] [Hlast HlastLength]. split.
 - intros watched Hwatched. now rewrite Hlast,Hfirst by exact Hwatched.
 - now rewrite HlastLength,HfirstLength.
Qed.
Lemma entered_frame native request tail : frame native (NativeFullTapeStep.entered native request tail).
Proof.
 unfold NativeFullTapeStep.entered,CommandLoopExecution.pending_state.
 eapply frame_trans;[apply input_frame|apply metadata_frame].
Qed.
Lemma bounded_frame before after fs classes bound : frame before after ->
 SchemaEvaluationIndexCell.bounded before fs classes bound ->
 SchemaEvaluationIndexCell.bounded after fs classes bound.
Proof.
 intros [Harrays Hmeta] Hbounded.
 exact(SchemaEvaluationIndexCell.bounded_array_frame before after fs classes bound
   (Harrays arraydef_0__formulas ltac:(discriminate)) Hbounded).
Qed.
Lemma fields_frame before after cap : frame before after ->
 NativeSchemaFieldBounds.fields before cap -> NativeSchemaFieldBounds.fields after cap.
Proof.
 intros [Harrays Hmeta] Hfields.
 exact(NativeSchemaFieldBounds.fields_frame before after cap
   (Harrays arraydef_0__schemaNodes ltac:(discriminate)) Hfields).
Qed.
Lemma top_frame before after count : frame before after ->
 FormulaTopology.ordered before count -> FormulaTopology.ordered after count.
Proof.
 intros [Harrays Hmeta] Htop. apply(FormulaTopology.same before);[exact Htop|].
 intros parent Hparent. unfold HashTableInvariant.tuple_at. now rewrite Harrays by discriminate.
Qed.
Lemma class_wellformed_frame before after : frame before after ->
 ClassLookup.wellformed before -> ClassLookup.wellformed after.
Proof. intros [Harrays Hmeta]. apply ClassLookup.transport. apply Harrays;discriminate. Qed.
Lemma compact_frame before after logical : frame before after ->
 NativeNameCompact.compact before logical -> NativeNameCompact.compact after logical.
Proof.
 intros [Harrays Hmeta]. unfold NativeNameCompact.compact.
 apply NativeNameCompact.compact_same. apply Harrays;discriminate.
Qed.
Lemma budget_frame before after logical E N F B C : frame before after ->
 NativeSchemaUniformBoundary.budget before logical E N F B C ->
 NativeSchemaUniformBoundary.budget after logical E N F B C.
Proof.
 intros [Harrays Hmeta]. apply NativeSchemaUniformBoundary.budget_transport;apply Harrays;discriminate.
Qed.
Lemma entered_bounded native request tail fs classes bound :
 SchemaEvaluationIndexCell.bounded native fs classes bound ->
 SchemaEvaluationIndexCell.bounded (NativeFullTapeStep.entered native request tail) fs classes bound.
Proof. apply bounded_frame. apply entered_frame. Qed.
Lemma entered_fields native request tail cap :
 NativeSchemaFieldBounds.fields native cap ->
 NativeSchemaFieldBounds.fields (NativeFullTapeStep.entered native request tail) cap.
Proof. apply fields_frame. apply entered_frame. Qed.
Lemma entered_top native request tail count : FormulaTopology.ordered native count ->
 FormulaTopology.ordered (NativeFullTapeStep.entered native request tail) count.
Proof. apply top_frame. apply entered_frame. Qed.
Lemma entered_class_wellformed native request tail : ClassLookup.wellformed native ->
 ClassLookup.wellformed (NativeFullTapeStep.entered native request tail).
Proof. apply class_wellformed_frame. apply entered_frame. Qed.
Lemma entered_compact native request tail logical : NativeNameCompact.compact native logical ->
 NativeNameCompact.compact (NativeFullTapeStep.entered native request tail) logical.
Proof. apply compact_frame. apply entered_frame. Qed.
Lemma entered_budget native request tail logical E N F B C :
 NativeSchemaUniformBoundary.budget native logical E N F B C ->
 NativeSchemaUniformBoundary.budget (NativeFullTapeStep.entered native request tail) logical E N F B C.
Proof. apply budget_frame. apply entered_frame. Qed.
Lemma entered_state native request tail logical : NativeState.represents native logical ->
 NativeState.represents (NativeFullTapeStep.entered native request tail) logical.
Proof.
 intro Hstate. unfold NativeFullTapeStep.entered,CommandLoopExecution.pending_state.
 apply NativeSession.state_meta;try lia. now apply NativeSession.state_input.
Qed.
Lemma entered_meta_other native request tail slot : slot<>15%nat ->
 meta_value(NativeFullTapeStep.entered native request tail)slot=meta_value native slot.
Proof.
 intro Hslot. unfold NativeFullTapeStep.entered,CommandLoopExecution.pending_state.
 rewrite meta_store_other by exact Hslot. reflexivity.
Qed.
Lemma entered_lengths native request tail watched :
 length(memory(NativeFullTapeStep.entered native request tail)watched)=length(memory native watched).
Proof.
 destruct(decide(watched=arraydef_0__meta)) as [->|Hwatched].
 - apply NativeFullTapeStep.entered_meta_length.
 - now rewrite NativeFullTapeStep.entered_arrays by exact Hwatched.
Qed.
Lemma entered_pending native request tail : (15<length(memory native arraydef_0__meta))%nat ->
 meta_value(NativeFullTapeStep.entered native request tail)15=NativeBasicDispatcher.first(Protocol.opcode request)+1.
Proof.
 intro Hmeta. unfold NativeFullTapeStep.entered,CommandLoopExecution.pending_state.
 apply meta_store_same. exact Hmeta.
Qed.
Lemma entered_io native request tail :
 stdin(NativeFullTapeStep.entered native request tail)=NativeBasicDispatcher.rest request++tail /\
 stdout(NativeFullTapeStep.entered native request tail)=stdout native.
Proof. split;reflexivity. Qed.
Lemma entered_boundary native request tail logical : NativeDialogueComposition.boundary native logical ->
 NativeDialogueComposition.boundary (NativeFullTapeStep.entered native request tail) logical.
Proof.
 intros [Hstate Htoken Hprint Herror Hrunning]. constructor.
 - now apply entered_state.
 - now rewrite entered_lengths.
 - now rewrite entered_lengths.
 - now rewrite entered_meta_other by lia.
 - now rewrite entered_meta_other by lia.
Qed.

(** Startup already constructs the canonical falsity node and empty permanent
    registries. Its index bound is zero; empty descriptors fit every cap. *)
Lemma initial_bounded native : NativeState.represents native Protocol.initial ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas Protocol.initial) (Protocol.classes Protocol.initial) 0.
Proof.
 intro Hstate.
 exact(SchemaInstanceCheckedResources.initial_bounded native Protocol.initial
   (NativeState.formula_representation _ _ Hstate)).
Qed.
Lemma initial_fields native cap : NativeState.empty_registries native -> NativeSchemaFieldBounds.fields native cap.
Proof.
 intros Hempty node raw Hlookup. rewrite(NativeState.empty_schemas _ Hempty) in Hlookup.
 destruct node;discriminate.
Qed.
Theorem initial native cap : NativeState.represents native Protocol.initial -> NativeState.empty_registries native ->
 SchemaEvaluationIndexCell.bounded native (Protocol.formulas Protocol.initial) (Protocol.classes Protocol.initial) 0 /\
 NativeSchemaFieldBounds.fields native cap /\ NativeNameCompact.compact native Protocol.initial /\
 ClassLookup.wellformed native /\
 length(Protocol.formulas Protocol.initial)=1%nat /\ length(Protocol.classes Protocol.initial)=0%nat /\
 length(Protocol.expressions Protocol.initial)=0%nat /\ NativeNameCompact.bytes Protocol.initial=0%nat.
Proof.
 intros Hstate Hempty. split;[now apply initial_bounded|]. split;[now apply initial_fields|].
 split;[apply NativeNameCompact.initial_compact;exact(NativeState.empty_names _ Hempty)|].
 split;[apply ClassLookup.empty;exact(NativeState.empty_classes _ Hempty)|]. repeat split;reflexivity.
Qed.
End NativeBudgetFrame.
