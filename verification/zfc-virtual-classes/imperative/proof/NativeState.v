From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash Representation ClassStorage HistoryRefinement NameRepresentation SchemaRepresentation ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeState.
Import IndexExecution SipHashExecution.
(** The whole logical protocol state, including the semantics of immutable
    schema descriptors, is represented at a command boundary. *)
Record represents (native:Machine) (logical:Protocol.state) : Prop := Represents {
 formula_representation : NativeRepresentation.canonical_arena native (Protocol.formulas logical);
 class_representation : ClassStorage.represents native (Protocol.formulas logical) (Protocol.classes logical);
 history_representation : HistoryRefinement.represents native logical;
 name_representation : NameRepresentation.represents native (Protocol.bindings logical);
 schema_representation : SchemaRepresentation.represents native logical
}.
Record empty_registries (native:Machine) : Prop := EmptyRegistries {
 empty_classes : memory native arraydef_0__classes=[];
 empty_names : memory native arraydef_0__names=[];
 empty_bindings : memory native arraydef_0__bindings=[];
 empty_schemas : memory native arraydef_0__schemaNodes=[];
 empty_class_count : meta_value native 2=0;
 empty_history_count : meta_value native 3=0;
 empty_binding_count : meta_value native 4=0;
 empty_name_count : meta_value native 5=0;
 empty_schema_count : meta_value native 16=0
}.
Lemma initial native : empty_registries native -> NativeRepresentation.canonical_arena native [SetTheory.falsity] ->
 represents native Protocol.initial.
Proof.
 intros Hempty Harena. constructor;[exact Harena| | | |].
 - unfold ClassStorage.represents. cbn [Protocol.initial Protocol.formulas Protocol.classes].
   rewrite (empty_class_count _ Hempty),(empty_classes _ Hempty). split;[reflexivity|constructor].
 - unfold HistoryRefinement.represents. cbn [Protocol.initial Protocol.history firstn map].
   rewrite (empty_history_count _ Hempty). split;reflexivity.
 - unfold NameRepresentation.represents. cbn [Protocol.initial Protocol.bindings].
   rewrite (empty_names _ Hempty),(empty_bindings _ Hempty),(empty_binding_count _ Hempty),(empty_name_count _ Hempty).
   split;[reflexivity|]. split;[reflexivity|]. split;[change (0<=maximum);unfold maximum;lia|]. split;[change (0<=maximum);unfold maximum;lia|].
   constructor.
 - apply SchemaRepresentation.empty;[reflexivity|exact (empty_schema_count _ Hempty)|exact (empty_schemas _ Hempty)].
Qed.
Lemma output native logical bytes : represents native logical -> represents (withOutput native bytes) logical.
Proof.
 intros Hrep. constructor.
 - exact (ArenaFrame.storage_arena native _ _ (ArenaFrame.storage_output native bytes) (formula_representation _ _ Hrep)).
 - exact (class_representation _ _ Hrep).
 - exact (history_representation _ _ Hrep).
 - exact (name_representation _ _ Hrep).
 - eapply SchemaRepresentation.transport;[exact (schema_representation _ _ Hrep)|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.
End NativeState.
