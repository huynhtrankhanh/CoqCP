From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaMarking SchemaMarkingRun SchemaGraph SchemaMetadata
 SchemaRepresentation SchemaEvaluation SchemaEvaluationRun FormulaProjection Representation FormulaTopology ClassStorage ClassLookup HashTable.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationInitial.
Import IndexExecution SipHashExecution ObservedLocal.
(** All clauses describe concrete arrays and indices. This relation contains no
    program execution or success assumption. *)
Record marked_state (before:SchemaEvaluation.Frame) root (after:SchemaEvaluation.Frame) : Prop := MarkedState {
 marked_exact : forall node depth,(node<SchemaGraph.width root)%nat -> (depth<SchemaGraph.width root)%nat ->
  (SchemaMarking.cell (machine after) (SchemaGraph.key root node depth)<>0 <-> SchemaGraph.reachable (machine before) root node depth);
 marked_arrays : SchemaMarkingRun.same_arrays (SchemaMarking.grown (machine before) root) (machine after);
 marked_capacity : (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaMarks))%nat;
 values_capacity : (SchemaMarking.size root<=length (memory (machine after) arraydef_0__schemaValues))%nat;
 marked_root : nums after vardef_0__schemaInstance_root=Z.of_nat root;
 marked_width : nums after vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root)
}.
Lemma untouched before root after : marked_state before root after ->
 forall name,name<>arraydef_0__schemaMarks -> name<>arraydef_0__schemaValues ->
 memory (machine after) name=memory (machine before) name.
Proof.
 intros Hmarked name Hmarks Hvalues. rewrite (marked_arrays _ _ _ Hmarked name Hmarks).
 now apply SchemaMarking.grown_other.
Qed.
Lemma meta_same before root after slot : marked_state before root after ->
 meta_value (machine after) slot=meta_value (machine before) slot.
Proof. intro H. unfold meta_value. now rewrite (untouched _ _ _ H) by discriminate. Qed.
Lemma projection before root after : marked_state before root after ->
 FormulaProjection.storage (machine before) (machine after).
Proof.
 intro Hmarked. split;[now rewrite (untouched _ _ _ Hmarked) by discriminate|]. split.
 - intros name Hneeded. apply (untouched _ _ _ Hmarked);unfold FormulaProjection.needed in Hneeded;
   destruct Hneeded as [Heq|[Heq|[Heq|Heq]]];subst name;discriminate.
 - repeat split;now apply (meta_same _ _ _ _ Hmarked).
Qed.
Theorem marked_domain before logical root rho after :
 marked_state before root after -> SchemaRepresentation.represents (machine before) logical ->
 NativeRepresentation.canonical_arena (machine before) (Protocol.formulas logical) ->
 ClassStorage.represents (machine before) (Protocol.formulas logical) (Protocol.classes logical) ->
 ClassLookup.wellformed (machine before) -> FormulaTopology.ordered (machine before) (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 (31<length (memory (machine before) arraydef_0__meta))%nat ->
 (0<length (memory (machine before) arraydef_0__sipState))%nat -> meta_value (machine before) 8=0 ->
 SchemaEvaluationRun.domain (machine before) logical root rho (Protocol.formulas logical) (Protocol.classes logical) after.
Proof.
 intros Hmarked Hschemas Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror. constructor.
 - exact (FormulaProjection.storage_arena _ _ _ (projection _ _ _ Hmarked) Harena).
 - unfold ClassStorage.represents in *. rewrite (meta_same _ _ _ _ Hmarked),(untouched _ _ _ Hmarked) by discriminate. exact Hclasses.
 - unfold ClassLookup.wellformed in *. now rewrite (untouched _ _ _ Hmarked) by discriminate.
 - apply (FormulaTopology.same (machine before));[exact Htop|]. intros parent Hparent. unfold HashTableInvariant.tuple_at.
   now rewrite (untouched _ _ _ Hmarked) by discriminate.
 - exact Hfalse.
 - replace (SchemaEvaluationRun.logical_with logical (Protocol.formulas logical) (Protocol.classes logical)) with logical by (destruct logical;reflexivity).
   eapply SchemaRepresentation.transport;[exact Hschemas|exact (meta_same _ _ _ _ Hmarked)| |reflexivity|reflexivity|reflexivity].
   now apply (untouched _ _ _ Hmarked).
 - now apply (untouched _ _ _ Hmarked).
 - exact (marked_exact _ _ _ Hmarked).
 - now rewrite (untouched _ _ _ Hmarked) by discriminate.
 - now rewrite (untouched _ _ _ Hmarked) by discriminate.
 - exact (values_capacity _ _ _ Hmarked).
 - exact (marked_capacity _ _ _ Hmarked).
 - exact (marked_root _ _ _ Hmarked).
 - exact (marked_width _ _ _ Hmarked).
 - now rewrite (meta_same _ _ _ _ Hmarked).
Qed.
Theorem generated_marking (before:SchemaEvaluation.Frame) logical root rho observations :
 SchemaRepresentation.represents (machine before) logical ->
 (root<length (memory (machine before) arraydef_0__schemaNodes))%nat -> Z.of_nat (SchemaMarking.size root)<=maximum ->
 nums before vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena (machine before) (Protocol.formulas logical) ->
 ClassStorage.represents (machine before) (Protocol.formulas logical) (Protocol.classes logical) ->
 ClassLookup.wellformed (machine before) -> FormulaTopology.ordered (machine before) (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 (31<length (memory (machine before) arraydef_0__meta))%nat ->
 (0<length (memory (machine before) arraydef_0__sipState))%nat -> meta_value (machine before) 8=0 ->
 exists after,
  execLocalObserved (SchemaMarking.initial_with SchemaMarking.marked_pass) (before,observations)=Some (tt,(after,observations)) /\
  execLocalObserved funcdef_0__schemaInstance_body (before,observations)=execLocalObserved SchemaMarking.evaluation (after,observations) /\
  marked_state before root after /\
  SchemaEvaluationRun.domain (machine before) logical root rho (Protocol.formulas logical) (Protocol.classes logical) after /\
  meta_value (machine after) 18=meta_value (machine before) 18.
Proof.
 intros Hschemas Hroot Hroom Hrootnum Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror.
 destruct (SchemaMarkingRun.generated_represented_initial_marking root before logical observations Hschemas Hroot Hroom Hrootnum)
  as (after & Hinitial & Hbody & Hexact & Harrays & Hmarks & Hvalues & Hr & Hw).
 assert (Hmarked:marked_state before root after) by (constructor;assumption).
 exists after. split;[exact Hinitial|]. split;[exact Hbody|]. split;[exact Hmarked|]. split.
 - exact (marked_domain before logical root rho after Hmarked Hschemas Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror).
 - exact (meta_same _ _ _ _ Hmarked).
Qed.
(** The real procedure body includes initialization, complete dependency
    marking, the actual nested evaluation loops, and result publication. *)
Theorem generated_body (before:SchemaEvaluation.Frame) logical root rootCert rho observations :
 SchemaRepresentation.represents (machine before) logical ->
 nth_error (Protocol.expressions logical) root=Some (Protocol.PE rootCert) ->
 Z.of_nat (SchemaMarking.size root)<=maximum -> nums before vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena (machine before) (Protocol.formulas logical) ->
 ClassStorage.represents (machine before) (Protocol.formulas logical) (Protocol.classes logical) ->
 ClassLookup.wellformed (machine before) -> FormulaTopology.ordered (machine before) (length (Protocol.formulas logical)) ->
 nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 (31<length (memory (machine before) arraydef_0__meta))%nat ->
 (0<length (memory (machine before) arraydef_0__sipState))%nat ->
 meta_value (machine before) 8=0 -> meta_value (machine before) 18<>0 ->
 (forall marked,marked_state before root marked ->
   SchemaEvaluationRun.fits (machine before) logical root rho (SchemaMarking.size root) 0
     (Protocol.formulas logical) (Protocol.classes logical) marked) ->
 exists marked final next_fs next_classes,
  marked_state before root marked /\
  execLocalObserved funcdef_0__schemaInstance_body (before,observations)=Some (tt,(final,observations)) /\
  SchemaEvaluationRun.domain (machine before) logical root rho next_fs next_classes final /\
  SchemaEvaluationRun.frame marked final /\
  (exists extra,next_fs=Protocol.formulas logical++extra) /\
  (exists extra,next_classes=Protocol.classes logical++extra) /\
  ((exists p,Schemata.infer rho 0 rootCert=Some p /\ SetTheory.derives p /\
     SchemaEvaluation.formula_value next_fs (meta_value (machine final) 0) p /\ meta_value (machine final) 18<>0) \/
   (Schemata.infer rho 0 rootCert=None /\ meta_value (machine final) 18=0)).
Proof.
 intros Hschemas Hlookup Hroom Hrootnum Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror Hvalid Hfits.
 assert (Hroot:(root<length (memory (machine before) arraydef_0__schemaNodes))%nat).
 { rewrite (SchemaMetadata.represents_length _ _ (SchemaRepresentation.metadata _ _ Hschemas)).
   apply nth_error_Some;congruence. }
 destruct (generated_marking before logical root rho observations Hschemas Hroot Hroom Hrootnum Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror)
  as (marked & Hinitial & Hbody & Hmarked & Hdomain & Hmarkedvalid).
 destruct (SchemaEvaluationRun.generated_evaluation (machine before) logical root rootCert rho
   (Protocol.formulas logical) (Protocol.classes logical) marked observations Hschemas Hlookup Hdomain
   ltac:(now rewrite Hmarkedvalid) Hroom (Hfits marked Hmarked))
  as (final & next_fs & next_classes & Hrun & Hfinal & Hframe & Hfs & Hcs & Hresult).
 exists marked,final,next_fs,next_classes. split;[exact Hmarked|]. split;[now rewrite Hbody|].
 repeat first [assumption|split].
Qed.
End SchemaEvaluationInitial.
