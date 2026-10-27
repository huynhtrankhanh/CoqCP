From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal SchemaRepresentation SchemaGraph SchemaMarking
 SchemaEvaluation SchemaEvaluationRun SchemaEvaluationInitial SchemaEvaluationBudget Representation ClassStorage ClassLookup FormulaTopology.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationFree.
Import IndexExecution SipHashExecution ObservedLocal.
(** This domain contains arbitrarily many saved proof/MP nodes. Its resource
    condition is the checked grid size; no opaque future-success premise is
    required. It supplements the general evaluator's explicit resource domain. *)
Theorem generated s bs ns logical root cert rho observations :
 SchemaRepresentation.represents s logical -> nth_error (Protocol.expressions logical) root=Some (Protocol.PE cert) ->
 SchemaEvaluationBudget.free_reachable s root -> Z.of_nat (SchemaMarking.size root)<=maximum ->
 ns vardef_0__schemaInstance_root=Z.of_nat root ->
 NativeRepresentation.canonical_arena s (Protocol.formulas logical) ->
 ClassStorage.represents s (Protocol.formulas logical) (Protocol.classes logical) -> ClassLookup.wellformed s ->
 FormulaTopology.ordered s (length (Protocol.formulas logical)) -> nth_error (Protocol.formulas logical) 0=Some SetTheory.falsity ->
 (31<length (memory s arraydef_0__meta))%nat -> (0<length (memory s arraydef_0__sipState))%nat ->
 meta_value s 8=0 -> meta_value s 18<>0 ->
 exists final fs classes,
 execObserved (funcdef_0__schemaInstance bs ns) (s,observations)=Some (tt,(final,observations)) /\
 NativeRepresentation.canonical_arena final fs /\ ClassStorage.represents final fs classes /\
 ClassLookup.wellformed final /\ FormulaTopology.ordered final (length fs) /\ meta_value final 8=0 /\
 (exists extra,fs=Protocol.formulas logical++extra) /\ (exists extra,classes=Protocol.classes logical++extra) /\
 ((exists p,Schemata.infer rho 0 cert=Some p /\ SetTheory.derives p /\
    SchemaEvaluation.formula_value fs (meta_value final 0) p /\ meta_value final 18<>0) \/
  (Schemata.infer rho 0 cert=None /\ meta_value final 18=0)).
Proof.
 intros Hschema Hlookup Hfree Hroom Hroot Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror Hvalid.
 set (before := ({|machine:=s;bools:=bs;nums:=ns|}:SchemaEvaluation.Frame)).
 assert (Hfits:forall marked,SchemaEvaluationInitial.marked_state before root marked ->
   SchemaEvaluationRun.fits s logical root rho (SchemaMarking.size root) 0 (Protocol.formulas logical) (Protocol.classes logical) marked).
 { intros marked Hmarked. apply SchemaEvaluationBudget.fits_free;[exact Hfree|].
   exact (SchemaEvaluationInitial.untouched before root marked Hmarked arraydef_0__schemaNodes ltac:(discriminate) ltac:(discriminate)). }
 destruct (SchemaEvaluationInitial.generated_body before logical root cert rho observations Hschema Hlookup Hroom Hroot
   Harena Hclasses Hgood Htop Hfalse Hmeta Hsip Herror Hvalid Hfits)
   as (marked & after & fs & classes & Hmarked & Hrun & Hdomain & Hframe & Hfs & Hcs & Hresult).
 exists (machine after),fs,classes. split.
 - change (execObserved (eliminateLocalVariables bs ns funcdef_0__schemaInstance_body) (s,observations)=Some (tt,(machine after,observations))).
   rewrite (ObservedLocal.eliminate_correct funcdef_0__schemaInstance_body bs ns s observations). change (optionBind (execLocalObserved funcdef_0__schemaInstance_body (before,observations))
    (fun response=>Some (fst response,(machine (fst (snd response)),snd (snd response))))=Some (tt,(machine after,observations))).
   now rewrite Hrun.
 - split;[exact (SchemaEvaluationRun.arena _ _ _ _ _ _ _ Hdomain)|].
   split;[exact (SchemaEvaluationRun.class_meaning _ _ _ _ _ _ _ Hdomain)|].
   split;[exact (SchemaEvaluationRun.class_words _ _ _ _ _ _ _ Hdomain)|].
   split;[exact (SchemaEvaluationRun.topology _ _ _ _ _ _ _ Hdomain)|].
   split;[exact (SchemaEvaluationRun.error_clear _ _ _ _ _ _ _ Hdomain)|].
   split;[exact Hfs|]. split;[exact Hcs|exact Hresult].
Qed.
End SchemaEvaluationFree.
