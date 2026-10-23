From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaPair SchemaEvaluation SchemaEvaluationControl SchemaMarking ArrayFacts InternTail Overflow.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaPairStep.
Import IndexExecution SipHashExecution ObservedLocal SchemaPair SchemaEvaluationControl.
Definition written (s:Machine) key id := withMemory s (modifyArray (memory s) arraydef_0__schemaValues key id).
Lemma written_other s key id name : name<>arraydef_0__schemaValues -> memory (written s key id) name=memory s name.
Proof. intro Hname. unfold written. cbn [memory withMemory]. now apply InternTailExecution.modify_other. Qed.
Lemma written_length s key id : length (memory (written s key id) arraydef_0__schemaValues)=length (memory s arraydef_0__schemaValues).
Proof. unfold written. cbn [memory withMemory]. rewrite InternTailExecution.modify_same. apply length_insert. Qed.
Lemma written_same s key id : (key<length (memory s arraydef_0__schemaValues))%nat ->
 SchemaEvaluation.value (written s key id) key=id.
Proof. intro Hkey. unfold SchemaEvaluation.value,written. cbn [memory withMemory]. rewrite InternTailExecution.modify_same. now apply OverflowExecution.nth_insert_same. Qed.
Lemma written_preserves s key id index : index<>key -> SchemaEvaluation.value (written s key id) index=SchemaEvaluation.value s index.
Proof. intro Hindex. unfold SchemaEvaluation.value,written. cbn [memory withMemory]. rewrite InternTailExecution.modify_same. now apply ArrayFacts.nth_insert_other. Qed.
Theorem generated_output (f:Frame) width remaining outer_remaining key observations :
 (0<length (memory (machine f) arraydef_0__meta))%nat ->
 nums f vardef_0__schemaInstance_key=Z.of_nat key ->
 (key<length (memory (machine f) arraydef_0__schemaValues))%nat ->
 execLocalObserved (dropWithinLoop (raw_output width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(setMachine f (written (machine f) key (meta_value (machine f) 0)),observations)).
Proof.
 intros Hmeta Hkey Hbound. unfold raw_output.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine];rewrite ?Nat2Z.id;first [exact Hbound|lia])
 |progress rewrite Hkey|progress rewrite Nat2Z.id
 |progress cbn [dropWithinLoop Action_rect]]. reflexivity.
Qed.
Theorem generated_compute which (f middle:Frame) width remaining outer_remaining kind key observations :
 nums f vardef_0__schemaInstance_kind=kind -> nums middle vardef_0__schemaInstance_kind=kind -> applies which kind ->
 execLocalObserved (dropWithinLoop (selected which width remaining outer_remaining)) (f,observations)=Some (KeepGoing,(middle,observations)) ->
 (0<length (memory (machine middle) arraydef_0__meta))%nat ->
 nums middle vardef_0__schemaInstance_key=Z.of_nat key ->
 (key<length (memory (machine middle) arraydef_0__schemaValues))%nat ->
 execLocalObserved (dropWithinLoop (SchemaEvaluation.compute_body width remaining outer_remaining)) (f,observations)=
 Some (KeepGoing,(setMachine middle (written (machine middle) key (meta_value (machine middle) 0)),observations)).
Proof.
 intros Hkind Hmiddle Happly Hrun Hmeta Hkey Hbound.
 rewrite (generated_dispatch which f middle width remaining outer_remaining kind observations Hkind Hmiddle Happly Hrun).
 now apply generated_output.
Qed.
Definition descriptor_frame (f:Frame) (raw:Z*Z*Z*Z*Z*Z*Z) :=
 let '(kind,a,b,c,d,_,_):=raw in
 setNum (setNum (setNum (setNum (setNum f vardef_0__schemaInstance_kind kind)
   vardef_0__schemaInstance_a a) vardef_0__schemaInstance_b b) vardef_0__schemaInstance_c c) vardef_0__schemaInstance_d d.
Definition marked_with width remaining outer_remaining (work:LoopAction unit) : LoopAction unit := ltac:(
 let code:=eval cbv beta iota zeta delta [SchemaEvaluation.marked_body] in (SchemaEvaluation.marked_body width remaining outer_remaining) in
 let rest:=eval cbv beta iota zeta delta [SchemaEvaluation.compute_body] in (SchemaEvaluation.compute_body width remaining outer_remaining) in
 let family:=eval pattern rest in code in lazymatch family with ?family _=>exact (family work) end).
Lemma actual_marked width remaining outer_remaining : SchemaEvaluation.marked_body width remaining outer_remaining=
 marked_with width remaining outer_remaining (SchemaEvaluation.compute_body width remaining outer_remaining).
Proof. reflexivity. Qed.
Theorem generated_descriptor (f:Frame) width remaining outer_remaining node raw (work:LoopAction unit) observations :
 SchemaEvaluation.depth width outer_remaining=Z.of_nat node ->
 nth_error (memory (machine f) arraydef_0__schemaNodes) node=Some raw ->
 execLocalObserved (dropWithinLoop (marked_with width remaining outer_remaining work)) (f,observations)=
 execLocalObserved (dropWithinLoop work) (descriptor_frame f raw,observations).
Proof.
 intros Hnode Hraw.
 assert (Hbound:(node<length (memory (machine f) arraydef_0__schemaNodes))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ (0,0,0,0,0,0,0) Hraw) as Hnth.
 unfold SchemaEvaluation.depth in Hnode. destruct raw as [[[[[[kind a] b] c] d] typ] arity].
 unfold marked_with,descriptor_frame.
 repeat first [progress cbn [optionBind fst snd bind]
 |progress rewrite drop_assoc|progress rewrite drop_lift
 |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];rewrite ?Hnode,?Nat2Z.id;exact Hbound)
 |progress rewrite Hnode|progress rewrite Nat2Z.id
 |match goal with |- context [List.nth ?i ?xs ?zero]=>
   let expression:=constr:(List.nth i xs zero) in
   let Hsame:=fresh in assert (Hsame:expression=(kind,a,b,c,d,typ,arity)) by exact Hnth;rewrite Hsame;clear Hsame end
 |progress cbn [machine setMachine setNum]]. reflexivity.
Qed.
End SchemaPairStep.
