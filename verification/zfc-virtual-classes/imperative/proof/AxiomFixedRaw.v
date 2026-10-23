From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  AxiomStructure AxiomRefl AxiomFixedCircuits FormulaCircuit InternLengths.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomFixedRaw.
Import IndexExecution SipHashExecution ObservedLocal.
Local Opaque funcdef_0__intern Imperative.update.
Ltac execute Hmeta :=
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine setNum];
       repeat first [rewrite store_meta_length
         |match goal with Hrun : execObserved (funcdef_0__intern ?bi ?ni) (?before,?trace)=Some (tt,(?after,?after_trace))
           |- context [length (memory ?after arraydef_0__meta)] =>
             rewrite (proj1 (InternLengths.observed_lengths before bi ni trace after after_trace Hrun)) end];lia)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       multimatch goal with Hrun : ?candidate=Some ?answer |- _ =>
         let Hsame:=fresh in assert (Hsame : expression=Some answer) by exact Hrun;
         rewrite Hsame;clear Hsame end end
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 13) with 13%nat by reflexivity
    |match goal with |- context [meta_value ?before 0] =>
       multimatch goal with Hvalue : meta_value before 0=?value |- _ => progress rewrite Hvalue end end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
Theorem generated_extensionality (f : AxiomRefl.Frame) built ids observations :
  (13<length (memory (machine f) arraydef_0__meta))%nat ->
  FormulaCircuit.executes observations AxiomFixedCircuits.extensionality_plan (machine f) [0] built ids ->
  exists after, execLocalObserved AxiomStructure.handler_9 (f,observations)=Some (tt,(after,observations)) /\
    machine after=AxiomRefl.finished built /\ nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  intros Hmeta Htrace. unfold AxiomFixedCircuits.extensionality_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H;clear H;subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H;clear H;subst end.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold AxiomStructure.handler_9.
  execute Hmeta. eexists;split;[reflexivity|]. split;[reflexivity|].
  repeat rewrite RenameMemoControl.updated_other by discriminate. reflexivity.
Qed.
End AxiomFixedRaw.
