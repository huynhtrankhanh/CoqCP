From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  AxiomRefl AxiomCircuits FormulaCircuit FormulaCircuitProperties InternLengths ArenaFrame
  FormulaTopology HashTable Representation Intern.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomS.
Import IndexExecution SipHashExecution ObservedLocal.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Theorem generated_helper s bs ns built ids p q r observations :
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=1 -> ns vardef_0__axiom_p=p -> ns vardef_0__axiom_q=q -> ns vardef_0__axiom_r=r ->
  p<meta_value s 1 -> q<meta_value s 1 -> r<meta_value s 1 ->
  FormulaCircuit.executes observations AxiomCircuits.s_plan (AxiomRefl.cleared s) [p;q;r] built ids ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hq Hr Hpbound Hqbound Hrbound Htrace.
  pose proof (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace) as [Hbuiltmeta Hsip].
  unfold AxiomRefl.cleared in Hbuiltmeta. rewrite store_meta_length in Hbuiltmeta.
  unfold AxiomCircuits.s_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  unfold funcdef_0__axiom. rewrite eliminate_correct. unfold funcdef_0__axiom_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine setNum];
       repeat first [rewrite store_meta_length
         |match goal with Hrun : execObserved (funcdef_0__intern ?bi ?ni) (?before,?trace)=Some (tt,(?after,?after_trace))
           |- context [length (memory ?after arraydef_0__meta)] =>
            rewrite (proj1 (InternLengths.observed_lengths before bi ni trace after after_trace Hrun)) end
         |progress unfold AxiomRefl.cleared]; lia)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       multimatch goal with Hrun : ?candidate=Some ?answer |- _ =>
         let Hsame:=fresh in assert (Hsame : expression=Some answer) by exact Hrun;
         rewrite Hsame; clear Hsame end end
    |progress rewrite Hp |progress rewrite Hq |progress rewrite Hr |progress rewrite Htag
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress rewrite meta_store_other by lia
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 1) with 1%nat by reflexivity
    |progress replace (Z.to_nat 13) with 13%nat by reflexivity
    |match goal with |- context [meta_value ?before 0] =>
       multimatch goal with Hvalue : meta_value before 0 = ?value |- _ => progress rewrite Hvalue end end
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; first [exact Hpbound|exact Hqbound|exact Hrbound|lia])
       |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
End AxiomS.
