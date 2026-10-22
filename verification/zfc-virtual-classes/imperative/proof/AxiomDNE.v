From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Intern InternLengths
  FormulaEncoding FormulaTopology Representation FormulaCircuit FormulaCircuitProperties AxiomCircuits AxiomRefl RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomDNE.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom.
Definition cleared s := store_meta s 13 0.
Definition finished s := store_meta (store_meta s 0 (meta_value s 0)) 13 1.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Theorem generated_body (f : Frame) built ids p_id observations :
  (13 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__axiom_tag=2 -> nums f vardef_0__axiom_p=p_id ->
  p_id<meta_value (machine f) 1 ->
  FormulaCircuit.executes observations AxiomCircuits.dne_plan (cleared (machine f)) [0;p_id] built ids ->
  optionBind (execLocalObserved funcdef_0__axiom_body (f,observations))
    (fun r=>Some (tt,(machine (fst (snd r)),snd (snd r)))) = Some (tt,(finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hpbound Htrace.
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Htrace)) as Hfinalmeta.
  assert (Hbuiltmeta:(13<length (memory built arraydef_0__meta))%nat)
    by (rewrite Hfinalmeta;unfold cleared;rewrite store_meta_length;exact Hmeta).
  unfold AxiomCircuits.dne_plan in Htrace.
  repeat match goal with H : FormulaCircuit.executes _ (_::_) _ _ _ _ |- _ => inversion H; clear H; subst end.
  match goal with H : FormulaCircuit.executes _ [] _ _ _ _ |- _ => inversion H; clear H; subst end.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__axiom_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot=>first [exact Hmeta|exact Hbuiltmeta|assumption|rewrite !store_meta_length;first [exact Hmeta|exact Hbuiltmeta]|cbn [machine setMachine setNum];rewrite ?store_meta_length;lia])
    |match goal with H : execObserved (funcdef_0__intern _ _) _ = Some (tt,(?after,?trace)) |-
         context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(after,trace))) by exact H; rewrite Hrun; clear Hrun end
    |progress rewrite Htag |progress rewrite Hp
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress rewrite meta_store_other by lia
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by first [exact Hpbound|lia] |progress rewrite (bool_decide_false P) by lia] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
End AxiomDNE.
