From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives ArenaFrame Intern InternLengths
  FormulaEncoding FormulaTopology Representation FormulaCircuit FormulaCircuitProperties AxiomCircuits AxiomRefl RenameMemoLengths RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomInstRaw.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom.
Definition cleared s := store_meta s 13 0.
Definition finished s := store_meta (store_meta s 0 (meta_value s 0)) 13 1.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Definition rename_arguments root arg : varsfuncdef_0__rename -> Z :=
  update (update (update (update (fun _=>0) vardef_0__rename_node root)
    vardef_0__rename_mode 1) vardef_0__rename_shift 0) vardef_0__rename_arg arg.
Theorem generated_body (f : Frame) quantified renamed built p_id arg observations :
  (13 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__axiom_tag=3 -> nums f vardef_0__axiom_p=p_id -> nums f vardef_0__axiom_q=arg ->
  p_id<meta_value (machine f) 1 ->
  execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 4 p_id 0))
    (cleared (machine f),observations)=Some (tt,(quantified,observations)) ->
  execObserved (funcdef_0__rename (fun _=>false) (rename_arguments p_id arg))
    (quantified,observations)=Some (tt,(renamed,observations)) ->
  execObserved (funcdef_0__intern (fun _=>false) (FormulaCircuit.arguments 3 (meta_value quantified 0) (meta_value renamed 0)))
    (renamed,observations)=Some (tt,(built,observations)) ->
  optionBind (execLocalObserved funcdef_0__axiom_body (f,observations))
    (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r)))) = Some (tt,(finished built,observations)).
Proof.
  intros Hmeta Htag Hp Harg Hpbound Hall Hrename Hlast.
  pose proof (proj1 (InternLengths.observed_lengths _ _ _ _ _ _ Hall)) as Hqlength.
  pose proof (proj1 (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename)) as Hrlength.
  pose proof (proj1 (InternLengths.observed_lengths _ _ _ _ _ _ Hlast)) as Hblength.
  assert (Hqmeta:(13<length (memory quantified arraydef_0__meta))%nat)
    by (rewrite Hqlength;unfold cleared;rewrite store_meta_length;exact Hmeta).
  assert (Hrmeta:(13<length (memory renamed arraydef_0__meta))%nat) by (rewrite Hrlength;exact Hqmeta).
  assert (Hbmeta:(13<length (memory built arraydef_0__meta))%nat) by (rewrite Hblength;exact Hrmeta).
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__axiom_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot=>first [exact Hmeta|exact Hqmeta|exact Hrmeta|exact Hbmeta|assumption|rewrite !store_meta_length;first [exact Hmeta|exact Hbmeta]|cbn [machine setMachine setNum];rewrite ?store_meta_length;lia])
    |match goal with H : execObserved (funcdef_0__intern _ _) _ = Some (tt,(?after,?trace)) |-
         context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(after,trace))) by exact H; rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__rename ?bi ?ni) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__rename bi ni) state) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(renamed,observations))) by exact Hrename; rewrite Hrun; clear Hrun end
    |progress rewrite Htag |progress rewrite Hp |progress rewrite Harg
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
End AxiomInstRaw.
