From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  AxiomRefl AxiomDispatch AxiomStructure FormulaCircuit FormulaCircuitProperties InternLengths
  RenameMemoLengths AxiomSeparationCircuits NativeAxiomBuilder NativeAxiomPrefix.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomSeparationRaw.
Import IndexExecution SipHashExecution ObservedLocal NativeAxiomBuilder.
Local Opaque funcdef_0__intern funcdef_0__rename Imperative.update.
Definition rename_arguments root : varsfuncdef_0__rename -> Z :=
  update (update (update (update (fun _=>0) vardef_0__rename_node root)
    vardef_0__rename_mode 2) vardef_0__rename_shift 0) vardef_0__rename_arg 0.
Ltac drop_statements count code := lazymatch count with
| O=>code
| S ?n=>lazymatch code with bind ?head ?next => let rest:=eval cbn beta in (next tt) in drop_statements n rest end
end.
Definition rename_call : AxiomStructure.LocalAction unit := ltac:(
  let code:=eval unfold AxiomStructure.handler_15 in AxiomStructure.handler_15 in
  let rest:=drop_statements 4%nat code in lazymatch rest with bind ?head _=>exact head end).
Definition continuation := rename_call >>= fun _=>save 2 >>= fun _=>program AxiomSeparationCircuits.after 3.
Lemma actual : AxiomStructure.handler_15=NativeAxiomPrefix.prefix AxiomSeparationCircuits.before 0 continuation.
Proof. reflexivity. Qed.
Lemma before_valid : valid AxiomSeparationCircuits.before 0.
Proof. cbn [AxiomSeparationCircuits.before valid valid_op];repeat split;lia. Qed.
Lemma after_valid : valid AxiomSeparationCircuits.after 3.
Proof. cbn [AxiomSeparationCircuits.after valid valid_op];repeat split;lia. Qed.
Lemma p_not_slot i : vardef_0__axiom_p<>slot i.
Proof. unfold slot,slots. do 42 (destruct i as [|i];[discriminate|]);destruct i;discriminate. Qed.
Lemma rename_run (f:AxiomRefl.Frame) p renamed observations :
  nums f vardef_0__axiom_p=p ->
  execObserved (funcdef_0__rename (fun _=>false) (rename_arguments p)) (machine f,observations)=Some (tt,(renamed,observations)) ->
  execLocalObserved rename_call (f,observations)=Some (tt,(setMachine f renamed,observations)).
Proof.
  intros Hp Hrename. unfold rename_call.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
    |progress rewrite Hp
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__rename ?bi ?ni) ?state] =>
      let expression:=constr:(@execObserved I T EI R (funcdef_0__rename bi ni) state) in
      let Hsame:=fresh in assert (Hsame:expression=Some (tt,(renamed,observations))) by exact Hrename;
      rewrite Hsame;clear Hsame end]. reflexivity.
Qed.
Theorem generated_helper s bs ns prepared before_ids renamed built ids p observations :
  (13<length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__axiom_tag=15 -> ns vardef_0__axiom_p=p -> p<meta_value s 1 ->
  FormulaCircuit.executes observations AxiomSeparationCircuits.before (AxiomRefl.cleared s) [0] prepared before_ids ->
  execObserved (funcdef_0__rename (fun _=>false) (rename_arguments p))
    (prepared,observations)=Some (tt,(renamed,observations)) ->
  FormulaCircuit.executes observations AxiomSeparationCircuits.after renamed (before_ids++[meta_value renamed 0]) built ids ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(AxiomRefl.finished built,observations)).
Proof.
  intros Hmeta Htag Hp Hpbound Hbefore Hrename Htrace.
  pose (f:=AxiomDispatch.cleared_frame {|machine:=s;bools:=bs;nums:=ns|}).
  assert (Hclear:(13<length (memory (AxiomRefl.cleared s) arraydef_0__meta))%nat)
    by (unfold AxiomRefl.cleared;rewrite store_meta_length;exact Hmeta).
  assert (Henv:environment f 0 [0]).
  { split;[reflexivity|]. split;[reflexivity|]. intros;lia. }
  destruct (NativeAxiomPrefix.run _ _ _ _ _ _ Hbefore f 0 eq_refl Henv before_valid Hclear)
    as (pf & Hprepared & Hpenv & Hptag & Hplocals & Hprefix).
  change (environment pf 2 before_ids) in Hpenv.
  assert (Hpp:nums pf vardef_0__axiom_p=p).
  { rewrite Hplocals;[exact Hp|intros;apply p_not_slot]. }
  assert (Hrename_local:execLocalObserved rename_call (pf,observations)=Some (tt,(setMachine pf renamed,observations))).
  { apply (rename_run pf p renamed observations Hpp). now rewrite Hprepared. }
  pose proof (proj1 (FormulaCircuitProperties.lengths _ _ _ _ _ _ Hbefore)) as Hpremeta.
  pose proof (proj1 (RenameMemoLengths.observed_lengths _ _ _ _ _ _ Hrename)) as Hrenmeta.
  assert (Hrmeta:(13<length (memory renamed arraydef_0__meta))%nat) by lia.
  assert (Hrenenv:environment (advanced pf renamed 2 (meta_value renamed 0)) 3 (before_ids++[meta_value renamed 0])).
  { apply advance_environment;[exact Hpenv|lia]. }
  assert (Hlast:List.nth 3 (before_ids++[meta_value renamed 0]) 0=meta_value renamed 0).
  { destruct Hpenv as [Hlen _]. rewrite List.app_nth2 by lia. replace (3-length before_ids)%nat with 0%nat by lia. reflexivity. }
  assert (Hpositive:(3>0)%nat) by lia.
  destruct (NativeAxiomBuilder.run _ _ _ _ _ _ Htrace (advanced pf renamed 2 (meta_value renamed 0)) 3
    eq_refl Hrenenv after_valid Hrmeta (or_introl Hpositive) (or_intror Hlast))
    as (after & Hafter & Hbuilt & Haftertag).
  apply (AxiomDispatch.generated_projected s bs ns 15 (AxiomRefl.finished built) observations observations).
  - lia.
  - exact Htag.
  - unfold AxiomDispatch.references_valid,AxiomDispatch.reference_names. constructor;[cbn [nums machine];now rewrite Hp|constructor].
  - exact Hmeta.
  - change (optionBind (execLocalObserved AxiomStructure.handler_15 (f,observations))
      (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))=Some (tt,(AxiomRefl.finished built,observations))).
    rewrite actual,Hprefix. unfold continuation. rewrite local_bind,Hrename_local. cbn [optionBind fst snd].
    rewrite local_bind.
    match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (save 2) ?state] =>
      let expression:=constr:(@execLocalObserved I T EI V EV R (save 2) state) in
      let Hsave:=fresh in assert (Hsave:expression=Some (tt,(advanced pf renamed 2 (meta_value renamed 0),observations)))
        by exact (save_run (setMachine pf renamed) 2 observations ltac:(cbn [machine setMachine];lia));rewrite Hsave;clear Hsave end.
    cbn [optionBind fst snd machine setMachine]. change (optionBind
      (execLocalObserved (program AxiomSeparationCircuits.after 3) (advanced pf renamed 2 (meta_value renamed 0),observations))
      (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))=Some (tt,(AxiomRefl.finished built,observations))).
    pose proof (f_equal (fun response=>optionBind response
      (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))) Hafter) as Hprojected.
    cbn [optionBind fst snd] in Hprojected. rewrite Hbuilt in Hprojected. exact Hprojected.
Qed.
End AxiomSeparationRaw.
