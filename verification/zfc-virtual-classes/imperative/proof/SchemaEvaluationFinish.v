From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol Schemata.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
 SchemaEvaluation SchemaEvaluationInvariant SchemaEvaluationControl SchemaMarking SchemaGraph.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationFinish.
Import IndexExecution SipHashExecution ObservedLocal.
Definition pass : SchemaEvaluation.LocalAction unit := ltac:(
 let code:=eval unfold SchemaMarking.evaluation in SchemaMarking.evaluation in
 lazymatch code with bind ?first _=>exact first end).
Definition finish : SchemaEvaluation.LocalAction unit := ltac:(
 let code:=eval unfold SchemaMarking.evaluation in SchemaMarking.evaluation in
 lazymatch code with bind _ ?next=>exact (next tt) end).
Lemma evaluation_parts : SchemaMarking.evaluation=(pass >>= fun _=>finish).
Proof. reflexivity. Qed.
Lemma evaluation_execution f observations :
 execLocalObserved SchemaMarking.evaluation (f,observations)=
 optionBind (execLocalObserved pass (f,observations))
   (fun response=>execLocalObserved finish (snd response)).
Proof. rewrite evaluation_parts,local_bind. reflexivity. Qed.
Lemma generated_pass (f:SchemaEvaluation.Frame) stride observations :
 nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 execLocalObserved pass (f,observations)=
 execLocalObserved (loop stride (SchemaEvaluation.outer_body (Z.of_nat stride))) (f,observations).
Proof.
 intro Hwidth. unfold pass.
 repeat first [progress cbn [optionBind fst snd]
  |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
  |progress rewrite Hwidth|progress rewrite Nat2Z.id]. reflexivity.
Qed.
Lemma generated_rejected (f:SchemaEvaluation.Frame) observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 (meta_value (machine f) 8<>0 \/ meta_value (machine f) 18=0) ->
 execLocalObserved finish (f,observations)=Some (tt,(f,observations)).
Proof.
 intros Hmeta Hrejected. unfold finish.
 repeat first [progress cbn [optionBind fst snd negb bind]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity].
 destruct Hrejected as [Herror|Hzero].
 - rewrite bool_decide_false by exact Herror. reflexivity.
 - destruct (bool_decide (meta_value (machine f) 8=0));[|reflexivity].
   repeat first [progress cbn [optionBind fst snd negb bind]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity].
   rewrite Hzero. reflexivity.
Qed.
Lemma generated_accepted (f:SchemaEvaluation.Frame) root stride key id observations :
 (18<length (memory (machine f) arraydef_0__meta))%nat ->
 meta_value (machine f) 8=0 -> meta_value (machine f) 18<>0 ->
 nums f vardef_0__schemaInstance_root=Z.of_nat root ->
 nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
 key=(root*stride)%nat -> Z.of_nat key<=maximum ->
 nth_error (memory (machine f) arraydef_0__schemaValues) key=Some id ->
 execLocalObserved finish (f,observations)=Some (tt,(setMachine f (store_meta (machine f) 0 id),observations)).
Proof.
 intros Hmeta Herror Hvalid Hroot Hwidth Hkey Hword Hlookup.
 assert (Hbound:(key<length (memory (machine f) arraydef_0__schemaValues))%nat) by (apply nth_error_Some;congruence).
 pose proof (List.nth_error_nth _ _ 0 Hlookup) as Hnth.
 assert (Hmul:coerceInt (Z.of_nat root*Z.of_nat stride) 64=Z.of_nat key).
 { rewrite <-Nat2Z.inj_mul,<-Hkey. apply coerce_word. unfold word;lia. }
 unfold finish.
 repeat first [progress cbn [optionBind fst snd negb bind]
  |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];rewrite ?Nat2Z.id;first [exact Hbound|lia])
  |progress rewrite Hroot|progress rewrite Hwidth|progress unfold multInt at 1|progress rewrite Hmul|progress rewrite Nat2Z.id
  |progress rewrite Herror
  |multimatch goal with |- context [bool_decide ?P]=>first
    [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
  |progress rewrite (bool_decide_false (meta_value (machine f) 18=0)) by exact Hvalid
  |progress replace (Z.to_nat 18) with 18%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [List.nth ?i ?xs ?zero]=>let expression:=constr:(List.nth i xs zero) in
   let Hsame:=fresh in assert (Hsame:expression=id) by exact Hnth;rewrite Hsame;clear Hsame end].
 reflexivity.
Qed.
Theorem generated_sound source root expressions rho fs classes (f:SchemaEvaluation.Frame) cert observations :
 SchemaGraph.ordered source -> (root<length (memory source arraydef_0__schemaNodes))%nat ->
 SchemaEvaluationInvariant.completed source root expressions rho fs classes (machine f) (SchemaGraph.width root*SchemaGraph.width root) ->
 nth_error expressions root=Some (Protocol.PE cert) ->
 (18<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 -> meta_value (machine f) 18<>0 ->
 nums f vardef_0__schemaInstance_root=Z.of_nat root -> nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
 Z.of_nat (SchemaGraph.width root*SchemaGraph.width root)<=maximum ->
 (SchemaGraph.width root*SchemaGraph.width root<=length (memory (machine f) arraydef_0__schemaValues))%nat ->
 exists final p,execLocalObserved finish (f,observations)=Some (tt,(final,observations)) /\
 Schemata.infer rho 0 cert=Some p /\ SetTheory.derives p /\
 SchemaEvaluation.formula_value fs (meta_value (machine final) 0) p.
Proof.
 intros Hordered Hroot Hcompleted Hlookup Hmeta Herror Hvalid Hrootnum Hwidth Hword Hallocated.
 destruct (SchemaEvaluationInvariant.completed_proof source root expressions rho fs classes (machine f) cert Hordered Hroot Hcompleted Hlookup)
  as [p [Hinfer [Hmeaning Hderive]]].
 set (key:=SchemaGraph.key root root 0).
 assert (Hgrid:(key<SchemaGraph.width root*SchemaGraph.width root)%nat).
 { apply (proj2 (proj2 (SchemaGraph.reachable_grid source root root 0 Hordered Hroot (SchemaGraph.root_reachable source root)))). }
 set (id:=SchemaEvaluation.value (machine f) key).
 exists (setMachine f (store_meta (machine f) 0 id)),p. split.
 - apply (generated_accepted f root (SchemaGraph.width root) key id observations Hmeta Herror Hvalid Hrootnum Hwidth).
   + unfold key,SchemaGraph.key. lia.
   + apply Nat2Z.inj_lt in Hgrid. lia.
   + unfold id,SchemaEvaluation.value. apply List.nth_error_nth'. lia.
 - split;[exact Hinfer|]. split;[exact Hderive|]. cbn [machine setMachine].
   rewrite meta_store_same by lia. exact Hmeaning.
Qed.
End SchemaEvaluationFinish.
