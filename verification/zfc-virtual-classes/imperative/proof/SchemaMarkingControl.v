From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash SchemaGraph SchemaMarking ObservedLocal NativePrimitives RenameMemoControl.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaMarkingControl.
Import IndexExecution SipHashExecution ObservedLocal.
Theorem generated_marked_pass (f:SchemaMarking.Frame) root observations :
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  execLocalObserved SchemaMarking.marked_pass (f,observations)=
  execLocalObserved (loop (SchemaGraph.width root) (SchemaMarking.mark_outer_body (Z.of_nat (SchemaGraph.width root)))) (f,observations).
Proof.
  intro Hwidth. unfold SchemaMarking.marked_pass.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
    |progress rewrite Hwidth|progress rewrite Nat2Z.id]. reflexivity.
Qed.
Theorem generated_row (f:SchemaMarking.Frame) root remaining observations :
  nums f vardef_0__schemaInstance_root=Z.of_nat root ->
  nums f vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root) ->
  (remaining<SchemaGraph.width root)%nat -> Z.of_nat (SchemaGraph.width root)<=maximum ->
  execLocalObserved (SchemaMarking.mark_outer_body (Z.of_nat (SchemaGraph.width root)) remaining) (f,observations)=
  optionBind (execLocalObserved
    (loop (SchemaGraph.width root) (SchemaMarking.mark_depth_body (Z.of_nat (SchemaGraph.width root))))
    (setNum f vardef_0__schemaInstance_node (Z.of_nat remaining),observations))
    (fun r=>Some (KeepGoing,snd r)).
Proof.
  intros Hroot Hwidth Hremaining Hroom.
  assert (Hroot':(let (_,_,ns):=f in ns) vardef_0__schemaInstance_root=Z.of_nat root) by exact Hroot.
  assert (Hwidth':(let (_,_,ns):=f in ns) vardef_0__schemaInstance_width=Z.of_nat (SchemaGraph.width root)) by exact Hwidth.
  assert (Hsub:coerceInt (Z.of_nat root-(Z.of_nat (SchemaGraph.width root)-Z.of_nat remaining-1)) 64=Z.of_nat remaining).
  { replace (Z.of_nat root-(Z.of_nat (SchemaGraph.width root)-Z.of_nat remaining-1)) with (Z.of_nat remaining) by (unfold SchemaGraph.width;lia).
    apply coerce_word. unfold word. apply Nat2Z.inj_lt in Hremaining. lia. }
  unfold SchemaMarking.mark_outer_body.
  repeat first [progress cbn [optionBind fst snd]
    |progress rewrite drop_assoc|progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>lia)
    |progress unfold subInt at 1
    |progress rewrite Hroot|progress rewrite Hwidth|progress rewrite Hroot'|progress rewrite Hwidth'
    |progress rewrite Hsub|progress rewrite Nat2Z.id
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress cbn [nums setNum machine]
  ]. reflexivity.
Qed.
End SchemaMarkingControl.
