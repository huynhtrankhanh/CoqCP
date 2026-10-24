From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl
  SchemaEvaluation SchemaMarking SchemaEvaluationControl SchemaGraph.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module SchemaEvaluationLoop.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := SchemaEvaluation.Frame.
Definition LocalAction := SchemaEvaluation.LocalAction.
Definition LoopAction := SchemaEvaluation.LoopAction.

Lemma drop_return (code:LoopAction unit) f observations :
  execLocalObserved (dropWithinLoop (code>>=fun _=>Done _ _ _ tt)) (f,observations)=
  execLocalObserved (dropWithinLoop code) (f,observations).
Proof.
  induction code as [value|effect cont IH] in f,observations|-*.
  - destruct value. reflexivity.
  - destruct effect as [effect| |];try reflexivity.
    cbn [bind dropWithinLoop Action_rect execLocalObserved].
    destruct (localStepObserved effect (f,observations)) as [[value [middle trace]]|];cbn [optionBind fst snd];
      [apply IH|reflexivity].
Qed.

Definition inner_with width remaining outer_remaining (work:LoopAction unit) : LocalAction LoopOutcome := ltac:(
  let code:=eval cbv beta iota zeta delta [SchemaEvaluation.inner_body] in
    (SchemaEvaluation.inner_body width remaining outer_remaining) in
  let selected:=eval cbv beta iota zeta delta [SchemaEvaluation.marked_body] in
    (SchemaEvaluation.marked_body width remaining outer_remaining) in
  let family:=eval pattern selected in code in lazymatch family with ?family _=>exact (family work) end).
Lemma actual_inner width remaining outer_remaining :
  SchemaEvaluation.inner_body width remaining outer_remaining=
    inner_with width remaining outer_remaining (SchemaEvaluation.marked_body width remaining outer_remaining).
Proof. reflexivity. Qed.

Lemma generated_stopped (f:Frame) width remaining outer_remaining work observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  (meta_value (machine f) 18=0 \/ meta_value (machine f) 8<>0) ->
  execLocalObserved (inner_with width remaining outer_remaining work) (f,observations)=Some (Stop,(f,observations)).
Proof.
  intros Hmeta Hstop. unfold inner_with.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity].
  destruct Hstop as [Hzero|Herror].
  - rewrite Hzero. reflexivity.
  - destruct (bool_decide (meta_value (machine f) 18=0));[reflexivity|].
    repeat first [progress cbn [optionBind fst snd negb]
      |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
      |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine];lia)].
    rewrite bool_decide_true by exact Herror. reflexivity.
Qed.

Lemma generated_cell (f:Frame) width remaining outer_remaining stride node d key work observations :
  (19<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 18<>0 -> meta_value (machine f) 8=0 ->
  nums f vardef_0__schemaInstance_width=Z.of_nat stride ->
  SchemaEvaluation.depth width outer_remaining=Z.of_nat node -> SchemaEvaluation.depth width remaining=Z.of_nat d ->
  key=(node*stride+d)%nat -> Z.of_nat key<=maximum ->
  (key<length (memory (machine f) arraydef_0__schemaMarks))%nat ->
  execLocalObserved (inner_with width remaining outer_remaining work) (f,observations)=
    if bool_decide (SchemaMarking.cell (machine f) key<>0) then
      execLocalObserved (dropWithinLoop work) (setNum f vardef_0__schemaInstance_key (Z.of_nat key),observations)
    else Some (KeepGoing,(setNum f vardef_0__schemaInstance_key (Z.of_nat key),observations)).
Proof.
  intros Hmeta Hvalid Herror Hwidth Hnode Hd Hkey Hword Hbound.
  assert (Hmul:coerceInt (Z.of_nat node*Z.of_nat stride) 64=Z.of_nat (node*stride)).
  { rewrite <-Nat2Z.inj_mul. apply coerce_word. unfold word. lia. }
  assert (Hsum:coerceInt (Z.of_nat (node*stride)+Z.of_nat d) 64=Z.of_nat key).
  { rewrite <-Nat2Z.inj_add,<-Hkey. apply coerce_word. unfold word. lia. }
  unfold SchemaEvaluation.depth in Hnode,Hd. unfold inner_with.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite drop_assoc|progress rewrite drop_lift|progress rewrite drop_lift_final
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setNum];rewrite ?Nat2Z.id;first [exact Hbound|lia])
    |progress unfold addInt at 1|progress unfold multInt at 1
    |progress rewrite Herror|progress rewrite Hwidth|progress rewrite Hnode|progress rewrite Hd
    |progress rewrite Hmul|progress rewrite Hsum|progress rewrite Nat2Z.id
    |progress rewrite (bool_decide_false (meta_value (machine f) 18=0)) by exact Hvalid
    |progress rewrite (bool_decide_false (0<>0)) by congruence
    |multimatch goal with |- context [bool_decide ?P] => first
      [progress rewrite (bool_decide_true P) by congruence|progress rewrite (bool_decide_false P) by congruence] end
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |progress replace (coerceInt 0 8) with 0 by reflexivity
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress change (List.nth key (memory (machine f) arraydef_0__schemaMarks) 0) with (SchemaMarking.cell (machine f) key)
    ].
  destruct (bool_decide (SchemaMarking.cell (machine f) key<>0));[apply drop_return|reflexivity].
Qed.
End SchemaEvaluationLoop.
