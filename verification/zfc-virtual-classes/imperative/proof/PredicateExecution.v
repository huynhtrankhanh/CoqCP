From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash NativePrimitives ObservedLocal.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module PredicateExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__predicate.
Definition intern_arguments arg value shift : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _ => 0) vardef_0__intern_tag 2) vardef_0__intern_a arg) vardef_0__intern_b (coerceInt (value + shift) 64).
Definition rename_arguments value shift arg : varsfuncdef_0__rename -> Z :=
  update (update (update (update (fun _ => 0) vardef_0__rename_node value) vardef_0__rename_mode 6) vardef_0__rename_shift shift) vardef_0__rename_arg arg.
Local Opaque funcdef_0__intern funcdef_0__rename.
Theorem generated_set_body (f : Frame) final cls value shift arg observations :
  nums f vardef_0__predicate_cls = cls -> nums f vardef_0__predicate_shift = shift -> nums f vardef_0__predicate_arg = arg ->
  (Z.to_nat cls < length (memory (machine f) arraydef_0__classes))%nat ->
  List.nth (Z.to_nat cls) (memory (machine f) arraydef_0__classes) (0,0) = (0,value) ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  word value -> word shift -> value + shift <= maximum ->
  execObserved (funcdef_0__intern (fun _ => false) (intern_arguments arg value shift)) (machine f,observations) = Some (tt,(final,observations)) ->
  execLocalObserved funcdef_0__predicate_body (f,observations) =
    Some (tt,(setMachine (setNum f vardef_0__predicate_value value) final,observations)).
Proof.
  intros Hcls Hshift Harg Hbound Hclass Hmeta Herror Hvalue Hshiftword Hsum Hintern.
  assert (Hoverflow : maximum - value < shift -> False) by lia.
  assert (Hsub : coerceInt (maximum - value) 64 = maximum - value)
    by (apply coerce_word; unfold word in *; lia).
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__predicate_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; lazymatch name with
       |arraydef_0__meta => exact Hmeta |arraydef_0__classes => exact Hbound end)
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in assert (Hsame : expression = (0,value)) by exact Hclass; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(final,observations))) by exact Hintern; rewrite Hrun; clear Hrun end
    |progress rewrite Hcls |progress rewrite Hshift |progress rewrite Harg |progress rewrite Herror
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace 18446744073709551615 with maximum by reflexivity
    |progress rewrite Hsub
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update subInt addInt]
  ]. reflexivity.
Qed.
Theorem generated_abstract_body (f : Frame) final cls value shift arg observations :
  nums f vardef_0__predicate_cls = cls -> nums f vardef_0__predicate_shift = shift -> nums f vardef_0__predicate_arg = arg ->
  (Z.to_nat cls < length (memory (machine f) arraydef_0__classes))%nat ->
  List.nth (Z.to_nat cls) (memory (machine f) arraydef_0__classes) (0,0) = (1,value) ->
  execObserved (funcdef_0__rename (fun _ => false) (rename_arguments value shift arg)) (machine f,observations) = Some (tt,(final,observations)) ->
  execLocalObserved funcdef_0__predicate_body (f,observations) = Some (tt,(setMachine f final,observations)).
Proof.
  intros Hcls Hshift Harg Hbound Hclass Hrename.
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold funcdef_0__predicate_body.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hbound)
    |match goal with |- context [List.nth ?i (memory ?source arraydef_0__classes) ?zero] =>
       let expression := constr:(List.nth i (memory source arraydef_0__classes) zero) in
       let Hsame := fresh in assert (Hsame : expression = (1,value)) by exact Hclass; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__rename ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__rename bi ni) state) in
       let Hrun := fresh in assert (Hrun : expression = Some (tt,(final,observations))) by exact Hrename; rewrite Hrun; clear Hrun end
    |progress rewrite Hcls |progress rewrite Hshift |progress rewrite Harg
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Theorem generated_set s bs ns final cls value shift arg observations :
  ns vardef_0__predicate_cls = cls -> ns vardef_0__predicate_shift = shift -> ns vardef_0__predicate_arg = arg ->
  (Z.to_nat cls < length (memory s arraydef_0__classes))%nat ->
  List.nth (Z.to_nat cls) (memory s arraydef_0__classes) (0,0) = (0,value) ->
  (8 < length (memory s arraydef_0__meta))%nat -> meta_value s 8 = 0 ->
  word value -> word shift -> value + shift <= maximum ->
  execObserved (funcdef_0__intern (fun _ => false) (intern_arguments arg value shift)) (s,observations) = Some (tt,(final,observations)) ->
  execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)).
Proof.
  intros Hcls Hshift Harg Hbound Hclass Hmeta Herror Hvalue Hshiftword Hsum Hintern.
  pose proof (generated_set_body {|machine:=s;bools:=bs;nums:=ns|} final cls value shift arg observations
    Hcls Hshift Harg Hbound Hclass Hmeta Herror Hvalue Hshiftword Hsum Hintern) as Hbody.
  pose proof (eliminate_correct funcdef_0__predicate_body bs ns s observations) as Heliminate.
  unfold Frame in Hbody. rewrite Hbody in Heliminate. exact Heliminate.
Qed.
Theorem generated_abstract s bs ns final cls value shift arg observations :
  ns vardef_0__predicate_cls = cls -> ns vardef_0__predicate_shift = shift -> ns vardef_0__predicate_arg = arg ->
  (Z.to_nat cls < length (memory s arraydef_0__classes))%nat ->
  List.nth (Z.to_nat cls) (memory s arraydef_0__classes) (0,0) = (1,value) ->
  execObserved (funcdef_0__rename (fun _ => false) (rename_arguments value shift arg)) (s,observations) = Some (tt,(final,observations)) ->
  execObserved (funcdef_0__predicate bs ns) (s,observations) = Some (tt,(final,observations)).
Proof.
  intros Hcls Hshift Harg Hbound Hclass Hrename.
  pose proof (generated_abstract_body {|machine:=s;bools:=bs;nums:=ns|} final cls value shift arg observations
    Hcls Hshift Harg Hbound Hclass Hrename) as Hbody.
  pose proof (eliminate_correct funcdef_0__predicate_body bs ns s observations) as Heliminate.
  unfold Frame in Hbody. rewrite Hbody in Heliminate. exact Heliminate.
Qed.
End PredicateExecution.
