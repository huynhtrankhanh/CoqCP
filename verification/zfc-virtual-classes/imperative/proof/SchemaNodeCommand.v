From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives CommandQuit CommandStructure
  CommandDispatch CommandChain AxiomCommand RenameMemoControl.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaNodeCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments kind a b c d : varsfuncdef_0__schemaNode -> Z :=
  update (update (update (update (update (fun _=>0) vardef_0__schemaNode_kind kind)
    vardef_0__schemaNode_a a) vardef_0__schemaNode_b b) vardef_0__schemaNode_c c) vardef_0__schemaNode_d d.
Definition locals (f:Frame) kind a b c d :=
  setNum (setNum (setNum (setNum (setNum f vardef_0__command_tag kind)
    vardef_0__command_a a) vardef_0__command_b b) vardef_0__command_c c) vardef_0__command_node d.
Local Opaque funcdef_0__schemaNode Imperative.update.
Theorem generated_handler reader (f:Frame) first second third fourth fifth built kind a b c d observations trace :
  (17<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  AxiomCommand.read_result reader (machine f) first kind observations ->
  AxiomCommand.read_result reader first second a observations ->
  AxiomCommand.read_result reader second third b observations ->
  AxiomCommand.read_result reader third fourth c observations ->
  AxiomCommand.read_result reader fourth fifth d observations ->
  execObserved (funcdef_0__schemaNode (fun _=>false) (arguments kind a b c d))
    (fifth,observations)=Some (tt,(built,trace)) ->
  execLocalObserved (CommandStructure.handler_22 reader) (f,observations)=
    Some (tt,(setMachine (locals f kind a b c d) built,trace)).
Proof.
  intros Hinitial Herror [Hread1 [Hmeta1 [Hvalue1 [Hvalid1 Herror1]]]]
    [Hread2 [Hmeta2 [Hvalue2 [Hvalid2 Herror2]]]]
    [Hread3 [Hmeta3 [Hvalue3 [Hvalid3 Herror3]]]]
    [Hread4 [Hmeta4 [Hvalue4 [Hvalid4 Herror4]]]]
    [Hread5 [Hmeta5 [Hvalue5 [Hvalid5 Herror5]]]] Hhelper.
  destruct f as [s bs ns];cbn [machine] in *;unfold CommandStructure.handler_22.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta5]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta4]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta3]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta2]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hmeta1]
         |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (?callee ?bo ?no) ?state] =>
       let expression:=constr:(@execObserved I T EI R (callee bo no) state) in
       let Hrun:=fresh in first
         [assert (Hrun:expression=Some (tt,(first,observations))) by exact Hread1
         |assert (Hrun:expression=Some (tt,(second,observations))) by exact Hread2
         |assert (Hrun:expression=Some (tt,(third,observations))) by exact Hread3
         |assert (Hrun:expression=Some (tt,(fourth,observations))) by exact Hread4
         |assert (Hrun:expression=Some (tt,(fifth,observations))) by exact Hread5
         |assert (Hrun:expression=Some (tt,(built,trace))) by exact Hhelper]; rewrite Hrun;clear Hrun end
    |progress rewrite Herror |progress rewrite Herror1 |progress rewrite Herror2 |progress rewrite Herror3 |progress rewrite Herror4 |progress rewrite Herror5
    |progress rewrite Hvalid1 |progress rewrite Hvalid2 |progress rewrite Hvalid3 |progress rewrite Hvalid4 |progress rewrite Hvalid5
    |progress rewrite Hvalue1 |progress rewrite Hvalue2 |progress rewrite Hvalue3 |progress rewrite Hvalue4 |progress rewrite Hvalue5
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 13) with 13%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite RenameMemoControl.updated_same
    |progress rewrite RenameMemoControl.updated_other by discriminate
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by congruence] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P:=P)) by congruence |progress rewrite (decide_False (P:=P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ].
  unfold locals;reflexivity.
Qed.
Theorem generated_command s bs ns opstate first second third fourth fifth built kind a b c d observations trace :
  AxiomCommand.read_result funcdef_0__readNat s opstate 22 observations ->
  AxiomCommand.read_result funcdef_0__readNat opstate first kind observations ->
  AxiomCommand.read_result funcdef_0__readNat first second a observations ->
  AxiomCommand.read_result funcdef_0__readNat second third b observations ->
  AxiomCommand.read_result funcdef_0__readNat third fourth c observations ->
  AxiomCommand.read_result funcdef_0__readNat fourth fifth d observations ->
  execObserved (funcdef_0__schemaNode (fun _=>false) (arguments kind a b c d))
    (fifth,observations)=Some (tt,(built,trace)) ->
  (8<length (memory built arraydef_0__meta))%nat -> meta_value built 8=0 ->
  execObserved (funcdef_0__command bs ns) (s,observations)=Some (tt,(built,trace)).
Proof.
  intros [Hopcode [Hopmeta [Hopnumber [Hopvalid Hoperror]]]] Hfirst Hsecond Hthird Hfourth Hfifth Hhelper Hbuilt Herror.
  set (initial:=CommandDispatch.opcode_frame {|machine:=s;bools:=bs;nums:=ns|} opstate 22).
  set (after:=setMachine (locals initial kind a b c d) built).
  apply (CommandDispatch.generated_positive_command s bs ns after opstate 22 observations trace);try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandChain.handler_for funcdef_0__readNat 22) (initial,observations)=Some (tt,(after,trace))).
    eapply generated_handler;eassumption.
Qed.
End SchemaNodeCommand.
