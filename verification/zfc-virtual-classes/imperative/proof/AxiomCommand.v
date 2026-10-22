From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives CommandQuit CommandStructure
  CommandDispatch CommandChain HistoryStorage AppendTheorem ReplyNO RenameMemoControl.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module AxiomCommand.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments tag a b c : varsfuncdef_0__axiom -> Z :=
  update (update (update (update (fun _=>0) vardef_0__axiom_tag tag)
    vardef_0__axiom_p a) vardef_0__axiom_q b) vardef_0__axiom_r c.
Definition read_result (reader : CommandQuitExecution.reader_function) s t value observations :=
  execObserved (reader (fun _=>false) (fun _=>0)) (s,observations)=Some (tt,(t,observations)) /\
  (17<length (memory t arraydef_0__meta))%nat /\
  meta_value t 11=value /\ meta_value t 14=1 /\ meta_value t 8=0.
Definition locals (f : Frame) tag a b c :=
  setNum (setNum (setNum (setNum f vardef_0__command_tag tag) vardef_0__command_a a)
    vardef_0__command_b b) vardef_0__command_c c.
Definition result built n index accepted := if accepted then HistoryStorage.result built n (Z.of_nat index)
  else ReplyNOExecution.reply_state built.
Definition reply n accepted := if accepted then Protocol.OK n else Protocol.NO.
Local Opaque funcdef_0__axiom funcdef_0__appendTheorem funcdef_0__no Imperative.update.
Theorem generated_handler reader (f : Frame) first second third fourth built tag a b c n index accepted observations :
  (17<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8=0 ->
  read_result reader (machine f) first tag observations -> read_result reader first second a observations ->
  read_result reader second third b observations -> read_result reader third fourth c observations ->
  execObserved (funcdef_0__axiom (fun _=>false) (arguments tag a b c)) (fourth,observations)=Some (tt,(built,observations)) ->
  (17<length (memory built arraydef_0__meta))%nat -> meta_value built 13=(if accepted then 1 else 0) ->
  meta_value built 8=0 -> meta_value built 0=Z.of_nat index ->
  meta_value built 3=Z.of_nat n -> Z.of_nat n<maximum ->
  (20<=length (memory built arraydef_0__printBuffer))%nat ->
  execLocalObserved (CommandStructure.handler_11 reader) (f,observations)=
    Some (tt,(setMachine (locals f tag a b c) (result built n index accepted),
      observations++[{|flushedOutput:=stdout built++Protocol.reply_bytes (reply n accepted);unreadInput:=stdin built|}])).
Proof.
  intros Hinitial Herror [Hread1 [Hmeta1 [Hvalue1 [Hvalid1 Herror1]]]]
    [Hread2 [Hmeta2 [Hvalue2 [Hvalid2 Herror2]]]]
    [Hread3 [Hmeta3 [Hvalue3 [Hvalid3 Herror3]]]]
    [Hread4 [Hmeta4 [Hvalue4 [Hvalid4 Herror4]]]] Haxiom Hbuilt Hsuccess Hbuilt_error Hindex Hcount Hword Hbuffer.
  destruct accepted; destruct f as [s bs ns]; cbn [machine] in *; unfold CommandStructure.handler_11.
  all: repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hbuilt]
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
         |assert (Hrun:expression=Some (tt,(built,observations))) by exact Haxiom]; rewrite Hrun;clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__appendTheorem ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__appendTheorem bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(HistoryStorage.result current n (Z.of_nat index),
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes (Protocol.OK n);unreadInput:=stdin current|}]))) by
         (apply AppendTheoremExecution.generated_append; try assumption;try lia;reflexivity);rewrite Hrun;clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
       let Hrun:=fresh in assert (Hrun:expression=Some (tt,(ReplyNOExecution.reply_state current,
         trace++[{|flushedOutput:=stdout current++Protocol.reply_bytes Protocol.NO;unreadInput:=stdin current|}]))) by
         apply ReplyNOExecution.generated_no;rewrite Hrun;clear Hrun end
    |progress rewrite Herror |progress rewrite Herror1 |progress rewrite Herror2 |progress rewrite Herror3 |progress rewrite Herror4
    |progress rewrite Hvalid1 |progress rewrite Hvalid2 |progress rewrite Hvalid3 |progress rewrite Hvalid4
    |progress rewrite Hvalue1 |progress rewrite Hvalue2 |progress rewrite Hvalue3 |progress rewrite Hvalue4
    |progress rewrite Hsuccess |progress rewrite Hindex
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
  all: unfold locals,result,reply;reflexivity.
Qed.
End AxiomCommand.
