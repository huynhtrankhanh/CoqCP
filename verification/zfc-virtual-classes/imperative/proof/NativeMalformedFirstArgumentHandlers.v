From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps CommandChain NativeMalformedArgumentHandler.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedFirstArgumentHandlers.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Theorem handler_1 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_1 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_1.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_2 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_2 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_2.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_3 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_3 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_3.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_5 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_5 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_5.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_6 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_6 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_6.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_7 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_7 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_7.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_8 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_8 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_8.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_9 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_9 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_9.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_12 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_12 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_12.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_13 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_13 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_13.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_18 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_18 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_18.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_19 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_19 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_19.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_20 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_20 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_20.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Theorem handler_23 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_23 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_23.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread;rewrite Hrun;clear Hrun end
  |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Hinitialerror
  |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |progress replace (Z.to_nat 11) with 11%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [progress rewrite (bool_decide_true P) by (try congruence;lia)|progress rewrite (bool_decide_false P) by (try congruence;lia)] end
  |match goal with |- context [decide ?P] => first [progress rewrite (decide_True (P:=P)) by congruence|progress rewrite (decide_False (P:=P)) by congruence] end
  |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
 ]. reflexivity.
Qed.
Definition supported opcode : Prop := List.In opcode [1;2;3;4;5;6;7;8;9;12;13;18;19;20;23].
Theorem handler reader opcode (f:Frame) arg number observations :
 supported opcode ->
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandChain.handler_for reader opcode)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hopcode Hread Hinitial Herror Harg Hnumber Hvalid.
 unfold supported in Hopcode. cbn [List.In] in Hopcode.
 repeat destruct Hopcode as [Hopcode|Hopcode];try contradiction;subst opcode;
 cbn [CommandChain.handler_for]; first [eapply handler_1 | eapply handler_2 | eapply handler_3 | eapply NativeMalformedArgumentHandler.handler_4 | eapply handler_5 | eapply handler_6 | eapply handler_7 | eapply handler_8 | eapply handler_9 | eapply handler_12 | eapply handler_13 | eapply handler_18 | eapply handler_19 | eapply handler_20 | eapply handler_23]; eassumption.
Qed.
End NativeMalformedFirstArgumentHandlers.
