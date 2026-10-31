From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedTagLaterHandlers.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Theorem handler_11_2 reader (f:Frame) p1 v1 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_11 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_11.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread2];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
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
Theorem handler_11_3 reader (f:Frame) p1 v1 p2 v2 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_11 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) p2)vardef_0__command_a v2) arg)vardef_0__command_b number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hread3 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hp2meta Hp2number Hp2valid Hp2error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_11.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp2meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(p2,observations))) by exact Hread2|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread3];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
  |progress rewrite Hp2number |progress rewrite Hp2valid |progress rewrite Hp2error
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
Theorem handler_11_4 reader (f:Frame) p1 v1 p2 v2 p3 v3 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(p3,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p3,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 (17<length(memory p3 arraydef_0__meta))%nat -> meta_value p3 11=v3 -> meta_value p3 14=1 -> meta_value p3 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_11 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) p2)vardef_0__command_a v2) p3)vardef_0__command_b v3) arg)vardef_0__command_c number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hread3 Hread4 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hp2meta Hp2number Hp2valid Hp2error Hp3meta Hp3number Hp3valid Hp3error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_11.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp2meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp3meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(p2,observations))) by exact Hread2|assert(Hrun:expression=Some(tt,(p3,observations))) by exact Hread3|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread4];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
  |progress rewrite Hp2number |progress rewrite Hp2valid |progress rewrite Hp2error
  |progress rewrite Hp3number |progress rewrite Hp3valid |progress rewrite Hp3error
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
Theorem handler_22_2 reader (f:Frame) p1 v1 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_22 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_22.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread2];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
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
Theorem handler_22_3 reader (f:Frame) p1 v1 p2 v2 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_22 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) p2)vardef_0__command_a v2) arg)vardef_0__command_b number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hread3 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hp2meta Hp2number Hp2valid Hp2error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_22.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp2meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(p2,observations))) by exact Hread2|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread3];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
  |progress rewrite Hp2number |progress rewrite Hp2valid |progress rewrite Hp2error
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
Theorem handler_22_4 reader (f:Frame) p1 v1 p2 v2 p3 v3 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(p3,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p3,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 (17<length(memory p3 arraydef_0__meta))%nat -> meta_value p3 11=v3 -> meta_value p3 14=1 -> meta_value p3 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_22 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) p2)vardef_0__command_a v2) p3)vardef_0__command_b v3) arg)vardef_0__command_c number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hread3 Hread4 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hp2meta Hp2number Hp2valid Hp2error Hp3meta Hp3number Hp3valid Hp3error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_22.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp2meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp3meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(p2,observations))) by exact Hread2|assert(Hrun:expression=Some(tt,(p3,observations))) by exact Hread3|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread4];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
  |progress rewrite Hp2number |progress rewrite Hp2valid |progress rewrite Hp2error
  |progress rewrite Hp3number |progress rewrite Hp3valid |progress rewrite Hp3error
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
Theorem handler_22_5 reader (f:Frame) p1 v1 p2 v2 p3 v3 p4 v4 arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(p1,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p1,observations)=Some(tt,(p2,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p2,observations)=Some(tt,(p3,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p3,observations)=Some(tt,(p4,observations)) ->
 execObserved(reader (fun _=>false)(fun _=>0))(p4,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory p1 arraydef_0__meta))%nat -> meta_value p1 11=v1 -> meta_value p1 14=1 -> meta_value p1 8=0 ->
 (17<length(memory p2 arraydef_0__meta))%nat -> meta_value p2 11=v2 -> meta_value p2 14=1 -> meta_value p2 8=0 ->
 (17<length(memory p3 arraydef_0__meta))%nat -> meta_value p3 11=v3 -> meta_value p3 14=1 -> meta_value p3 8=0 ->
 (17<length(memory p4 arraydef_0__meta))%nat -> meta_value p4 11=v4 -> meta_value p4 14=1 -> meta_value p4 8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_22 reader)(f,observations)=Some(tt,(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(setNum(setMachine(f) p1)vardef_0__command_tag v1) p2)vardef_0__command_a v2) p3)vardef_0__command_b v3) p4)vardef_0__command_c v4) arg)vardef_0__command_node number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread1 Hread2 Hread3 Hread4 Hread5 Hinitial Hinitialerror Hp1meta Hp1number Hp1valid Hp1error Hp2meta Hp2number Hp2valid Hp2error Hp3meta Hp3number Hp3valid Hp3error Hp4meta Hp4number Hp4valid Hp4error Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_22.
 repeat first [progress cbn [optionBind fst snd]
  |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       first [eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hargmeta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp1meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp2meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp3meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hp4meta]
             |eapply Nat.le_lt_trans with (m:=17%nat);[cbn;lia|exact Hinitial]])
  |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
    let expression:=constr:(@execObserved I T EI R (reader br nr) state) in
    let Hrun:=fresh "Hrun" in first [assert(Hrun:expression=Some(tt,(p1,observations))) by exact Hread1|assert(Hrun:expression=Some(tt,(p2,observations))) by exact Hread2|assert(Hrun:expression=Some(tt,(p3,observations))) by exact Hread3|assert(Hrun:expression=Some(tt,(p4,observations))) by exact Hread4|assert(Hrun:expression=Some(tt,(arg,observations))) by exact Hread5];rewrite Hrun;clear Hrun end
  |progress rewrite Hp1number |progress rewrite Hp1valid |progress rewrite Hp1error
  |progress rewrite Hp2number |progress rewrite Hp2valid |progress rewrite Hp2error
  |progress rewrite Hp3number |progress rewrite Hp3valid |progress rewrite Hp3error
  |progress rewrite Hp4number |progress rewrite Hp4valid |progress rewrite Hp4error
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
End NativeMalformedTagLaterHandlers.
