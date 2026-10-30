From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandSteps.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedArgumentHandler.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Theorem handler_4 reader (f:Frame) arg number observations :
 execObserved(reader (fun _=>false)(fun _=>0))(machine f,observations)=Some(tt,(arg,observations)) ->
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)8=0 ->
 (17<length(memory arg arraydef_0__meta))%nat -> meta_value arg 11=number -> meta_value arg 14=0 ->
 execLocalObserved(CommandStructure.handler_4 reader)(f,observations)=Some(tt,
 (setMachine(setNum(setMachine f arg)vardef_0__command_a number)(store_meta arg 8 1),observations)).
Proof.
 intros Hread Hinitial Hinitialerror Hargmeta Hnumber Hvalid.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold CommandStructure.handler_4.
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
End NativeMalformedArgumentHandler.
