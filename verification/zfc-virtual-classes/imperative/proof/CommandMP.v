From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandDispatch NativePrimitives ReplyNO.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandMPExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Definition arguments i j := update (update (fun _ => 0) vardef_0__modusPonens_implication i) vardef_0__modusPonens_antecedent j.
Definition after (f : Frame) firststate secondstate final i j :=
  setMachine (setNum (setMachine (setNum (setMachine f firststate) vardef_0__command_a i) secondstate) vardef_0__command_b j) final.
Local Opaque funcdef_0__modusPonens funcdef_0__no.
Theorem generated_handler reader (f : Frame) firststate secondstate final i j observations after_observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(firststate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory firststate arraydef_0__meta))%nat ->
  meta_value firststate 11 = i -> meta_value firststate 14 = 1 -> meta_value firststate 8 = 0 ->
  execObserved (reader (fun _ => false) (fun _ => 0)) (firststate,observations) = Some (tt,(secondstate,observations)) ->
  (17 < length (memory secondstate arraydef_0__meta))%nat ->
  meta_value secondstate 11 = j -> meta_value secondstate 14 = 1 -> meta_value secondstate 8 = 0 ->
  i < meta_value secondstate 3 -> j < meta_value secondstate 3 ->
  execObserved (funcdef_0__modusPonens (fun _ => false) (arguments i j)) (secondstate,observations) = Some (tt,(final,after_observations)) ->
  execLocalObserved (CommandStructure.handler_12 reader) (f,observations) =
    Some (tt,(after f firststate secondstate final i j,after_observations)).
Proof.
  intros Hfirst Hinitial Hinitialerror Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror Hsecond Hmeta Hnumber Hvalid Herror Hi Hj Hmp.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_12.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hfirstmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?br ?nr) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader br nr) state) in
        let Hread := fresh "Hread" in first
        [assert (Hread : expression = Some (tt,(firststate,observations))) by exact Hfirst
        |assert (Hread : expression = Some (tt,(secondstate,observations))) by exact Hsecond];
        rewrite Hread; clear Hread end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__modusPonens ?bi ?ni) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__modusPonens bi ni) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(final,after_observations))) by exact Hmp;
        rewrite Hrun; clear Hrun end
    |progress rewrite Hfirstnumber |progress rewrite Hfirstvalid |progress rewrite Hfirsterror
    |progress rewrite Hnumber |progress rewrite Hvalid |progress rewrite Herror |progress rewrite Hinitialerror
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold after. reflexivity.
Qed.
Theorem generated_command s bs ns opcode_state firststate secondstate final i j observations after_observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(opcode_state,observations)) ->
  (17 < length (memory opcode_state arraydef_0__meta))%nat ->
  meta_value opcode_state 11 = 12 -> meta_value opcode_state 14 = 1 -> meta_value opcode_state 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opcode_state,observations) = Some (tt,(firststate,observations)) ->
  (17 < length (memory firststate arraydef_0__meta))%nat ->
  meta_value firststate 11 = i -> meta_value firststate 14 = 1 -> meta_value firststate 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (firststate,observations) = Some (tt,(secondstate,observations)) ->
  (17 < length (memory secondstate arraydef_0__meta))%nat ->
  meta_value secondstate 11 = j -> meta_value secondstate 14 = 1 -> meta_value secondstate 8 = 0 ->
  i < meta_value secondstate 3 -> j < meta_value secondstate 3 ->
  execObserved (funcdef_0__modusPonens (fun _ => false) (arguments i j)) (secondstate,observations) = Some (tt,(final,after_observations)) ->
  (8 < length (memory final arraydef_0__meta))%nat -> meta_value final 8 = 0 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(final,after_observations)).
Proof.
  intros Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hfirst Hfirstmeta Hfirstnumber Hfirstvalid Hfirsterror
    Hsecond Hmeta Hnumber Hvalid Herror Hi Hj Hmp Hpostmeta Hposterror.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opcode_state 12).
  set (finalframe := after initial firststate secondstate final i j).
  apply (CommandDispatch.generated_positive_command s bs ns finalframe opcode_state 12 observations after_observations); try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_12 funcdef_0__readNat) (initial,observations) = Some (tt,(finalframe,after_observations))).
    apply (generated_handler funcdef_0__readNat initial firststate secondstate final i j observations after_observations); assumption.
Qed.
End CommandMPExecution.
