From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandChain CommandDispatch NativeMalformedCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeFatalDispatch.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Local Opaque funcdef_0__intern funcdef_0__ok funcdef_0__no funcdef_0__readToken funcdef_0__readNat.
Theorem fatal_composition reader sequence (f after : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command)
  readstate opcode observations trace :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = opcode -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  1 <= opcode <= 26 ->
  execLocalObserved sequence (CommandDispatch.opcode_frame f readstate opcode,observations) = Some (tt,(after,trace)) ->
  (17 < length (memory (machine after) arraydef_0__meta))%nat -> meta_value (machine after) 8 = 1 ->
  execLocalObserved (CommandDispatch.with_chain reader sequence) (f,observations) = Some (tt,(setMachine after (store_meta(withOutput (machine after) (stdout(machine after)++Protocol.reply_bytes Protocol.ERR))9 1),
   trace++[{|flushedOutput:=stdout(machine after)++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin(machine after)|}])).
Proof.
  intros Hreader Hmeta Hnumber Hvalid Herror Hrange Hsequence Haftermeta Haftererror.
  destruct f as [s bs ns]. destruct after as [final bs_final ns_final]. cbn [machine] in *.
  unfold CommandDispatch.opcode_frame in Hsequence. unfold CommandDispatch.with_chain. cbv beta iota zeta.
  repeat first [progress cbn [optionBind fst snd]
    |progress (match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
      lazymatch state with (?frame,?trace_now) =>
      let expression := constr:(@execLocalObserved I T EI V EV R code state) in
      let head := CommandDispatch.action_head code in
      first [constr_eq head (@Done) |constr_eq head (@bind) |constr_eq head (@numberLocalGet)
        |constr_eq head (@numberLocalSet) |constr_eq head (@retrieve) |constr_eq head (@store)
        |constr_eq head (@liftToWithLocalVariables) |constr_eq head (@shortCircuitAnd) |constr_eq head (@shortCircuitOr)];
      lazymatch head with
      | @Done => lazymatch code with @Done ?E ?F ?A ?value => change expression with (Some (value,state)) end
      | @bind => lazymatch code with bind ?first ?next =>
          let Hbind := fresh "Hbind" in
          assert (Hbind : expression = optionBind (execLocalObserved first state)
            (fun response => execLocalObserved (R := R) (next (fst response)) (snd response))) by
            (exact (local_bind first next state)); rewrite Hbind; clear Hbind end
      | @numberLocalGet => lazymatch code with numberLocalGet _ _ _ ?name =>
          change expression with (Some (nums frame name,state)) end
      | @numberLocalSet => lazymatch code with numberLocalSet _ _ _ ?name ?value =>
          change expression with (Some (tt,(setNum frame name value,trace_now))) end
      | @retrieve => lazymatch code with retrieve _ _ _ arraydef_0__meta ?slot =>
          let Hstep := fresh "Hstep" in
          assert (Hstep : expression = Some (meta_value (machine frame) (Z.to_nat slot),state)) by
            (exact (local_read_meta frame slot trace_now ltac:(cbn [machine setMachine]; first
              [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
              |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Haftermeta]])));
          rewrite Hstep; clear Hstep end
      | @liftToWithLocalVariables => lazymatch code with liftToWithLocalVariables ?callee =>
          let Hlift := fresh "Hlift" in
          assert (Hlift : expression = optionBind (execObserved callee (machine frame,trace_now))
            (fun response => Some (fst response,(setMachine frame (fst (snd response)),snd (snd response))))) by
            (exact (lift_correct callee frame trace_now)); rewrite Hlift; clear Hlift end
      | @shortCircuitAnd => unfold shortCircuitAnd at 1
      | @shortCircuitOr => unfold shortCircuitOr at 1
      end
      end
    end)
    |match goal with |- context [execObserved (reader _ _) _] => progress rewrite Hreader end
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R sequence ?state] =>
        let expression := constr:(@execLocalObserved I T EI V EV R sequence state) in
        let Hseq := fresh "Hseq" in
        assert (Hseq : expression = Some (tt,({|machine := final; bools := bs_final; nums := ns_final|},trace))) by
          (exact Hsequence); rewrite Hseq; clear Hseq
      end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |match goal with |- context [meta_value final 8] => progress rewrite Haftererror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  
    |match goal with |- context [execLocalObserved (dropWithinLoop (bind (bind ?code ?next) ?last)) ?state] => rewrite (drop_assoc code next last state) end
    |match goal with |- context [execLocalObserved (dropWithinLoop (bind (liftToWithinLoop ?code) ?next)) ?state] => rewrite (drop_lift code next state) end
    |rewrite dropWithinLoop_1
    |progress cbn [loopString]
    |rewrite local_write |rewrite local_flush
    |rewrite local_store_meta by (cbn [machine setMachine];repeat first [rewrite store_meta_length | rewrite output_length];lia)
    |rewrite output_meta |rewrite meta_store_other by lia
    |rewrite meta_store_same by (repeat first [rewrite store_meta_length | rewrite output_length];lia)
    |progress replace (Z.to_nat 9) with 9%nat by reflexivity
    |progress replace (Z.to_nat 7) with 7%nat by reflexivity
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
  ]. unfold Protocol.reply_bytes.
  cbn [withOutput store_meta withMemory memory stdout stdin setMachine setNum machine nums bools Imperative.update].
  repeat rewrite <-List.app_assoc. reflexivity.
Qed.
Theorem generated_fatal_body reader (f after : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command)
  readstate (opcode : Z) observations trace :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = opcode -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  1 <= opcode <= 26 -> nums after vardef_0__command_op = opcode ->
  execLocalObserved (CommandChain.handler_for reader opcode) (CommandDispatch.opcode_frame f readstate opcode,observations) = Some (tt,(after,trace)) ->
  (17 < length (memory (machine after) arraydef_0__meta))%nat -> meta_value (machine after) 8 = 1 ->
  execLocalObserved (body_with reader) (f,observations) = Some (tt,(setMachine after (store_meta(withOutput (machine after) (stdout(machine after)++Protocol.reply_bytes Protocol.ERR))9 1),trace++[{|flushedOutput:=stdout(machine after)++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin(machine after)|}])).
Proof.
  intros Hread Hmeta Hnumber Hvalid Herror Hrange Hafterop Hhandler Haftermeta Haftererror.
  rewrite CommandDispatch.actual_body. eapply fatal_composition; try eassumption.
  eapply CommandChain.generated_source_chain; try eassumption.
  - reflexivity.
  - change (8 < length (memory readstate arraydef_0__meta))%nat.
    eapply Nat.le_lt_trans with (m := 17%nat); [lia|exact Hmeta].
Qed.
Theorem generated_fatal_command s bs ns after readstate (opcode : Z) observations trace :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = opcode -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  1 <= opcode <= 26 -> nums after vardef_0__command_op = opcode ->
  execLocalObserved (CommandChain.handler_for funcdef_0__readNat opcode)
    (CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} readstate opcode,observations) = Some (tt,(after,trace)) ->
  (17 < length (memory (machine after) arraydef_0__meta))%nat -> meta_value (machine after) 8 = 1 ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(store_meta(withOutput (machine after) (stdout(machine after)++Protocol.reply_bytes Protocol.ERR))9 1,trace++[{|flushedOutput:=stdout(machine after)++Protocol.reply_bytes Protocol.ERR;unreadInput:=stdin(machine after)|}])).
Proof.
  intros Hread Hmeta Hnumber Hvalid Herror Hrange Hafterop Hhandler Haftermeta Haftererror.
  unfold IndexExecution.Machine in *. unfold funcdef_0__command.
  rewrite ObservedLocal.eliminate_correct, CommandQuitExecution.actual_body.
  pose proof (generated_fatal_body funcdef_0__readNat {|machine := s; bools := bs; nums := ns|}
    after readstate opcode observations trace Hread Hmeta Hnumber Hvalid Herror Hrange Hafterop Hhandler Haftermeta Haftererror) as Hbody.
  rewrite Hbody. reflexivity.
Qed.
End NativeFatalDispatch.
