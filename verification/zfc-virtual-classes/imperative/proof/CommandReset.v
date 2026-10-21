From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit ReplyOK CommandStructure.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandResetExecution.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Lemma opcode_guard_skip_reset opcode right body (f : Frame) observations :
  nums f vardef_0__command_op = 17 -> opcode <> 17 ->
  execLocalObserved (opcode_guard opcode right body) (f,observations) = Some (tt,(f,observations)).
Proof.
  intros Hvalue Hopcode. unfold opcode_guard, shortCircuitAnd.
  cbn [bind numberLocalGet execLocalObserved localStepObserved optionBind fst snd].
  rewrite Hvalue, bool_decide_false by lia. reflexivity.
Qed.
Ltac skip_reset_opcode :=
  match goal with |- context [execLocalObserved (bind (shortCircuitAnd ?lhs_code ?rhs_code) ?branch_code) (?current_frame,?trace_so_far)] =>
    lazymatch lhs_code with bind (numberLocalGet _ _ _ vardef_0__command_op) ?test_next =>
      let comparison_code := eval cbn beta in (test_next 0%Z) in
      lazymatch comparison_code with bind (Done _ _ _ ?opcode_value) _ =>
        let body_code := eval cbn beta iota in (branch_code true) in
        let Hskip := fresh "Hskip" in
        pose proof (opcode_guard_skip_reset opcode_value rhs_code body_code current_frame trace_so_far ltac:(reflexivity) ltac:(lia)) as Hskip;
        unfold CommandQuitExecution.Frame in Hskip;
        rewrite Hskip; clear Hskip
      end
    end
  end.
Ltac action_head term := lazymatch term with ?head ?arg => action_head head | _ => term end.
Definition reset_state s := ReplyOKExecution.reply_state (store_meta s 3 0) 0.
Definition reset_frame (f : Frame) s := setMachine (setNum (setMachine f s) vardef_0__command_op 17) (reset_state s).
Lemma reset_meta s i : meta_value (reset_state s) i = meta_value (store_meta s 3 0) i.
Proof. reflexivity. Qed.
Lemma reset_meta_length s : length (memory (reset_state s) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. change (length (memory (store_meta s 3 0) arraydef_0__meta) = length (memory s arraydef_0__meta)). apply store_meta_length. Qed.
Local Opaque funcdef_0__intern funcdef_0__ok funcdef_0__no funcdef_0__readToken funcdef_0__readNat
  funcdef_0__lookup funcdef_0__bindName funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize
  funcdef_0__rename funcdef_0__predicate funcdef_0__classEqual funcdef_0__classMember funcdef_0__setness
  funcdef_0__axiom funcdef_0__schemaCheck funcdef_0__schemaNode funcdef_0__schemaInstance.
Local Opaque CommandStructure.handler_1 CommandStructure.handler_2 CommandStructure.handler_3 CommandStructure.handler_4 CommandStructure.handler_5 CommandStructure.handler_6 CommandStructure.handler_7 CommandStructure.handler_8 CommandStructure.handler_9 CommandStructure.handler_10 CommandStructure.handler_11 CommandStructure.handler_12 CommandStructure.handler_13 CommandStructure.handler_14 CommandStructure.handler_15 CommandStructure.handler_16 CommandStructure.handler_18 CommandStructure.handler_19 CommandStructure.handler_20 CommandStructure.handler_21 CommandStructure.handler_22 CommandStructure.handler_23 CommandStructure.handler_24 CommandStructure.handler_25 CommandStructure.handler_26.
Theorem generated_reset_body reader (f : Frame) readstate observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  (20 <= length (memory readstate arraydef_0__printBuffer))%nat ->
  meta_value readstate 11 = 17 -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  execLocalObserved (body_with reader) (f,observations) = Some (tt,(reset_frame f readstate,
    observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hmeta Hbuffer Hnumber Hvalid Herror. destruct f as [s bs ns]. cbn [machine] in Hreader.
  rewrite CommandStructure.actual_body. unfold CommandStructure.compact_body. cbv beta iota zeta.
  repeat first [progress fold (reset_state readstate)
    |progress cbn [optionBind fst snd]
    |progress skip_reset_opcode
    |match goal with |- context [execLocalObserved (CommandStructure.handler_17 _) _] => unfold CommandStructure.handler_17 at 1 end
    |progress (match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
      lazymatch state with (?frame,?trace) =>
      let expression := constr:(@execLocalObserved I T EI V EV R code state) in
      let head := action_head code in
      first [constr_eq head (@Done) |constr_eq head (@bind) |constr_eq head (@numberLocalGet)
        |constr_eq head (@numberLocalSet) |constr_eq head (@retrieve) |constr_eq head (@store)
        |constr_eq head (@liftToWithLocalVariables) |constr_eq head (@shortCircuitAnd) |constr_eq head (@shortCircuitOr)];
      lazymatch head with
      | @Done => lazymatch code with @Done ?E ?F ?R ?value => change (execLocalObserved (@Done E F R value) (frame,trace)) with (Some (value,(frame,trace))) end
      | @bind => lazymatch code with bind ?first ?next =>
          let Hbind := fresh "Hbind" in
          assert (Hbind : expression = optionBind (execLocalObserved first state)
            (fun response => execLocalObserved (R := R) (next (fst response)) (snd response))) by
            (exact (local_bind first next state));
          rewrite Hbind; clear Hbind end
      | @numberLocalGet => lazymatch code with numberLocalGet _ _ _ ?name => change (execLocalObserved code (frame,trace)) with (Some (nums frame name,(frame,trace))) end
      | @numberLocalSet => lazymatch code with numberLocalSet _ _ _ ?name ?value => change (execLocalObserved code (frame,trace)) with (Some (tt,(setNum frame name value,trace))) end
      | @retrieve => lazymatch code with retrieve _ _ _ arraydef_0__meta ?slot =>
          let Hstep := fresh "Hstep" in
          assert (Hstep : expression = Some (meta_value (machine frame) (Z.to_nat slot),state)) by
            (exact (local_read_meta frame slot trace ltac:(cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite reset_meta_length]; eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta])));
          rewrite Hstep; clear Hstep end
      | @store => lazymatch code with store _ _ _ arraydef_0__meta ?slot ?value =>
          let Hstep := fresh "Hstep" in
          assert (Hstep : expression = Some (tt,(setMachine frame (store_meta (machine frame) (Z.to_nat slot) value),trace))) by
            (exact (local_store_meta frame slot value trace ltac:(cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite reset_meta_length]; eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta])));
          rewrite Hstep; clear Hstep end
      | @liftToWithLocalVariables => lazymatch code with liftToWithLocalVariables ?callee =>
          let Hlift := fresh "Hlift" in
          assert (Hlift : expression = optionBind (execObserved callee (machine frame,trace))
            (fun response => Some (fst response,(setMachine frame (fst (snd response)),snd (snd response))))) by
            (exact (lift_correct callee frame trace));
          rewrite Hlift; clear Hlift end
      | @shortCircuitAnd => lazymatch code with shortCircuitAnd _ _ => unfold shortCircuitAnd at 1 end
      | @shortCircuitOr => lazymatch code with shortCircuitOr _ _ => unfold shortCircuitOr at 1 end
      end
      end
    end)
    |match goal with |- context [execObserved (reader _ _) _] => progress rewrite Hreader end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bs_ok ?ns_ok) ?state] =>
        lazymatch state with (?current,?trace) =>
          let execution := constr:(@execObserved I T EI R (funcdef_0__ok bs_ok ns_ok) state) in
          let Hok := fresh "Hok" in
          assert (Hok : execution = Some (tt,(ReplyOKExecution.reply_state current 0,
            trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK 0); unreadInput := stdin current|}]))) by
            (apply (ReplyOKExecution.generated_ok current bs_ok ns_ok 0 trace);
              [reflexivity|unfold maximum; lia|cbn [machine setMachine]; rewrite store_meta_other by discriminate; exact Hbuffer]);
          rewrite Hok; clear Hok
        end
      end
    |match goal with |- context [meta_value (reset_state ?state) ?slot] => progress rewrite (reset_meta state slot) end
    |match goal with |- context [meta_value (withOutput ?state ?out) ?slot] => progress rewrite (output_meta state out slot) end
    |match goal with |- context [meta_value (store_meta ?state ?slot ?value) ?index] => progress rewrite (meta_store_other state index slot value) by lia end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |progress replace (Z.to_nat 9) with 9%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ].
  unfold reset_frame. reflexivity.
Qed.
End CommandResetExecution.
