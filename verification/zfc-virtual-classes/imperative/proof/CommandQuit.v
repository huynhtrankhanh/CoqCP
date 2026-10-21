From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module CommandQuitExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) withLocalVariablesReturnValue R.
Definition reader_function := (varsfuncdef_0__readNat -> bool) -> (varsfuncdef_0__readNat -> Z) ->
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition body_with (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__command_body in funcdef_0__command_body in
  let generalized := eval pattern funcdef_0__readNat in code in
  lazymatch generalized with ?family _ => exact (family reader) end).
Lemma actual_body : funcdef_0__command_body = body_with funcdef_0__readNat.
Proof. reflexivity. Qed.
Lemma local_done {R} (value : R) (f : Frame) observations :
  execLocalObserved (Done _ _ _ value) (f,observations) = Some (value,(f,observations)).
Proof. reflexivity. Qed.
Lemma local_get (f : Frame) name observations :
  execLocalObserved (R := Z) (numberLocalGet _ _ _ name) (f,observations) = Some (nums f name,(f,observations)).
Proof. reflexivity. Qed.
Lemma local_set (f : Frame) name value observations :
  execLocalObserved (R := unit) (numberLocalSet _ _ _ name value) (f,observations) = Some (tt,(setNum f name value,observations)).
Proof. reflexivity. Qed.
Lemma local_read_meta (f : Frame) slot observations :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (R := arrayType _ environment1 arraydef_0__meta) (retrieve _ _ _ arraydef_0__meta slot) (f,observations) =
    Some (meta_value (machine f) (Z.to_nat slot),(f,observations)).
Proof.
  intro Hmeta. cbn [retrieve execLocalObserved localStepObserved fst snd].
  unfold observedStep. cbn [step optionBind fst snd]. case_decide; [|lia].
  rewrite nth_lt_default with (default := 0%Z). destruct f. reflexivity.
Qed.
Lemma local_store_meta (f : Frame) slot value observations :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (R := unit) (store _ _ _ arraydef_0__meta slot value) (f,observations) =
    Some (tt,(setMachine f (store_meta (machine f) (Z.to_nat slot) value),observations)).
Proof.
  intro Hmeta. cbn [store execLocalObserved localStepObserved fst snd].
  unfold observedStep. cbn [step optionBind fst snd]. case_decide; [|lia]. destruct f. reflexivity.
Qed.
Lemma local_write (f : Frame) ch observations :
  execLocalObserved (R := unit) (writeChar _ _ _ ch) (f,observations) =
    Some (tt,(setMachine f (withOutput (machine f) (stdout (machine f) ++ [ch])),observations)).
Proof. destruct f. reflexivity. Qed.
Lemma local_flush (f : Frame) observations :
  execLocalObserved (R := unit) (flush _ _ _) (f,observations) = Some (tt,(f,
    observations ++ [{|flushedOutput := stdout (machine f); unreadInput := stdin (machine f)|}])).
Proof. destruct f. reflexivity. Qed.
Definition bye_bytes : list Z := [66;89;69;10].
Definition quit_state (s : Machine) := withOutput (store_meta s 9 1) (stdout s ++ bye_bytes).
Definition quit_frame (f : Frame) s := setMachine (setNum (setMachine f s) vardef_0__command_op 0) (quit_state s).

Definition opcode_guard (opcode : Z) (right : LocalAction bool) (body : LocalAction unit) :=
  shortCircuitAnd
    (numberLocalGet _ _ _ vardef_0__command_op >>= fun value => Done _ _ _ opcode >>= fun n => Done _ _ _ (bool_decide (value = n)))
    right >>= fun enabled => if enabled then body else Done _ _ _ tt.
Lemma opcode_guard_skip opcode right body (f : Frame) observations :
  nums f vardef_0__command_op = 0 -> opcode <> 0 ->
  execLocalObserved (opcode_guard opcode right body) (f,observations) = Some (tt,(f,observations)).
Proof.
  intros Hvalue Hopcode. unfold opcode_guard, shortCircuitAnd.
  cbn [bind numberLocalGet execLocalObserved localStepObserved optionBind fst snd].
  rewrite Hvalue, bool_decide_false by lia. reflexivity.
Qed.
Lemma output_meta s output i : meta_value (withOutput s output) i = meta_value s i.
Proof. reflexivity. Qed.
Lemma output_length (s : Machine) output : length (memory (withOutput s output) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. reflexivity. Qed.

Ltac skip_opcode :=
  match goal with |- context [execLocalObserved (bind (shortCircuitAnd ?lhs_code ?rhs_code) ?branch_code) (?current_frame,?trace_so_far)] =>
    lazymatch lhs_code with bind (numberLocalGet _ _ _ vardef_0__command_op) ?test_next =>
      let comparison_code := eval cbn beta in (test_next 0%Z) in
      lazymatch comparison_code with bind (Done _ _ _ ?opcode_value) _ =>
        let body_code := eval cbn beta iota in (branch_code true) in
        rewrite (opcode_guard_skip opcode_value rhs_code body_code current_frame trace_so_far) by (try reflexivity; lia)
      end
    end
  end.
Local Opaque funcdef_0__intern funcdef_0__ok funcdef_0__no funcdef_0__readToken funcdef_0__readNat
  funcdef_0__lookup funcdef_0__bindName funcdef_0__appendTheorem funcdef_0__modusPonens funcdef_0__generalize
  funcdef_0__rename funcdef_0__predicate funcdef_0__classEqual funcdef_0__classMember funcdef_0__setness
  funcdef_0__axiom funcdef_0__schemaCheck funcdef_0__schemaNode funcdef_0__schemaInstance.
Theorem generated_quit_body reader (f : Frame) readstate observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  meta_value readstate 11 = 0 -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  execLocalObserved (body_with reader) (f,observations) = Some (tt,(quit_frame f readstate,
    observations ++ [{|flushedOutput := stdout readstate ++ bye_bytes; unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hmeta Hnumber Hvalid Herror. destruct f as [s bs ns]. cbn [machine] in Hreader.
  unfold body_with.
  repeat first [skip_opcode |match goal with |- context [execLocalObserved (bind ?code ?next) ?state] => rewrite (local_bind code next state) end |match goal with |- context [execLocalObserved (liftToWithLocalVariables ?code) (?frame,?trace)] => rewrite (lift_correct code frame trace) end |rewrite Hreader
    |rewrite local_done |rewrite local_get |rewrite local_set |rewrite local_write |rewrite local_flush
    |rewrite local_read_meta by (cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite output_length]; lia)
    |rewrite local_store_meta by (cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite output_length]; lia)
    |rewrite output_meta |rewrite meta_store_other by lia |rewrite Hnumber |rewrite Hvalid |rewrite Herror
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 9) with 9%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [execLocalObserved (dropWithinLoop (bind (bind ?code ?next) ?last)) ?state] => rewrite (drop_assoc code next last state) end
    |match goal with |- context [execLocalObserved (dropWithinLoop (bind (liftToWithinLoop ?code) ?next)) ?state] => rewrite (drop_lift code next state) end
    |rewrite dropWithinLoop_1
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by congruence |rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [rewrite (decide_True (P := P)) by congruence |rewrite (decide_False (P := P)) by congruence] end
    |match goal with |- context [execLocalObserved (shortCircuitAnd _ _) _] => unfold shortCircuitAnd at 1 end
    |match goal with |- context [execLocalObserved (shortCircuitOr _ _) _] => unfold shortCircuitOr at 1 end
    |progress cbn [bind optionBind fst snd shortCircuitAnd shortCircuitOr loopString]
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ].
  cbv beta iota zeta delta [quit_frame quit_state bye_bytes withOutput store_meta withMemory memory
    stdout stdin setMachine setNum machine nums bools Imperative.update].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.
End CommandQuitExecution.
