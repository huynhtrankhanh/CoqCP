From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure CommandChain CommandDispatch CommandSteps ReplyOK.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module UndoPositiveExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition result s count := ReplyOKExecution.reply_state (store_meta s 3 (Z.of_nat count)) count.
Local Opaque funcdef_0__no funcdef_0__ok.
Theorem generated_handler reader (f : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) count observations :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  (20 <= length (memory (machine f) arraydef_0__printBuffer))%nat ->
  meta_value (machine f) 8 = 0 -> meta_value (machine f) 3 = Z.of_nat (S count) ->
  Z.of_nat (S count) <= maximum ->
  execLocalObserved (CommandStructure.handler_16 reader) (f,observations) =
    Some (tt,(setMachine f (result (machine f) count),
      observations ++ [{|flushedOutput := stdout (machine f) ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := stdin (machine f)|}])).
Proof.
  intros Hmeta Hbuffer Herror Hhistory Hword. destruct f as [s bs ns]. cbn [machine] in *.
  assert (Hcount : Z.of_nat count <= maximum) by lia.
  assert (Hminus : coerceInt (Z.of_nat (S count) - 1) 64 = Z.of_nat count).
  { rewrite coerce_word by (unfold word; lia). lia. }
  assert (Hstored : meta_value (store_meta s 3 (Z.of_nat count)) 3 = Z.of_nat count).
  { apply meta_store_same. lia. }
  unfold CommandStructure.handler_16.
  repeat first [progress cbn [optionBind fst snd]
    |progress unfold subInt at 1
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       rewrite ?store_meta_length;
       eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta])
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bs_ok ?ns_ok) ?state] =>
        lazymatch state with (?current,?trace) =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__ok bs_ok ns_ok) state) in
          let Hok := fresh "Hok" in
          assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current count,
            trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := stdin current|}]))) by
            (apply (ReplyOKExecution.generated_ok current bs_ok ns_ok count trace);
              [reflexivity|exact Hcount|rewrite store_meta_other by discriminate; exact Hbuffer]);
          rewrite Hok; clear Hok
        end
      end
    |match goal with |- context [meta_value (store_meta ?state ?slot ?value) ?index] =>
        first [progress rewrite (meta_store_same state slot value) by (cbn; lia)
              |progress rewrite (meta_store_other state index slot value) by lia] end
    |match goal with |- context [meta_value s 8] => progress rewrite Herror end
    |match goal with |- context [meta_value s 3] => progress rewrite Hhistory end
    |progress rewrite Hminus
    |progress rewrite Hstored
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 3) with 3%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
Lemma result_meta s count i : meta_value (result s count) i = meta_value (store_meta s 3 (Z.of_nat count)) i.
Proof. unfold result, meta_value. now rewrite ReplyOKExecution.reply_other by discriminate. Qed.
Lemma result_meta_length s count :
  length (memory (result s count) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold result. rewrite ReplyOKExecution.reply_other by discriminate. apply store_meta_length. Qed.
Theorem generated_after_read s bs ns readstate count observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  (20 <= length (memory readstate arraydef_0__printBuffer))%nat ->
  meta_value readstate 11 = 16 -> meta_value readstate 14 = 1 ->
  meta_value readstate 8 = 0 -> meta_value readstate 3 = Z.of_nat (S count) -> Z.of_nat (S count) <= maximum ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(result readstate count,
      observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hmeta Hbuffer Hnumber Hvalid Herror Hhistory Hword.
  set (f := {|machine := s; bools := bs; nums := ns|}).
  set (initial := CommandDispatch.opcode_frame f readstate 16).
  set (after := setMachine initial (result readstate count)).
  apply (CommandDispatch.generated_positive_command s bs ns after readstate 16 observations
    (observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := stdin readstate|}]));
    try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_16 funcdef_0__readNat) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes (Protocol.OK count); unreadInput := stdin readstate|}]))).
    now apply generated_handler.
  - change (8 < length (memory (result readstate count) arraydef_0__meta))%nat.
    rewrite result_meta_length. lia.
  - change (meta_value (result readstate count) 8 = 0).
    rewrite result_meta, meta_store_other by lia. exact Herror.
Qed.
End UndoPositiveExecution.
