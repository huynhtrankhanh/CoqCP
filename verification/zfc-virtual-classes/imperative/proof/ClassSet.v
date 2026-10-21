From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash InternTail ObservedLocal CommandQuit CommandStructure CommandSteps CommandDispatch ClassStorage ReplyOK.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ClassSetExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := CommandQuitExecution.Frame.
Lemma local_grow (f : Frame) size zero observations :
  execLocalObserved (grow _ _ _ arraydef_0__classes size zero) (f,observations) =
    Some (tt,(setMachine f (withMemory (machine f) (growArrays (memory (machine f)) arraydef_0__classes (Z.to_nat size) zero)),observations)).
Proof. destruct f. reflexivity. Qed.
Lemma local_store (f : Frame) slot entry observations :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__classes))%nat ->
  execLocalObserved (store _ _ _ arraydef_0__classes slot entry) (f,observations) =
    Some (tt,(setMachine f (withMemory (machine f) (modifyArray (memory (machine f)) arraydef_0__classes (Z.to_nat slot) entry)),observations)).
Proof.
  intro Hbound. cbn [store execLocalObserved localStepObserved fst snd].
  unfold observedStep. cbn [step optionBind fst snd].
  case_decide; [destruct f; reflexivity|lia].
Qed.
Definition frame_after (f : Frame) readstate n value :=
  setMachine (setNum (setMachine f readstate) vardef_0__command_a value) (ClassStorage.result readstate n (0%Z,value)).
Lemma reply_meta s n i : meta_value (ReplyOKExecution.reply_state s n) i = meta_value s i.
Proof. unfold meta_value. now rewrite ReplyOKExecution.reply_other by discriminate. Qed.
Local Opaque funcdef_0__ok funcdef_0__no.
Theorem generated_handler reader (f : Frame) readstate n value observations :
  execObserved (reader (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(readstate,observations)) ->
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  (17 < length (memory readstate arraydef_0__meta))%nat ->
  (20 <= length (memory readstate arraydef_0__printBuffer))%nat ->
  meta_value readstate 11 = value -> meta_value readstate 14 = 1 -> meta_value readstate 8 = 0 ->
  meta_value readstate 2 = Z.of_nat n -> Z.of_nat n < maximum ->
  execLocalObserved (CommandStructure.handler_5 reader) (f,observations) =
    Some (tt,(frame_after f readstate n value,
      observations ++ [{|flushedOutput := stdout readstate ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin readstate|}])).
Proof.
  intros Hreader Hinitial Hinitialerror Hmeta Hbuffer Hnumber Hvalid Herror Hcount Hword.
  destruct f as [s bs ns]. cbn [machine] in *. unfold CommandStructure.handler_5.
  assert (Hnext : coerceInt (Z.of_nat n + 1) 64 = Z.of_nat (S n)).
  { rewrite coerce_word by (unfold word; lia). lia. }
  assert (Hcountword : Z.of_nat n <= maximum) by lia.
  unfold maximum in Hword.
  repeat first [progress cbn [optionBind fst snd]
    |progress unfold addInt at 1
    |progress fold (ClassStorage.grown readstate n)
    |progress fold (ClassStorage.written readstate n (0%Z,value))
    |progress change (withMemory (ClassStorage.grown readstate n)
        (modifyArray (memory (ClassStorage.grown readstate n)) arraydef_0__classes n (0%Z,value)))
        with (ClassStorage.written readstate n (0%Z,value))
    |CommandSteps.primitive ltac:(fun frame slot => cbn [machine setMachine];
       repeat first [rewrite store_meta_length |rewrite ReplyOKExecution.reply_other by discriminate
         |rewrite ClassStorage.written_other by discriminate
         |progress unfold ClassStorage.grown
         |progress cbn [withMemory memory]
         |rewrite growArrays_other by discriminate
         |rewrite InternTailExecution.modify_other by discriminate];
       first [eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m := 17%nat); [cbn; lia|exact Hinitial]])
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (grow _ _ _ arraydef_0__classes ?size ?zero) (?frame,?trace)] =>
        let expression := constr:(@execLocalObserved I T EI V EV R (grow _ _ _ arraydef_0__classes size zero) (frame,trace)) in
        let Hgrow := fresh "Hgrow" in
        assert (Hgrow : expression = Some (tt,(setMachine frame (withMemory (machine frame)
          (growArrays (memory (machine frame)) arraydef_0__classes (Z.to_nat size) zero)),trace))) by
          (exact (local_grow frame size zero trace)); rewrite Hgrow; clear Hgrow
      end
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (store _ _ _ arraydef_0__classes ?slot ?entry) (?frame,?trace)] =>
        let expression := constr:(@execLocalObserved I T EI V EV R (store _ _ _ arraydef_0__classes slot entry) (frame,trace)) in
        let Hstore := fresh "Hstore" in
        assert (Hstore : expression = Some (tt,(setMachine frame (withMemory (machine frame)
          (modifyArray (memory (machine frame)) arraydef_0__classes (Z.to_nat slot) entry)),trace))) by
          (apply (local_store frame slot entry trace); cbn [machine setMachine];
            unfold ClassStorage.grown; cbn [withMemory memory]; rewrite growArrays_same, growList_length, Nat2Z.id; lia);
        rewrite Hstore; clear Hstore
      end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (reader ?bs_read ?ns_read) ?state] =>
        let expression := constr:(@execObserved I T EI R (reader bs_read ns_read) state) in
        let Hread := fresh "Hread" in assert (Hread : expression = Some (tt,(readstate,observations))) by exact Hreader;
        rewrite Hread; clear Hread
      end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bs_ok ?ns_ok) ?state] =>
        lazymatch state with (?current,?trace) =>
          let expression := constr:(@execObserved I T EI R (funcdef_0__ok bs_ok ns_ok) state) in
          let Hok := fresh "Hok" in
          assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current n,
            trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin current|}]))) by
            (apply (ReplyOKExecution.generated_ok current bs_ok ns_ok n trace);
              [reflexivity|exact Hcountword|rewrite ClassStorage.written_other by discriminate; exact Hbuffer]);
          rewrite Hok; clear Hok
        end
      end
    |progress rewrite reply_meta
    |progress rewrite ClassStorage.grown_meta
    |match goal with |- context [meta_value (ClassStorage.written ?state ?num ?entry) ?slot] =>
        progress rewrite (ClassStorage.written_meta state num entry slot) end
    |match goal with |- context [meta_value readstate 11] => progress rewrite Hnumber end
    |match goal with |- context [meta_value readstate 14] => progress rewrite Hvalid end
    |match goal with |- context [meta_value readstate 8] => progress rewrite Herror end
    |match goal with |- context [meta_value readstate 2] => progress rewrite Hcount end
    |match goal with |- context [meta_value s 8] => progress rewrite Hinitialerror end
    |progress rewrite Hnext
    |progress rewrite Nat2Z.id
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 2) with 2%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. unfold frame_after. reflexivity.
Qed.
Theorem generated_command s bs ns opcode_state argument_state n value observations :
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(opcode_state,observations)) ->
  (17 < length (memory opcode_state arraydef_0__meta))%nat ->
  meta_value opcode_state 11 = 5 -> meta_value opcode_state 14 = 1 -> meta_value opcode_state 8 = 0 ->
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (opcode_state,observations) = Some (tt,(argument_state,observations)) ->
  (17 < length (memory argument_state arraydef_0__meta))%nat ->
  (20 <= length (memory argument_state arraydef_0__printBuffer))%nat ->
  meta_value argument_state 11 = value -> meta_value argument_state 14 = 1 -> meta_value argument_state 8 = 0 ->
  meta_value argument_state 2 = Z.of_nat n -> Z.of_nat n < maximum ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(ClassStorage.result argument_state n (0%Z,value),
      observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin argument_state|}])).
Proof.
  intros Hopcode Hmeta Hnumber Hvalid Herror Hargument Haftermeta Hbuffer Ha Haftervalid Haftererror Hcount Hword.
  set (initial := CommandDispatch.opcode_frame {|machine := s; bools := bs; nums := ns|} opcode_state 5).
  set (after := frame_after initial argument_state n value).
  apply (CommandDispatch.generated_positive_command s bs ns after opcode_state 5 observations
    (observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin argument_state|}]));
    try assumption.
  - lia.
  - reflexivity.
  - change (execLocalObserved (CommandStructure.handler_5 funcdef_0__readNat) (initial,observations) =
      Some (tt,(after,observations ++ [{|flushedOutput := stdout argument_state ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := stdin argument_state|}]))).
    now apply generated_handler.
  - change (8 < length (memory (ClassStorage.result argument_state n (0%Z,value)) arraydef_0__meta))%nat.
    rewrite ClassStorage.result_meta_length. lia.
  - change (meta_value (ClassStorage.result argument_state n (0%Z,value)) 8 = 0).
    rewrite ClassStorage.result_meta_other by lia. exact Haftererror.
Qed.
End ClassSetExecution.
