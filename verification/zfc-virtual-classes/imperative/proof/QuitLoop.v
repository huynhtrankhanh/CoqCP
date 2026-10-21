From CoqCP Require Import Options Imperative Execution InteractiveExecution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ObservedLocal CommandQuit QuitInput SeedInput Startup ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module QuitLoopExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := SeedInputExecution.Frame.
Definition LocalAction R := SeedInputExecution.LocalAction R.
Definition callback ch : LocalAction LoopOutcome := ltac:(
  let code := eval unfold StartupExecution.commands_body in StartupExecution.commands_body in
  lazymatch code with context [tapeEnd ?body] => exact (body ch) end).
Lemma tape_stops (body : Z -> LocalAction LoopOutcome) (f : Frame) observations ch tail after trace :
  stdin (machine f) = ch :: tail -> ch <> 2^64-1 ->
  execLocalObserved (body ch) (setMachine f (withInput (machine f) tail),observations) = Some (Stop,(after,trace)) ->
  execLocalObserved (tapeEnd body) (f,observations) = Some (tt,(after,trace)).
Proof.
  destruct f as [[values input output] bs ns]. cbn [machine stdin]. intros Hin Hch Hbody. subst input.
  change (execLocalObserved (loop (S (S (length tail))) (tape_body body))
    ({|machine := {|memory := values; stdin := ch :: tail; stdout := output|}; bools := bs; nums := ns|},observations) = Some (tt,(after,trace))).
  rewrite loop_S, local_bind. unfold tape_body. rewrite local_bind.
  cbn [readChar execLocalObserved localStepObserved observedStep step optionBind fst snd machine setMachine withInput stdin].
  cbv beta iota zeta delta [machine setMachine withInput stdin stdout memory nums bools] in Hbody |- *.
  unfold Frame, SeedInputExecution.Frame in Hbody.
  destruct (Z.eq_dec ch (2^64-1)); [contradiction|]. rewrite Hbody. reflexivity.
Qed.
Lemma local_done {R} (value : R) (f : Frame) observations :
  execLocalObserved (Done _ _ _ value) (f,observations) = Some (value,(f,observations)).
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
Definition callback_result s tail := CommandQuitExecution.quit_state (QuitInputExecution.parsed_quit (store_meta s 15 49) tail).
Lemma callback_meta_length s tail : length (memory (callback_result s tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof.
  unfold callback_result, CommandQuitExecution.quit_state. change
    (length (memory (store_meta (QuitInputExecution.parsed_quit (store_meta s 15 49) tail) 9 1) arraydef_0__meta) = length (memory s arraydef_0__meta)).
  unfold QuitInputExecution.parsed_quit, ReadNatExecution.token_number.
  now rewrite !store_meta_length, ReadTokenExecution.pending_meta_length, store_meta_length.
Qed.
Local Opaque funcdef_0__command.
Theorem generated_callback_quit (f : Frame) tail observations :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  (1024 <= length (memory (machine f) arraydef_0__token))%nat -> meta_value (machine f) 8 = 0 ->
  stdin (machine f) = 10 :: tail ->
  execLocalObserved (callback 48) (f,observations) = Some (Stop,(setMachine f (callback_result (machine f) tail),
    observations ++ [{|flushedOutput := stdout (machine f) ++ CommandQuitExecution.bye_bytes; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Herror Hin. destruct f as [s bs ns]. cbn [machine] in *.
  set (pending := store_meta s 15 49).
  assert (Hpending : meta_value pending 15 = 49) by (apply meta_store_same; lia).
  assert (Herr : meta_value pending 8 = 0) by (unfold pending; rewrite meta_store_other by lia; exact Herror).
  assert (Hreadym : (17 < length (memory pending arraydef_0__meta))%nat) by (unfold pending; now rewrite store_meta_length).
  assert (Hreadyt : (1024 <= length (memory pending arraydef_0__token))%nat) by (unfold pending; now rewrite store_meta_other by discriminate).
  pose proof (QuitInputExecution.generated_quit_pending pending (fun _ => false) (fun _ => 0) 10 tail observations
    Hreadym Hreadyt Hpending Herr ltac:(unfold TokenByteExecution.separator; tauto) Hin) as Hquit.
  assert (Hstop : meta_value (callback_result s tail) 9 = 1) by (apply QuitInputExecution.quit_stop; exact Hreadym).
  assert (Hmfinal : (17 < length (memory (callback_result s tail) arraydef_0__meta))%nat) by (now rewrite callback_meta_length).
  change (execObserved (funcdef_0__command (fun _ => false) (fun _ => 0)) (pending,observations) =
    Some (tt,(callback_result s tail, observations ++ [{|flushedOutput := stdout s ++ CommandQuitExecution.bye_bytes; unreadInput := tail|}]))) in Hquit.
  unfold pending in Hquit. unfold callback.
  repeat first [rewrite local_bind |rewrite drop_assoc |rewrite drop_lift |rewrite lift_correct |rewrite Hquit
    |rewrite local_done
    |rewrite local_store_meta by (cbn [machine setMachine]; lia)
    |rewrite local_read_meta by (cbn [machine setMachine]; lia)
    |progress replace (48 + 1)%Z with 49%Z by reflexivity
    |progress replace (Z.to_nat 15) with 15%nat by reflexivity
    |progress replace (Z.to_nat 9) with 9%nat by reflexivity
    |rewrite Hstop |rewrite dropWithinLoop_break |rewrite dropWithinLoop_1
    |match goal with |- context [coerceInt ?value 64] =>
      rewrite (coerce_word value) by (unfold word, maximum; lia) end
    |rewrite bool_decide_true by congruence
    |progress cbn [bind addInt optionBind fst snd]
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.

Lemma actual_commands : StartupExecution.commands_body = tapeEnd callback >>= fun _ => Done _ _ _ tt.
Proof. reflexivity. Qed.
Definition loop_result s tail := callback_result (withInput s (10 :: tail)) tail.
Theorem generated_loop_quit s bs ns tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat -> meta_value s 8 = 0 ->
  stdin s = 48 :: 10 :: tail ->
  execObserved (eliminateLocalVariables bs ns StartupExecution.commands_body) (s,observations) =
    Some (tt,(loop_result s tail,
      observations ++ [{|flushedOutput := stdout s ++ CommandQuitExecution.bye_bytes; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Herror Hin.
  set (f := {|machine := s; bools := bs; nums := ns|} : Frame).
  pose proof (generated_callback_quit (setMachine f (withInput s (10 :: tail))) tail observations Hmeta Htoken Herror ltac:(reflexivity)) as Hcallback.
  pose proof (tape_stops callback f observations 48 (10 :: tail)
    (setMachine f (loop_result s tail))
    (observations ++ [{|flushedOutput := stdout s ++ CommandQuitExecution.bye_bytes; unreadInput := tail|}])
    Hin ltac:(lia) Hcallback) as Htape.
  rewrite actual_commands, SeedInputExecution.observed_local_bind, ObservedLocal.eliminate_correct. fold f.
  unfold Frame, SeedInputExecution.Frame in Htape. rewrite Htape. reflexivity.
Qed.
Lemma loop_input s tail : stdin (loop_result s tail) = tail.
Proof. reflexivity. Qed.
Lemma loop_output s tail : stdout (loop_result s tail) = stdout s ++ CommandQuitExecution.bye_bytes.
Proof. reflexivity. Qed.
Lemma loop_stop s tail : (17 < length (memory s arraydef_0__meta))%nat -> meta_value (loop_result s tail) 9 = 1.
Proof. intro Hmeta. apply QuitInputExecution.quit_stop. rewrite store_meta_length. exact Hmeta. Qed.
Lemma loop_storage s tail : ArenaFrame.storage s (loop_result s tail).
Proof.
  unfold loop_result, callback_result.
  apply (ArenaFrame.storage_trans s (store_meta (withInput s (10 :: tail)) 15 49)).
  - apply (ArenaFrame.storage_trans s (withInput s (10 :: tail))); [apply ArenaFrame.storage_input|].
    apply ArenaFrame.storage_meta; lia.
  - apply QuitInputExecution.quit_storage.
Qed.
Lemma input_meta s input i : meta_value (withInput s input) i = meta_value s i.
Proof. reflexivity. Qed.
Lemma loop_error s tail : meta_value (loop_result s tail) 8 = meta_value s 8.
Proof.
  unfold loop_result, callback_result, CommandQuitExecution.quit_state, QuitInputExecution.parsed_quit,
    ReadNatExecution.token_number, ReadTokenExecution.pending_result, ReadTokenExecution.started, ReadTokenExecution.reset.
  cbn [ReadTokenExecution.put_many].
  repeat first [rewrite CommandQuitExecution.output_meta |rewrite input_meta |rewrite meta_store_other by lia
    |rewrite TokenByteExecution.put_byte_meta_other by lia]. reflexivity.
Qed.
End QuitLoopExecution.

