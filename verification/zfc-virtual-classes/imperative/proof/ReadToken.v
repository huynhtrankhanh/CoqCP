From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash InternTail TokenByte Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ReadTokenExecution.
Import IndexExecution SipHashExecution TokenByteExecution.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readToken) withLocalVariablesReturnValue R.
Definition byte_function := (varsfuncdef_0__tokenByte -> bool) -> (varsfuncdef_0__tokenByte -> Z) ->
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition byte_body ch : LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__readToken_body in funcdef_0__readToken_body in
  lazymatch code with context [tapeEnd ?body] => exact (body ch) end).
Definition byte_body_with (byte_proc : byte_function) ch : LocalAction LoopOutcome := ltac:(
  let code := eval unfold byte_body in (byte_body ch) in
  let code := eval cbn beta zeta in code in
  let generalized := eval pattern funcdef_0__tokenByte in code in
  lazymatch generalized with ?family _ => exact (family byte_proc) end).
Lemma actual_byte_body ch : byte_body ch = byte_body_with funcdef_0__tokenByte ch.
Proof. reflexivity. Qed.
Definition byte_arguments ch : varsfuncdef_0__tokenByte -> Z := update (fun _ => 0) vardef_0__tokenByte_ch ch.
Definition byte_outcome (s : Machine) :=
  if bool_decide (meta_value s 17 <> 0) then Stop else if bool_decide (meta_value s 8 <> 0) then Stop else KeepGoing.
Lemma local_done {R} (value : R) (f : Frame) : execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.
Lemma exec_drop_assoc {V} `{EqDecision V} {A B}
  (code : Action (WithinLoop arrayIndex1 (arrayType _ environment1) V) withinLoopReturnValue A)
  (next : A -> Action (WithinLoop arrayIndex1 (arrayType _ environment1) V) withinLoopReturnValue B)
  (last : B -> Action (WithinLoop arrayIndex1 (arrayType _ environment1) V) withinLoopReturnValue unit)
  (f : @Execution.Frame arrayIndex1 (arrayType _ environment1) V) :
  execLocal (dropWithinLoop ((code >>= next) >>= last)) f =
    execLocal (dropWithinLoop (code >>= fun value => next value >>= last)) f.
Proof.
  induction code as [value|e cont IH] in f |- *; [reflexivity|].
  destruct e as [e| |]; cbn [bind dropWithinLoop Action_rect execLocal]; try reflexivity.
  destruct (localStep e f) as [[response after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
Theorem byte_composition byte_proc (f : Frame) ch after :
  coerceInt ch 64 = ch ->
  exec (byte_proc (fun _ => false) (byte_arguments ch)) (machine f) = Some (tt,after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  execLocal (byte_body_with byte_proc ch) f = Some (byte_outcome after,setMachine f after).
Proof.
  intros Hcoerce Hbyte Hmeta. destruct f as [s bs ns]. cbn [machine] in *.
  unfold byte_body_with. unfold byte_arguments in Hbyte.
  destruct (Z.eq_dec (meta_value after 17) 0), (Z.eq_dec (meta_value after 8) 0).
  all: unfold byte_outcome.
  all: repeat first [rewrite execLocal_bind |rewrite exec_drop_assoc |rewrite exec_drop_lift |rewrite execLocal_lift
    |rewrite local_done |rewrite local_read_meta by (cbn [machine setMachine]; lia)
    |rewrite Hcoerce |rewrite Hbyte
    |progress replace (Z.to_nat 17) with 17%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by congruence |rewrite (bool_decide_false P) by congruence] end
    |rewrite dropWithinLoop_break |rewrite dropWithinLoop_1
    |progress cbn [bind optionBind machine setMachine fst snd shortCircuitOr]
  ].
  all: reflexivity.
Qed.
Theorem generated_byte_body (f : Frame) size ch :
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size ->
  (size <= 1024)%nat -> (1024 <= length (memory (machine f) arraydef_0__token))%nat ->
  0 <= ch < 256 ->
  execLocal (byte_body ch) f = Some (byte_outcome (tick (machine f) size ch),setMachine f (tick (machine f) size ch)).
Proof.
  intros Hmeta Hsize Hlimit Htoken Hch. rewrite actual_byte_body. apply byte_composition.
  - apply coerce_word. unfold word, maximum. lia.
  - apply generated_tokenByte; assumption.
  - now rewrite tick_meta_length.
Qed.

Lemma generated_data_byte (f : Frame) size ch :
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size ->
  (size < 1024)%nat -> (1024 <= length (memory (machine f) arraydef_0__token))%nat ->
  0 <= ch < 256 -> ~ separator ch -> meta_value (machine f) 17 = 0 -> meta_value (machine f) 8 = 0 ->
  execLocal (byte_body ch) f = Some (KeepGoing,setMachine f (put_byte (machine f) size ch)).
Proof.
  intros Hmeta Hsize Hlimit Htoken Hbyte Hsep Hdone Herror.
  rewrite (generated_byte_body f size ch Hmeta Hsize ltac:(lia) Htoken Hbyte).
  rewrite tick_data by assumption. unfold byte_outcome.
  rewrite !put_byte_meta_other by lia. rewrite Hdone, Herror, bool_decide_false by congruence. reflexivity.
Qed.
Lemma generated_separator_byte (f : Frame) size ch :
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size ->
  (0 < size <= 1024)%nat -> (1024 <= length (memory (machine f) arraydef_0__token))%nat -> separator ch ->
  execLocal (byte_body ch) f = Some (Stop,setMachine f (store_meta (machine f) 17 1)).
Proof.
  intros Hmeta Hsize Hlimit Htoken Hsep.
  assert (Hbyte : 0 <= ch < 256) by (unfold separator in Hsep; lia).
  rewrite (generated_byte_body f size ch Hmeta Hsize ltac:(lia) Htoken Hbyte).
  rewrite tick_separator by (try assumption; lia). unfold byte_outcome.
  rewrite meta_store_same by lia. rewrite bool_decide_true by discriminate. reflexivity.
Qed.
Fixpoint put_many (s : Machine) size chars := match chars with
| [] => s | ch :: tail => put_many (put_byte s size ch) (S size) tail end.
Lemma put_meta_length s size ch : length (memory (put_byte s size ch) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold put_byte. rewrite store_meta_length. cbn [withMemory memory]. now rewrite InternTailExecution.modify_other by discriminate. Qed.
Lemma put_token_length s size ch : length (memory (put_byte s size ch) arraydef_0__token) = length (memory s arraydef_0__token).
Proof. rewrite put_byte_token. apply length_insert. Qed.
Lemma put_many_meta_length s size chars : length (memory (put_many s size chars) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. induction chars as [|ch tail IH] in s, size |- *; [reflexivity|]. cbn [put_many]. now rewrite IH, put_meta_length. Qed.
Lemma put_many_token_length s size chars : length (memory (put_many s size chars) arraydef_0__token) = length (memory s arraydef_0__token).
Proof. induction chars as [|ch tail IH] in s, size |- *; [reflexivity|]. cbn [put_many]. now rewrite IH, put_token_length. Qed.
Lemma put_many_meta_other s size chars i : i <> 6%nat -> meta_value (put_many s size chars) i = meta_value s i.
Proof. intro H. induction chars as [|ch tail IH] in s, size |- *; [reflexivity|]. cbn [put_many]. now rewrite IH, put_byte_meta_other. Qed.
Lemma put_many_input s size chars input : put_many (withInput s input) size chars = withInput (put_many s size chars) input.
Proof. induction chars as [|ch tail IH] in s, size |- *; [reflexivity|]. cbn [put_many]. now rewrite put_byte_input, IH. Qed.

Theorem payload_tape_execution chars (f : Frame) size sep tail :
  (17 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size ->
  (size + length chars <= 1024)%nat -> (0 < size + length chars)%nat ->
  (1024 <= length (memory (machine f) arraydef_0__token))%nat ->
  meta_value (machine f) 17 = 0 -> meta_value (machine f) 8 = 0 ->
  Forall (fun ch => 0 <= ch < 256 /\ ~ separator ch) chars -> separator sep ->
  stdin (machine f) = chars ++ sep :: tail ->
  tape_execution byte_body f (setMachine f (withInput (store_meta (put_many (machine f) size chars) 17 1) tail)).
Proof.
  induction chars as [|ch chars IH] in f, size |- *.
  - intros Hmeta Hsize Hlimit Hpositive Htoken Hdone Herror Hchars Hsep Hin.
    cbn [List.app put_many length] in *. apply (tape_stop byte_body f sep tail).
    + exact Hin.
    + unfold separator in Hsep. lia.
    + rewrite (generated_separator_byte (setMachine f (withInput (machine f) tail)) size sep Hmeta Hsize
        ltac:(lia) Htoken Hsep). reflexivity.
  - intros Hmeta Hsize Hlimit Hpositive Htoken Hdone Herror Hchars Hsep Hin.
    inversion Hchars as [|ch' chars' Hhead Hrest]; subst ch' chars'. destruct Hhead as [Hbyte Hnosep].
    set (read := setMachine f (withInput (machine f) (chars ++ sep :: tail))).
    set (next := setMachine read (put_byte (machine read) size ch)).
    assert (Hbody : execLocal (byte_body ch) read = Some (KeepGoing,next)).
    { apply generated_data_byte; try assumption; cbn [length] in Hlimit; lia. }
    assert (Hnext : tape_execution byte_body next
      (setMachine next (withInput (store_meta (put_many (machine next) (S size) chars) 17 1) tail))).
    { apply IH.
      - change (17 < length (memory (put_byte (machine read) size ch) arraydef_0__meta))%nat. rewrite put_meta_length. exact Hmeta.
      - change (meta_value (put_byte (machine read) size ch) 6 = Z.of_nat (S size)). apply put_byte_count. change (6 < length (memory (machine f) arraydef_0__meta))%nat. lia.
      - cbn [length] in Hlimit. lia.
      - lia.
      - change (1024 <= length (memory (put_byte (machine read) size ch) arraydef_0__token))%nat. rewrite put_token_length. exact Htoken.
      - change (meta_value (put_byte (machine read) size ch) 17 = 0). rewrite put_byte_meta_other by lia. exact Hdone.
      - change (meta_value (put_byte (machine read) size ch) 8 = 0). rewrite put_byte_meta_other by lia. exact Herror.
      - exact Hrest.
      - exact Hsep.
      - reflexivity. }
    assert (Hrel : setMachine next (withInput (store_meta (put_many (machine next) (S size) chars) 17 1) tail) =
      setMachine f (withInput (store_meta (put_many (machine f) size (ch :: chars)) 17 1) tail)).
    { unfold next, read. cbn [machine setMachine put_many]. rewrite put_byte_input, put_many_input. reflexivity. }
    rewrite <- Hrel. apply (tape_next byte_body f ch (chars ++ sep :: tail) next); try assumption.
    unfold separator in Hnosep. lia.
Qed.

Definition reset (s : Machine) := store_meta (store_meta (store_meta s 6 0) 14 0) 17 0.
Lemma reset_length s : length (memory (reset s) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold reset. now rewrite !store_meta_length. Qed.
Lemma reset_token s : memory (reset s) arraydef_0__token = memory s arraydef_0__token.
Proof. unfold reset. now rewrite !store_meta_other by discriminate. Qed.
Lemma reset_meta s i : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (reset s) i = if bool_decide (i = 6%nat \/ i = 14%nat \/ i = 17%nat) then 0 else meta_value s i.
Proof.
  intro Hlength. unfold reset. destruct (Nat.eq_dec i 6), (Nat.eq_dec i 14), (Nat.eq_dec i 17); subst; try congruence;
  repeat first [rewrite meta_store_other by lia |rewrite meta_store_same by (rewrite ?store_meta_length; lia)
    |rewrite bool_decide_true by tauto |rewrite bool_decide_false by tauto]; reflexivity.
Qed.
Definition read_with (tape_proc : LocalAction unit) (byte_proc : byte_function) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__readToken_body in funcdef_0__readToken_body in
  lazymatch code with context [tapeEnd ?body] =>
    let generalized := eval pattern (tapeEnd body) in code in
    lazymatch generalized with ?family _ =>
      let code := eval cbn beta in (family tape_proc) in
      let generalized := eval pattern funcdef_0__tokenByte in code in
      lazymatch generalized with ?family _ => exact (family byte_proc) end
    end
  end).
Lemma actual_read_body : funcdef_0__readToken_body = read_with (tapeEnd byte_body) funcdef_0__tokenByte.
Proof. reflexivity. Qed.
Lemma read_none_composition tape_proc byte_proc (f : Frame) after :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 15 = 0 -> meta_value (machine f) 8 = 0 ->
  execLocal tape_proc (setMachine f (reset (machine f))) = Some (tt,setMachine f after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  meta_value after 17 = 1 -> meta_value after 8 = 0 -> meta_value after 6 <> 0 ->
  execLocal (read_with tape_proc byte_proc) f = Some (tt,setMachine f (store_meta after 14 1)).
Proof.
  intros Hlength Hpending Herror Htape Hafter Hdone Herr Hsize.
  destruct f as [s bs ns]. cbn [machine] in *.
  unfold read_with. unfold reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
  repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
    |rewrite local_put_meta by (cbn [machine setMachine]; rewrite ?store_meta_length; lia)
    |rewrite local_read_meta by (cbn [machine setMachine]; rewrite ?store_meta_length; lia)
    |rewrite Htape |rewrite meta_store_other by lia |rewrite meta_store_same by (rewrite ?store_meta_length; lia)
    |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr
    |progress replace (Z.to_nat 17) with 17%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 15) with 15%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by congruence |rewrite (bool_decide_false P) by congruence] end
    |progress cbn [bind optionBind machine setMachine fst snd shortCircuitAnd]
    |progress cbv beta iota zeta delta [machine setMachine bools nums]
  ]. reflexivity.
Qed.

Lemma put_many_count s size chars :
  (6 < length (memory s arraydef_0__meta))%nat -> meta_value s 6 = Z.of_nat size ->
  meta_value (put_many s size chars) 6 = Z.of_nat (size + length chars).
Proof.
  induction chars as [|ch chars IH] in s, size |- *.
  - intros Hlength Hsize. cbn [put_many length]. now rewrite Nat.add_0_r.
  - intros Hlength Hsize. cbn [put_many]. rewrite IH.
    + cbn [length]. f_equal. lia.
    + now rewrite put_meta_length.
    + now apply put_byte_count.
Qed.
Definition read_result s chars tail :=
  store_meta (withInput (store_meta (put_many (reset s) 0 chars) 17 1) tail) 14 1.
Lemma result_meta_length s chars tail :
  length (memory (read_result s chars tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold read_result. rewrite store_meta_length. change
  (length (memory (store_meta (put_many (reset s) 0 chars) 17 1) arraydef_0__meta) = length (memory s arraydef_0__meta)).
  now rewrite store_meta_length, put_many_meta_length, reset_length. Qed.
Lemma result_input s chars tail : stdin (read_result s chars tail) = tail.
Proof. reflexivity. Qed.
Lemma result_count s chars tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (read_result s chars tail) 6 = Z.of_nat (length chars).
Proof.
  intro H. unfold read_result. rewrite meta_store_other by lia.
  change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 6 = Z.of_nat (length chars)).
  rewrite meta_store_other by lia. rewrite put_many_count.
  - reflexivity.
  - rewrite reset_length. lia.
  - rewrite reset_meta by exact H. reflexivity.
Qed.
Lemma result_valid s chars tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (read_result s chars tail) 14 = 1.
Proof. intro H. unfold read_result. apply meta_store_same.
  change (14 < length (memory (store_meta (put_many (reset s) 0 chars) 17 1%Z) arraydef_0__meta))%nat.
  rewrite store_meta_length, put_many_meta_length, reset_length. lia. Qed.
Theorem generated_readToken_none s bs ns chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  (0 < length chars <= 1024)%nat ->
  Forall (fun ch => 0 <= ch < 256 /\ ~ separator ch) chars -> separator sep ->
  stdin s = chars ++ sep :: tail ->
  exec (funcdef_0__readToken bs ns) s = Some (tt,read_result s chars tail).
Proof.
  intros Hmeta Htoken Hpending Herror Hchars Hbytes Hsep Hin.
  unfold funcdef_0__readToken. rewrite exec_eliminate, actual_read_body.
  set (f := {|machine := s; bools := bs; nums := ns|} : Frame).
  set (after := withInput (store_meta (put_many (reset s) 0 chars) 17 1) tail).
  assert (Hafterm : (17 < length (memory after arraydef_0__meta))%nat).
  { unfold after. change (17 < length (memory (store_meta (put_many (reset s) 0 chars) 17 1%Z) arraydef_0__meta))%nat.
    now rewrite store_meta_length, put_many_meta_length, reset_length. }
  assert (Htape : execLocal (tapeEnd byte_body) (setMachine f (reset s)) = Some (tt,setMachine f after)).
  { apply tapeEnd_execution. unfold after. change
      (tape_execution byte_body (setMachine f (reset s))
        (setMachine (setMachine f (reset s))
          (withInput (store_meta (put_many (reset s) 0 chars) 17 1) tail))).
    apply (payload_tape_execution chars (setMachine f (reset s)) 0 sep tail); cbn [machine setMachine].
    - now rewrite reset_length.
    - rewrite reset_meta by exact Hmeta. reflexivity.
    - exact (proj2 Hchars).
    - exact (proj1 Hchars).
    - rewrite reset_token. exact Htoken.
    - rewrite reset_meta by exact Hmeta. reflexivity.
    - rewrite reset_meta by exact Hmeta. exact Herror.
    - exact Hbytes.
    - exact Hsep.
    - exact Hin. }
  assert (Hdone : meta_value after 17 = 1).
  { unfold after. change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 17 = 1).
    apply meta_store_same. rewrite put_many_meta_length, reset_length. exact Hmeta. }
  assert (Herr : meta_value after 8 = 0).
  { unfold after. change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 8 = 0).
    rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. exact Herror. }
  assert (Hsize : meta_value after 6 <> 0).
  { unfold after. change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 6 <> 0).
    rewrite meta_store_other by lia. rewrite put_many_count.
    - change (Z.of_nat (length chars) <> 0). intro Hz. change (Z.of_nat (length chars) = Z.of_nat 0) in Hz. apply Nat2Z.inj in Hz. lia.
    - rewrite reset_length. lia.
    - rewrite reset_meta by exact Hmeta. reflexivity. }
  rewrite (read_none_composition (tapeEnd byte_body) funcdef_0__tokenByte f after Hmeta Hpending Herror Htape Hafterm Hdone Herr Hsize).
  reflexivity.
Qed.

Definition started s ch := store_meta (put_byte (reset s) 0 ch) 15 0.
Lemma started_length s ch : length (memory (started s ch) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold started. now rewrite store_meta_length, put_meta_length, reset_length. Qed.
Lemma started_token_length s ch : length (memory (started s ch) arraydef_0__token) = length (memory s arraydef_0__token).
Proof. unfold started. rewrite store_meta_other by discriminate. now rewrite put_token_length, reset_token. Qed.
Lemma started_count s ch : (17 < length (memory s arraydef_0__meta))%nat -> meta_value (started s ch) 6 = 1.
Proof. intro H. unfold started. rewrite meta_store_other by lia. apply put_byte_count. rewrite reset_length. lia. Qed.
Lemma started_zero s ch i : (17 < length (memory s arraydef_0__meta))%nat ->
  (i = 17%nat \/ (i = 8%nat /\ meta_value s 8 = 0)) -> meta_value (started s ch) i = 0.
Proof. intros H [->|[-> Herr]]; unfold started; rewrite meta_store_other by lia;
  rewrite put_byte_meta_other by lia; rewrite reset_meta by exact H; cbn; assumption || reflexivity. Qed.
Lemma read_pending_composition tape_proc byte_proc (f : Frame) ch after :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 15 = ch + 1 -> 0 <= ch < 256 -> ~ separator ch ->
  meta_value (machine f) 8 = 0 ->
  exec (byte_proc (fun _ => false) (byte_arguments ch)) (reset (machine f)) = Some (tt,put_byte (reset (machine f)) 0 ch) ->
  execLocal tape_proc (setMachine f (started (machine f) ch)) = Some (tt,setMachine f after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  meta_value after 17 = 1 -> meta_value after 8 = 0 -> meta_value after 6 <> 0 ->
  execLocal (read_with tape_proc byte_proc) f = Some (tt,setMachine f (store_meta after 14 1)).
Proof.
  intros Hlength Hpending Hch Hsep Herror Hbyte Htape Hafter Hdone Herr Hsize.
  destruct f as [s bs ns]. cbn [machine] in *.
  assert (Hcoerce : coerceInt (ch + 1 - 1) 64 = ch).
  { replace (ch + 1 - 1) with ch by lia. apply coerce_word. unfold word, maximum. lia. }
  unfold read_with. unfold reset in Hbyte. unfold byte_arguments in Hbyte.
  unfold started, reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
  repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
    |rewrite local_put_meta by (cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite put_meta_length |rewrite reset_length]; lia)
    |rewrite local_read_meta by (cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite put_meta_length |rewrite reset_length]; lia)
    |rewrite Htape |rewrite Hbyte |rewrite Hcoerce
    |rewrite put_byte_meta_other by lia
    |rewrite meta_store_other by lia |rewrite meta_store_same by (repeat first [rewrite store_meta_length |rewrite put_meta_length]; lia)
    |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr
    |progress replace (Z.to_nat 17) with 17%nat by reflexivity
    |progress replace (Z.to_nat 15) with 15%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by (try congruence; lia) |rewrite (bool_decide_false P) by (try congruence; lia)] end
    |progress cbn [subInt bind optionBind machine setMachine fst snd shortCircuitAnd]
    |progress cbv beta iota zeta delta [machine setMachine bools nums]
  ]. reflexivity.
Qed.

Definition pending_result s ch chars tail :=
  store_meta (withInput (store_meta (put_many (started s ch) 1 chars) 17 1) tail) 14 1.
Theorem generated_readToken_pending s bs ns ch chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = ch + 1 -> meta_value s 8 = 0 ->
  0 <= ch < 256 -> ~ separator ch -> (S (length chars) <= 1024)%nat ->
  Forall (fun c => 0 <= c < 256 /\ ~ separator c) chars -> separator sep ->
  stdin s = chars ++ sep :: tail ->
  exec (funcdef_0__readToken bs ns) s = Some (tt,pending_result s ch chars tail).
Proof.
  intros Hmeta Htoken Hpending Herror Hch Hnosep Hchars Hbytes Hsep Hin.
  unfold funcdef_0__readToken. rewrite exec_eliminate, actual_read_body.
  set (f := {|machine := s; bools := bs; nums := ns|} : Frame).
  set (after := withInput (store_meta (put_many (started s ch) 1 chars) 17 1) tail).
  assert (Hafterm : (17 < length (memory after arraydef_0__meta))%nat).
  { unfold after. change (17 < length (memory (store_meta (put_many (started s ch) 1 chars) 17 1%Z) arraydef_0__meta))%nat.
    now rewrite store_meta_length, put_many_meta_length, started_length. }
  assert (Htape : execLocal (tapeEnd byte_body) (setMachine f (started s ch)) = Some (tt,setMachine f after)).
  { apply tapeEnd_execution. unfold after. change
      (tape_execution byte_body (setMachine f (started s ch))
        (setMachine (setMachine f (started s ch))
          (withInput (store_meta (put_many (started s ch) 1 chars) 17 1) tail))).
    apply (payload_tape_execution chars (setMachine f (started s ch)) 1 sep tail); cbn [machine setMachine].
    - now rewrite started_length.
    - now apply started_count.
    - exact Hchars.
    - lia.
    - rewrite started_token_length. exact Htoken.
    - apply started_zero; [exact Hmeta|now left].
    - apply started_zero; [exact Hmeta|right; auto].
    - exact Hbytes.
    - exact Hsep.
    - exact Hin. }
  assert (Hdone : meta_value after 17 = 1).
  { unfold after. change (meta_value (store_meta (put_many (started s ch) 1 chars) 17 1) 17 = 1).
    apply meta_store_same. rewrite put_many_meta_length, started_length. exact Hmeta. }
  assert (Herr : meta_value after 8 = 0).
  { unfold after. change (meta_value (store_meta (put_many (started s ch) 1 chars) 17 1) 8 = 0).
    rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. apply started_zero; [exact Hmeta|right; auto]. }
  assert (Hsize : meta_value after 6 <> 0).
  { unfold after. change (meta_value (store_meta (put_many (started s ch) 1 chars) 17 1) 6 <> 0).
    rewrite meta_store_other by lia. rewrite put_many_count.
    - intro Hz. change (Z.of_nat (1 + length chars) = Z.of_nat 0) in Hz. apply Nat2Z.inj in Hz. lia.
    - rewrite started_length. lia.
    - now apply started_count. }
  assert (Hbyte : exec (funcdef_0__tokenByte (fun _ => false) (byte_arguments ch)) (reset s) = Some (tt,put_byte (reset s) 0 ch)).
  { rewrite (generated_tokenByte (reset s) (fun _ => false) (byte_arguments ch) 0).
    - rewrite tick_data by (try exact Hnosep; lia). reflexivity.
    - now rewrite reset_length.
    - rewrite reset_meta by exact Hmeta. reflexivity.
    - lia.
    - rewrite reset_token. exact Htoken.
    - exact Hch. }
  rewrite (read_pending_composition (tapeEnd byte_body) funcdef_0__tokenByte f ch after Hmeta Hpending Hch Hnosep Herror Hbyte Htape Hafterm Hdone Herr Hsize).
  reflexivity.
Qed.

Lemma put_many_before s size chars i : (i < size)%nat ->
  List.nth i (memory (put_many s size chars) arraydef_0__token) 0 = List.nth i (memory s arraydef_0__token) 0.
Proof.
  induction chars as [|ch chars IH] in s, size |- *; [reflexivity|].
  intro H. cbn [put_many]. rewrite IH by lia. rewrite put_byte_token. apply ArrayFacts.nth_insert_other. lia.
Qed.
Lemma put_many_entry s size chars i : (i < length chars)%nat ->
  (size + length chars <= length (memory s arraydef_0__token))%nat ->
  List.nth (size + i) (memory (put_many s size chars) arraydef_0__token) 0 = List.nth i chars 0.
Proof.
  induction chars as [|ch chars IH] in s, size, i |- *; [cbn; lia|].
  intros Hindex Hcapacity. destruct i as [|i].
  - cbn [put_many]. replace (size + 0)%nat with size by lia.
    rewrite put_many_before by lia. rewrite put_byte_token. apply OverflowExecution.nth_insert_same. cbn [length] in Hcapacity. lia.
  - cbn [put_many]. replace (size + S i)%nat with (S size + i)%nat by lia.
    rewrite IH.
    + reflexivity.
    + cbn [length] in Hindex. lia.
    + rewrite put_token_length. cbn [length] in Hcapacity. lia.
Qed.
Lemma put_many_other s size chars name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (put_many s size chars) name = memory s name.
Proof.
  intros Hmeta Htoken. induction chars as [|ch chars IH] in s, size |- *; [reflexivity|].
  cbn [put_many]. rewrite IH. unfold put_byte. rewrite store_meta_other by exact Hmeta.
  now apply InternTailExecution.modify_other.
Qed.
Lemma put_many_output s size chars : stdout (put_many s size chars) = stdout s.
Proof. induction chars as [|ch chars IH] in s, size |- *; [reflexivity|]. cbn [put_many]. rewrite IH. reflexivity. Qed.

Lemma result_token_entry s chars tail i : (i < length chars)%nat ->
  (length chars <= length (memory s arraydef_0__token))%nat ->
  List.nth i (memory (read_result s chars tail) arraydef_0__token) 0 = List.nth i chars 0.
Proof.
  intros Hindex Hcapacity. unfold read_result. rewrite store_meta_other by discriminate.
  change (List.nth i (memory (store_meta (put_many (reset s) 0 chars) 17 1) arraydef_0__token) 0 = List.nth i chars 0).
  rewrite store_meta_other by discriminate. change
    (List.nth (0 + i) (memory (put_many (reset s) 0 chars) arraydef_0__token) 0 = List.nth i chars 0).
  apply put_many_entry; [exact Hindex|now rewrite reset_token].
Qed.
Lemma result_meta_other s chars tail i : i <> 6%nat -> i <> 14%nat -> i <> 17%nat ->
  (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (read_result s chars tail) i = meta_value s i.
Proof.
  intros H6 H14 H17 Hmeta. unfold read_result. rewrite meta_store_other by exact H14.
  change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) i = meta_value s i).
  rewrite meta_store_other by exact H17. rewrite put_many_meta_other by exact H6.
  rewrite reset_meta by exact Hmeta. rewrite bool_decide_false by tauto. reflexivity.
Qed.
Lemma result_other s chars tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (read_result s chars tail) name = memory s name.
Proof.
  intros Hm Ht. unfold read_result. rewrite store_meta_other by exact Hm.
  change (memory (store_meta (put_many (reset s) 0 chars) 17 1) name = memory s name).
  rewrite store_meta_other by exact Hm. rewrite put_many_other by assumption.
  unfold reset. now rewrite !store_meta_other by exact Hm.
Qed.
Lemma result_output s chars tail : stdout (read_result s chars tail) = stdout s.
Proof. unfold read_result. change (stdout (put_many (reset s) 0 chars) = stdout s).
  rewrite put_many_output. reflexivity. Qed.

Lemma pending_meta_length s ch chars tail :
  length (memory (pending_result s ch chars tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold pending_result. rewrite store_meta_length. change
  (length (memory (store_meta (put_many (started s ch) 1 chars) 17 1) arraydef_0__meta) = length (memory s arraydef_0__meta)).
  now rewrite store_meta_length, put_many_meta_length, started_length. Qed.
Lemma pending_token_length s ch chars tail :
  length (memory (pending_result s ch chars tail) arraydef_0__token) = length (memory s arraydef_0__token).
Proof. unfold pending_result. rewrite store_meta_other by discriminate. change
  (length (memory (store_meta (put_many (started s ch) 1 chars) 17 1) arraydef_0__token) = length (memory s arraydef_0__token)).
  rewrite store_meta_other by discriminate. now rewrite put_many_token_length, started_token_length. Qed.
Lemma pending_count s ch chars tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (pending_result s ch chars tail) 6 = Z.of_nat (S (length chars)).
Proof.
  intro H. unfold pending_result. rewrite meta_store_other by lia.
  change (meta_value (store_meta (put_many (started s ch) 1 chars) 17 1) 6 = Z.of_nat (S (length chars))).
  rewrite meta_store_other by lia. rewrite put_many_count.
  - reflexivity.
  - rewrite started_length. lia.
  - now apply started_count.
Qed.
Lemma pending_valid s ch chars tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (pending_result s ch chars tail) 14 = 1.
Proof. intro H. unfold pending_result. apply meta_store_same. change
  (14 < length (memory (store_meta (put_many (started s ch) 1 chars) 17 1%Z) arraydef_0__meta))%nat.
  rewrite store_meta_length, put_many_meta_length, started_length. lia. Qed.
Lemma pending_token_entry s ch chars tail i : (i < S (length chars))%nat ->
  (S (length chars) <= length (memory s arraydef_0__token))%nat ->
  List.nth i (memory (pending_result s ch chars tail) arraydef_0__token) 0 = List.nth i (ch :: chars) 0.
Proof.
  intros Hindex Hcapacity. unfold pending_result. rewrite store_meta_other by discriminate. change
    (List.nth i (memory (store_meta (put_many (started s ch) 1 chars) 17 1) arraydef_0__token) 0 = List.nth i (ch :: chars) 0).
  rewrite store_meta_other by discriminate. destruct i as [|i].
  - rewrite put_many_before by lia. unfold started. rewrite store_meta_other by discriminate.
    rewrite put_byte_token. rewrite OverflowExecution.nth_insert_same.
    + reflexivity.
    + rewrite reset_token. lia.
  - change (List.nth (1+i) (memory (put_many (started s ch) 1 chars) arraydef_0__token) 0 = List.nth i chars 0).
    apply put_many_entry; [lia|]. rewrite started_token_length. exact Hcapacity.
Qed.
Theorem generated_readToken_observed s bs ns after observations :
  exec (funcdef_0__readToken bs ns) s = Some (tt,after) ->
  execObserved (funcdef_0__readToken bs ns) (s,observations) = Some (tt,(after,observations)).
Proof. intro Hrun. apply observed_plain; [apply InternalObservation.readToken_nf|exact Hrun]. Qed.
End ReadTokenExecution.





