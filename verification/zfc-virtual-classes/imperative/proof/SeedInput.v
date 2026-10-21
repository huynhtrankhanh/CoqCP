From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module SeedInputExecution.
Import IndexExecution SipHashExecution.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue R.
Definition reader_function := (varsfuncdef_0__readNat -> bool) -> (varsfuncdef_0__readNat -> Z) ->
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
(* The two reads and validation branches are selected from main, after its
   prompt/flush and before the final fatal/success branch. *)
Definition seed_body : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind ?read ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind ?validate _ => exact (read >>= fun _ => validate) end
      end
    end
  end).
Definition body_with (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold seed_body in seed_body in
  let generalized := eval pattern funcdef_0__readNat in code in
  lazymatch generalized with ?family _ => exact (family reader) end).
Lemma actual_body : seed_body = body_with funcdef_0__readNat.
Proof. reflexivity. Qed.
Lemma local_done {R} (value : R) (f : Frame) : execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.
Lemma seed_composition reader (f : Frame) first second :
  exec (reader (fun _ => false) (fun _ => 0)) (machine f) = Some (tt,first) ->
  (26 < length (memory first arraydef_0__meta))%nat -> meta_value first 14 <> 0 ->
  exec (reader (fun _ => false) (fun _ => 0)) (store_meta first 26 (meta_value first 11)) = Some (tt,second) ->
  (27 < length (memory second arraydef_0__meta))%nat -> meta_value second 14 <> 0 ->
  execLocal (body_with reader) f = Some (tt,setMachine f (store_meta second 27 (meta_value second 11))).
Proof.
  intros Hfirst Hmfirst Hvalidfirst Hsecond Hmsecond Hvalidsecond.
  destruct f as [s bs ns]. cbn [machine] in Hfirst.
  unfold body_with.
  repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
    |rewrite Hfirst |rewrite Hsecond
    |rewrite local_read_meta by (cbn [machine setMachine]; lia)
    |rewrite local_put_meta by (cbn [machine setMachine]; lia)
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 26) with 26%nat by reflexivity
    |progress replace (Z.to_nat 27) with 27%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by congruence |rewrite (bool_decide_false P) by congruence] end
    |progress cbn [bind optionBind fst snd]
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.

Definition first_state s key0 key1 tail := DecimalInput.encoded_result s key0 (decimalBytes key1 ++ 10 :: tail).
Definition second_start s key0 key1 tail := store_meta (first_state s key0 key1 tail) 26 (Z.of_nat key0).
Definition second_state s key0 key1 tail := DecimalInput.encoded_result (second_start s key0 key1 tail) key1 tail.
Definition seed_result s key0 key1 tail := store_meta (second_state s key0 key1 tail) 27 (Z.of_nat key1).
Lemma encoded_valid s value tail : (17 < length (memory s arraydef_0__meta))%nat ->
  meta_value (DecimalInput.encoded_result s value tail) 14 = 1.
Proof. intro H. unfold DecimalInput.encoded_result, ReadNatExecution.token_number.
  rewrite meta_store_other by lia. now apply ReadTokenExecution.result_valid. Qed.
Theorem generated_seed_input (f : Frame) key0 key1 tail :
  (27 < length (memory (machine f) arraydef_0__meta))%nat ->
  (1024 <= length (memory (machine f) arraydef_0__token))%nat ->
  meta_value (machine f) 15 = 0 -> meta_value (machine f) 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  stdin (machine f) = decimalBytes key0 ++ 32 :: (decimalBytes key1 ++ 10 :: tail) ->
  execLocal seed_body f = Some (tt,setMachine f (seed_result (machine f) key0 key1 tail)).
Proof.
  intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hin.
  set (s := machine f). fold s in Hmeta, Htoken, Hpending, Herror, Hin.
  set (first := first_state s key0 key1 tail).
  set (next := second_start s key0 key1 tail).
  set (second := second_state s key0 key1 tail).
  assert (Hmeta0 : (27 < length (memory first arraydef_0__meta))%nat).
  { unfold first, first_state. now rewrite DecimalInput.encoded_meta_length. }
  assert (Hmetan : (27 < length (memory next arraydef_0__meta))%nat).
  { unfold next, second_start. rewrite store_meta_length. exact Hmeta0. }
  assert (Hmeta1 : (27 < length (memory second arraydef_0__meta))%nat).
  { unfold second, second_state. rewrite DecimalInput.encoded_meta_length. exact Hmetan. }
  assert (Hfirst : exec (funcdef_0__readNat (fun _ => false) (fun _ => 0)) s = Some (tt,first)).
  { apply (DecimalInput.generated_readNat_encoded s (fun _ => false) (fun _ => 0) key0 32 (decimalBytes key1 ++ 10 :: tail)).
    - lia.
    - exact Htoken.
    - exact Hpending.
    - exact Herror.
    - exact Hkey0.
    - unfold TokenByteExecution.separator. tauto.
    - exact Hin. }
  assert (Hval0 : meta_value first 11 = Z.of_nat key0).
  { exact (proj1 (DecimalInput.encoded_result_correct s key0 (decimalBytes key1 ++ 10 :: tail) ltac:(lia) Hkey0)). }
  assert (Hvalid0 : meta_value first 14 <> 0).
  { unfold first, first_state. rewrite encoded_valid by lia. discriminate. }
  assert (Hval1 : meta_value second 11 = Z.of_nat key1).
  { exact (proj1 (DecimalInput.encoded_result_correct next key1 tail ltac:(lia) Hkey1)). }
  assert (Hvalid1 : meta_value second 14 <> 0).
  { change (meta_value (DecimalInput.encoded_result next key1 tail) 14 <> 0). rewrite encoded_valid by lia. discriminate. }
  assert (Hsecond : exec (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (store_meta first 26 (meta_value first 11)) = Some (tt,second)).
  { rewrite Hval0. change (exec (funcdef_0__readNat (fun _ => false) (fun _ => 0)) next = Some (tt,second)).
    apply (DecimalInput.generated_readNat_encoded next (fun _ => false) (fun _ => 0) key1 10 tail).
    - lia.
    - unfold next, second_start. rewrite store_meta_other by discriminate.
      unfold first_state. rewrite DecimalInput.encoded_token_length. exact Htoken.
    - unfold next, second_start. rewrite meta_store_other by lia.
      unfold first_state. rewrite DecimalInput.encoded_meta_other by lia. exact Hpending.
    - unfold next, second_start. rewrite meta_store_other by lia.
      unfold first_state. rewrite DecimalInput.encoded_meta_other by lia. exact Herror.
    - exact Hkey1.
    - unfold TokenByteExecution.separator. tauto.
    - reflexivity. }
  rewrite actual_body.
  rewrite (seed_composition funcdef_0__readNat f first second Hfirst ltac:(lia) Hvalid0 Hsecond Hmeta1 Hvalid1).
  rewrite Hval1. reflexivity.
Qed.

Lemma seed_meta_length s key0 key1 tail :
  length (memory (seed_result s key0 key1 tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold seed_result, second_state, second_start, first_state.
  now rewrite store_meta_length, DecimalInput.encoded_meta_length, store_meta_length, DecimalInput.encoded_meta_length. Qed.
Lemma seed_token_length s key0 key1 tail :
  length (memory (seed_result s key0 key1 tail) arraydef_0__token) = length (memory s arraydef_0__token).
Proof. unfold seed_result, second_state, second_start, first_state.
  rewrite store_meta_other by discriminate. rewrite DecimalInput.encoded_token_length.
  rewrite store_meta_other by discriminate. apply DecimalInput.encoded_token_length. Qed.
Theorem seed_keys s key0 key1 tail : (27 < length (memory s arraydef_0__meta))%nat ->
  meta_value (seed_result s key0 key1 tail) 26 = Z.of_nat key0 /\
  meta_value (seed_result s key0 key1 tail) 27 = Z.of_nat key1.
Proof.
  intro Hmeta. unfold seed_result, second_state, second_start, first_state. split.
  - rewrite meta_store_other by lia. rewrite DecimalInput.encoded_meta_other.
    + apply meta_store_same. rewrite DecimalInput.encoded_meta_length. lia.
    + rewrite store_meta_length, DecimalInput.encoded_meta_length. lia.
    + lia.
    + lia.
    + lia.
    + lia.
  - apply meta_store_same. rewrite DecimalInput.encoded_meta_length, store_meta_length, DecimalInput.encoded_meta_length. exact Hmeta.
Qed.
Lemma seed_input s key0 key1 tail : stdin (seed_result s key0 key1 tail) = tail.
Proof. reflexivity. Qed.
Lemma seed_other s key0 key1 tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (seed_result s key0 key1 tail) name = memory s name.
Proof. intros Hm Ht. unfold seed_result, second_state, second_start, first_state.
  rewrite store_meta_other by exact Hm. rewrite DecimalInput.encoded_other by assumption.
  rewrite store_meta_other by exact Hm. now apply DecimalInput.encoded_other. Qed.
Lemma seed_meta_other s key0 key1 tail i : (27 < length (memory s arraydef_0__meta))%nat ->
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 17%nat -> i <> 26%nat -> i <> 27%nat ->
  meta_value (seed_result s key0 key1 tail) i = meta_value s i.
Proof.
  intros Hm H6 H11 H14 H17 H26 H27. unfold seed_result, second_state, second_start, first_state.
  rewrite meta_store_other by exact H27. rewrite DecimalInput.encoded_meta_other.
  - rewrite meta_store_other by exact H26. apply DecimalInput.encoded_meta_other; try assumption; lia.
  - rewrite store_meta_length, DecimalInput.encoded_meta_length. lia.
  - exact H6.
  - exact H11.
  - exact H14.
  - exact H17.
Qed.
Lemma seed_output s key0 key1 tail : stdout (seed_result s key0 key1 tail) = stdout s.
Proof.
  unfold seed_result, second_state, second_start, first_state, DecimalInput.encoded_result, ReadNatExecution.token_number.
  change (stdout (ReadTokenExecution.read_result
    (store_meta (store_meta (ReadTokenExecution.read_result s (decimalBytes key0) (decimalBytes key1 ++ 10 :: tail)) 11 (ReadNatExecution.number_from 0 (decimalBytes key0))) 26 (Z.of_nat key0))
    (decimalBytes key1) tail) = stdout s).
  rewrite ReadTokenExecution.result_output. change (stdout (ReadTokenExecution.read_result s (decimalBytes key0) (decimalBytes key1 ++ 10 :: tail)) = stdout s).
  apply ReadTokenExecution.result_output.
Qed.

Definition seed_program bs ns := eliminateLocalVariables bs ns seed_body.
Theorem seed_no_flush bs ns : NoFlush (seed_program bs ns).
Proof.
  pose proof InternalObservation.readNat_nf as Hreader.
  unfold seed_program. apply InternalObservation.eliminate_nf. unfold seed_body. InternalObservation.nf.
Qed.
Theorem generated_seed_program s bs ns key0 key1 tail :
  (27 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  stdin s = decimalBytes key0 ++ 32 :: (decimalBytes key1 ++ 10 :: tail) ->
  exec (seed_program bs ns) s = Some (tt,seed_result s key0 key1 tail).
Proof.
  intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hin.
  unfold seed_program. rewrite exec_eliminate.
  rewrite (generated_seed_input {|machine := s; bools := bs; nums := ns|} key0 key1 tail Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hin).
  reflexivity.
Qed.
Lemma seed_wire_parts key0 key1 tail :
  Protocol.seed_bytes key0 key1 ++ tail = decimalBytes key0 ++ 32 :: (decimalBytes key1 ++ 10 :: tail).
Proof. unfold Protocol.seed_bytes. cbn [Protocol.join_tokens]. repeat rewrite <- List.app_assoc. reflexivity. Qed.
Theorem generated_seed_wire s bs ns key0 key1 tail observations :
  (27 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  stdin s = Protocol.seed_bytes key0 key1 ++ tail ->
  execObserved (seed_program bs ns) (s,observations) = Some (tt,(seed_result s key0 key1 tail,observations)).
Proof.
  intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hin.
  apply observed_plain; [apply seed_no_flush|]. apply (generated_seed_program s bs ns key0 key1 tail); try assumption.
  now rewrite seed_wire_parts in Hin.
Qed.

Ltac main_parts code use :=
  lazymatch code with bind ?prompt ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind ?flush_part ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind ?read ?next =>
        let code := eval cbn beta in (next tt) in
        lazymatch code with bind ?validate ?next =>
          let code := eval cbn beta in (next tt) in use prompt flush_part code
        end
      end
    end
  end.
Definition prompt_body : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  main_parts code ltac:(fun prompt flush_part finish => exact (prompt >>= fun _ => flush_part))).
Definition finish_body : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  main_parts code ltac:(fun prompt flush_part finish => exact finish)).
Lemma sequence_factorization (a b c d e : LocalAction unit) (f : Frame) :
  execLocal (a >>= fun _ => b >>= fun _ => c >>= fun _ => d >>= fun _ => e) f =
  optionBind (execLocal (a >>= fun _ => b) f) (fun first =>
    optionBind (execLocal (c >>= fun _ => d) (snd first)) (fun second => execLocal e (snd second))).
Proof.
  repeat rewrite execLocal_bind.
  destruct (execLocal a f) as [[[] fa]|]; cbn [optionBind fst snd]; [|reflexivity].
  repeat rewrite execLocal_bind.
  destruct (execLocal b fa) as [[[] fb]|]; cbn [optionBind fst snd]; [|reflexivity].
  repeat rewrite execLocal_bind.
  destruct (execLocal c fb) as [[[] fc]|]; cbn [optionBind fst snd]; [|reflexivity].
  repeat rewrite execLocal_bind.
  destruct (execLocal d fc) as [[[] fd]|]; reflexivity.
Qed.
Lemma main_factorization (f : Frame) :
  execLocal funcdef_0__main_body f =
  optionBind (execLocal prompt_body f) (fun first =>
    optionBind (execLocal seed_body (snd first)) (fun second => execLocal finish_body (snd second))).
Proof. unfold funcdef_0__main_body, prompt_body, seed_body, finish_body. apply sequence_factorization. Qed.

Theorem generated_prompt_observed s bs ns observations :
  execObserved (eliminateLocalVariables bs ns prompt_body) (s,observations) =
    Some (tt,(withOutput s (stdout s ++ Protocol.seed_prompt),
      observations ++ [{| flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s |}])).
Proof.
  unfold prompt_body.
  cbv beta iota zeta delta [loopString dropWithinLoop liftToWithinLoop liftToWithLocalVariables Action_rect
    bind writeChar flush eliminateLocalVariables execObserved observedStep step optionBind fst snd
    withOutput stdout stdin Protocol.seed_prompt].
  repeat rewrite <- List.app_assoc. reflexivity.
Qed.

Lemma observed_local_bind (code : LocalAction unit) (next : unit -> LocalAction unit) bs ns state :
  execObserved (eliminateLocalVariables bs ns (code >>= next)) state =
  optionBind (execObserved (eliminateLocalVariables bs ns code) state)
    (fun response => execObserved (eliminateLocalVariables bs ns (next (fst response))) (snd response)).
Proof.
  induction code as [value|effect cont IH] in state |- *; [reflexivity|].
  destruct effect as [effect|name|name value|name|name value]; try destruct name.
  cbn [bind eliminateLocalVariables Action_rect execObserved].
  destruct (observedStep effect state) as [[value after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
Lemma observed_sequence_factorization (a b c d e : LocalAction unit) bs ns state :
  execObserved (eliminateLocalVariables bs ns (a >>= fun _ => b >>= fun _ => c >>= fun _ => d >>= fun _ => e)) state =
  optionBind (execObserved (eliminateLocalVariables bs ns (a >>= fun _ => b)) state) (fun first =>
    optionBind (execObserved (eliminateLocalVariables bs ns (c >>= fun _ => d)) (snd first))
      (fun second => execObserved (eliminateLocalVariables bs ns e) (snd second))).
Proof.
  repeat rewrite observed_local_bind.
  destruct (execObserved (eliminateLocalVariables bs ns a) state) as [[[] fa]|]; cbn [optionBind fst snd]; [|reflexivity].
  repeat rewrite observed_local_bind.
  destruct (execObserved (eliminateLocalVariables bs ns b) fa) as [[[] fb]|]; cbn [optionBind fst snd]; [|reflexivity].
  repeat rewrite observed_local_bind.
  destruct (execObserved (eliminateLocalVariables bs ns c) fb) as [[[] fc]|]; cbn [optionBind fst snd]; [|reflexivity].
  repeat rewrite observed_local_bind.
  destruct (execObserved (eliminateLocalVariables bs ns d) fc) as [[[] fd]|]; reflexivity.
Qed.
Lemma observed_main_factorization s bs ns observations :
  execObserved (funcdef_0__main bs ns) (s,observations) =
  optionBind (execObserved (eliminateLocalVariables bs ns prompt_body) (s,observations)) (fun first =>
    optionBind (execObserved (seed_program bs ns) (snd first))
      (fun second => execObserved (eliminateLocalVariables bs ns finish_body) (snd second))).
Proof. unfold funcdef_0__main, funcdef_0__main_body, prompt_body, seed_program, seed_body, finish_body.
  apply observed_sequence_factorization. Qed.
Theorem generated_main_seed_prefix s bs ns key0 key1 tail observations :
  (27 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  stdin s = Protocol.seed_bytes key0 key1 ++ tail ->
  execObserved (funcdef_0__main bs ns) (s,observations) =
    execObserved (eliminateLocalVariables bs ns finish_body)
      (seed_result (withOutput s (stdout s ++ Protocol.seed_prompt)) key0 key1 tail,
       observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]).
Proof.
  intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hin.
  rewrite observed_main_factorization, generated_prompt_observed. cbn [optionBind fst snd].
  rewrite (generated_seed_wire (withOutput s (stdout s ++ Protocol.seed_prompt)) bs ns key0 key1 tail
    (observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}])
    Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hin). reflexivity.
Qed.
End SeedInputExecution.


