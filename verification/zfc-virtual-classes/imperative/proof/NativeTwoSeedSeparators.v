From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput SeedInput Observation Startup SeedBootstrap Representation SeedSeparator.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTwoSeedSeparators.
Import IndexExecution SipHashExecution SeedInputExecution StartupExecution.
Definition first2 s key0 key1 sep2 tail := DecimalInput.encoded_result s key0 (decimalBytes key1 ++ sep2 :: tail).
Definition next2 s key0 key1 sep2 tail := store_meta (first2 s key0 key1 sep2 tail) 26 (Z.of_nat key0).
Definition second2 s key0 key1 sep2 tail := DecimalInput.encoded_result (next2 s key0 key1 sep2 tail) key1 tail.
Definition result2 s key0 key1 sep2 tail := store_meta (second2 s key0 key1 sep2 tail) 27 (Z.of_nat key1).
Theorem generated_seed_separator (f : SeedInputExecution.Frame) key0 key1 sep sep2 tail :
  (27 < length (memory (machine f) arraydef_0__meta))%nat ->
  (1024 <= length (memory (machine f) arraydef_0__token))%nat ->
  meta_value (machine f) 15 = 0 -> meta_value (machine f) 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  TokenByteExecution.separator sep -> TokenByteExecution.separator sep2 ->
  stdin (machine f) = decimalBytes key0 ++ sep :: (decimalBytes key1 ++ sep2 :: tail) ->
  execLocal seed_body f = Some (tt,setMachine f (result2 (machine f) key0 key1 sep2 tail)).
Proof.
  intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hsep Hsep2 Hin.
  set (s := machine f). fold s in Hmeta, Htoken, Hpending, Herror, Hin.
  set (first := first2 s key0 key1 sep2 tail).
  set (next := next2 s key0 key1 sep2 tail).
  set (second := second2 s key0 key1 sep2 tail).
  assert (Hmeta0 : (27 < length (memory first arraydef_0__meta))%nat).
  { unfold first, first2. now rewrite DecimalInput.encoded_meta_length. }
  assert (Hmetan : (27 < length (memory next arraydef_0__meta))%nat).
  { unfold next, next2. rewrite store_meta_length. exact Hmeta0. }
  assert (Hmeta1 : (27 < length (memory second arraydef_0__meta))%nat).
  { unfold second, second2. rewrite DecimalInput.encoded_meta_length. exact Hmetan. }
  assert (Hfirst : exec (funcdef_0__readNat (fun _ => false) (fun _ => 0)) s = Some (tt,first)).
  { apply (DecimalInput.generated_readNat_encoded s (fun _ => false) (fun _ => 0) key0 sep (decimalBytes key1 ++ sep2 :: tail)).
    - lia.
    - exact Htoken.
    - exact Hpending.
    - exact Herror.
    - exact Hkey0.
    - exact Hsep.
    - exact Hin. }
  assert (Hval0 : meta_value first 11 = Z.of_nat key0).
  { exact (proj1 (DecimalInput.encoded_result_correct s key0 (decimalBytes key1 ++ sep2 :: tail) ltac:(lia) Hkey0)). }
  assert (Hvalid0 : meta_value first 14 <> 0).
  { unfold first, first2. rewrite encoded_valid by lia. discriminate. }
  assert (Hval1 : meta_value second 11 = Z.of_nat key1).
  { exact (proj1 (DecimalInput.encoded_result_correct next key1 tail ltac:(lia) Hkey1)). }
  assert (Hvalid1 : meta_value second 14 <> 0).
  { change (meta_value (DecimalInput.encoded_result next key1 tail) 14 <> 0). rewrite encoded_valid by lia. discriminate. }
  assert (Hsecond : exec (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (store_meta first 26 (meta_value first 11)) = Some (tt,second)).
  { rewrite Hval0. change (exec (funcdef_0__readNat (fun _ => false) (fun _ => 0)) next = Some (tt,second)).
    apply (DecimalInput.generated_readNat_encoded next (fun _ => false) (fun _ => 0) key1 sep2 tail).
    - lia.
    - unfold next, next2. rewrite store_meta_other by discriminate.
      unfold first2. rewrite DecimalInput.encoded_token_length. exact Htoken.
    - unfold next, next2. rewrite meta_store_other by lia.
      unfold first2. rewrite DecimalInput.encoded_meta_other by lia. exact Hpending.
    - unfold next, next2. rewrite meta_store_other by lia.
      unfold first2. rewrite DecimalInput.encoded_meta_other by lia. exact Herror.
    - exact Hkey1.
    - exact Hsep2.
    - reflexivity. }
  rewrite actual_body.
  rewrite (seed_composition funcdef_0__readNat f first second Hfirst ltac:(lia) Hvalid0 Hsecond Hmeta1 Hvalid1).
  rewrite Hval1. reflexivity.
Qed.


Lemma encoded_tail s value x y :
 DecimalInput.encoded_result s value x = withInput (DecimalInput.encoded_result s value y) x.
Proof.
 unfold DecimalInput.encoded_result,ReadNatExecution.token_number,ReadTokenExecution.read_result.
 repeat rewrite SeedSeparator.store_input.
 destruct (store_meta (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.reset s) 0 (decimalBytes value)) 17 1) 14 1). reflexivity.
Qed.
Lemma encoded_input s input value tail :
 DecimalInput.encoded_result (withInput s input) value tail = DecimalInput.encoded_result s value tail.
Proof.
 unfold DecimalInput.encoded_result,ReadNatExecution.token_number. now rewrite SeedSeparator.read_result_input.
Qed.
Lemma result2_same s key0 key1 sep2 tail :
 result2 s key0 key1 sep2 tail=seed_result s key0 key1 tail.
Proof.
 unfold result2,second2,next2,first2,seed_result,second_state,second_start,first_state.
 rewrite (encoded_tail s key0 (decimalBytes key1 ++ sep2 :: tail) (decimalBytes key1 ++ 10 :: tail)).
 rewrite SeedSeparator.store_input,encoded_input. reflexivity.
Qed.

Theorem generated_main_two_separators s bs ns key0 key1 sep1 sep2 tail observations :
  (27 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
  stdin s = decimalBytes key0 ++ sep1 :: (decimalBytes key1 ++ sep2 :: tail) ->
  execObserved (funcdef_0__main bs ns) (s,observations) =
    execObserved (eliminateLocalVariables bs ns finish_body)
      (seed_result (withOutput s (stdout s ++ Protocol.seed_prompt)) key0 key1 tail,
       observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]).
Proof.
 intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hsep1 Hsep2 Hin.
 rewrite observed_main_factorization, generated_prompt_observed. cbn [optionBind fst snd].
 assert (Hseed: execObserved (seed_program bs ns)
   (withOutput s (stdout s ++ Protocol.seed_prompt),
    observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]) =
   Some (tt,(seed_result (withOutput s (stdout s ++ Protocol.seed_prompt)) key0 key1 tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]))).
 { apply observed_plain; [apply seed_no_flush|]. unfold seed_program. rewrite exec_eliminate.
   rewrite (generated_seed_separator {|machine := withOutput s (stdout s ++ Protocol.seed_prompt); bools := bs; nums := ns|}
    key0 key1 sep1 sep2 tail Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hsep1 Hsep2 Hin).
   rewrite result2_same. reflexivity. }
 rewrite Hseed. reflexivity.
Qed.

End NativeTwoSeedSeparators.
