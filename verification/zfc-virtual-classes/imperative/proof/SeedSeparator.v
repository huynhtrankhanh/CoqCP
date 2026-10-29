From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput SeedInput Observation Startup SeedBootstrap Representation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SeedSeparator.
Import IndexExecution SipHashExecution SeedInputExecution StartupExecution.
Theorem generated_seed_separator (f : SeedInputExecution.Frame) key0 key1 sep tail :
  (27 < length (memory (machine f) arraydef_0__meta))%nat ->
  (1024 <= length (memory (machine f) arraydef_0__token))%nat ->
  meta_value (machine f) 15 = 0 -> meta_value (machine f) 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  TokenByteExecution.separator sep ->
  stdin (machine f) = decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: tail) ->
  execLocal seed_body f = Some (tt,setMachine f (seed_result (machine f) key0 key1 tail)).
Proof.
  intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hsep Hin.
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
  { apply (DecimalInput.generated_readNat_encoded s (fun _ => false) (fun _ => 0) key0 sep (decimalBytes key1 ++ 10 :: tail)).
    - lia.
    - exact Htoken.
    - exact Hpending.
    - exact Herror.
    - exact Hkey0.
    - exact Hsep.
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

Theorem generated_main_seed_separator s bs ns key0 key1 sep tail observations :
  (27 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum ->
  TokenByteExecution.separator sep ->
  stdin s = decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: tail) ->
  execObserved (funcdef_0__main bs ns) (s,observations) =
    execObserved (eliminateLocalVariables bs ns finish_body)
      (seed_result (withOutput s (stdout s ++ Protocol.seed_prompt)) key0 key1 tail,
       observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]).
Proof.
 intros Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hsep Hin.
 rewrite observed_main_factorization, generated_prompt_observed. cbn [optionBind fst snd].
 assert (Hseed: execObserved (seed_program bs ns)
   (withOutput s (stdout s ++ Protocol.seed_prompt),
    observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]) =
   Some (tt,(seed_result (withOutput s (stdout s ++ Protocol.seed_prompt)) key0 key1 tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.seed_prompt; unreadInput := stdin s|}]))).
 { apply observed_plain; [apply seed_no_flush|]. unfold seed_program. rewrite exec_eliminate.
   rewrite (generated_seed_separator {|machine := withOutput s (stdout s ++ Protocol.seed_prompt); bools := bs; nums := ns|}
    key0 key1 sep tail Hmeta Htoken Hpending Herror Hkey0 Hkey1 Hsep Hin). reflexivity. }
 rewrite Hseed. reflexivity.
Qed.
Lemma store_input s slot value input :
 store_meta (withInput s input) slot value = withInput (store_meta s slot value) input.
Proof. destruct s. reflexivity. Qed.
Lemma read_result_input s input chars tail :
 ReadTokenExecution.read_result (withInput s input) chars tail = ReadTokenExecution.read_result s chars tail.
Proof.
 unfold ReadTokenExecution.read_result,ReadTokenExecution.reset.
 repeat rewrite store_input. rewrite ReadTokenExecution.put_many_input.
 rewrite store_input. destruct (store_meta (ReadTokenExecution.put_many
   (store_meta (store_meta (store_meta s 6 0) 14 0) 17 0) 0 chars) 17 1). reflexivity.
Qed.
Lemma seed_result_input s input key0 key1 tail :
 seed_result (withInput s input) key0 key1 tail = seed_result s key0 key1 tail.
Proof.
 unfold seed_result,second_state,second_start,first_state,DecimalInput.encoded_result,ReadNatExecution.token_number.
 now rewrite read_result_input.
Qed.
Definition alternate_initial key0 key1 sep : Machine :=
 {| memory := arrays _ environment1;
    stdin := decimalBytes key0 ++ sep :: decimalBytes key1 ++ [10]; stdout := [] |}.
Theorem generated_alternate_seed_eof key0 key1 sep bs ns :
 Z.of_nat key0 <= maximum -> Z.of_nat key1 <= maximum -> TokenByteExecution.separator sep ->
 exists final, execObserved (funcdef_0__main bs ns) (alternate_initial key0 key1 sep,[]) = Some (tt,(final,
 [{|flushedOutput := Protocol.seed_prompt; unreadInput := decimalBytes key0 ++ sep :: decimalBytes key1 ++ [10]|};
  {|flushedOutput := Protocol.handshake_output; unreadInput := []|}])) /\
 NativeRepresentation.canonical_arena final [SetTheory.falsity] /\
 meta_value final 0 = 0 /\ meta_value final 8 = 0 /\ stdin final = [] /\ stdout final = Protocol.handshake_output.
Proof.
 intros Hkey0 Hkey1 Hsep.
 set (s := alternate_initial key0 key1 sep).
 set (before := seed_result (SeedBootstrapExecution.initial key0 key1 [] Protocol.seed_prompt) key0 key1 []).
 set (observations := [{|flushedOutput := Protocol.seed_prompt; unreadInput := decimalBytes key0 ++ sep :: decimalBytes key1 ++ [10]|}]).
 assert (Hm : (27 < length (memory s arraydef_0__meta))%nat) by (change (27 < 32)%nat; lia).
 assert (Ht : (1024 <= length (memory s arraydef_0__token))%nat) by (change (1024 <= 1024)%nat; lia).
 assert (Hp : meta_value s 15 = 0) by reflexivity.
 assert (He : meta_value s 8 = 0) by reflexivity.
 assert (Hin : stdin s = decimalBytes key0 ++ sep :: (decimalBytes key1 ++ 10 :: [])) by reflexivity.
 pose proof (generated_main_seed_separator s bs ns key0 key1 sep [] [] Hm Ht Hp He Hkey0 Hkey1 Hsep Hin) as Hprefix.
 assert (Hsame:seed_result (withOutput s (stdout s ++ Protocol.seed_prompt)) key0 key1 []=before).
 { unfold before,s,alternate_initial,SeedBootstrapExecution.initial.
   change (seed_result (withInput {|memory:=arrays _ environment1; stdin:=[]; stdout:=Protocol.seed_prompt|} (decimalBytes key0 ++ sep :: decimalBytes key1 ++ [10])) key0 key1 [] =
           seed_result (withInput {|memory:=arrays _ environment1; stdin:=[]; stdout:=Protocol.seed_prompt|} (Protocol.seed_bytes key0 key1 ++ [])) key0 key1 []).
   now rewrite !seed_result_input. }
 rewrite Hsame in Hprefix.
 change (execObserved (funcdef_0__main bs ns) (s,[]) =
   execObserved (eliminateLocalVariables bs ns finish_body) (before,observations)) in Hprefix.
 assert (Hbmeta : (27 < length (memory before arraydef_0__meta))%nat).
 { unfold before. rewrite seed_meta_length. change (27 < 32)%nat. lia. }
 assert (Hberror : meta_value before 8 = 0).
 { unfold before. rewrite seed_meta_other by (try apply SeedBootstrapExecution.initial_meta; lia). reflexivity. }
 destruct (SeedBootstrapExecution.generated_parsed_bootstrap_observed key0 key1 [] Protocol.seed_prompt observations)
    as [boot [Hboot [Harena [Hzero [Herror [Hinput Houtput]]]]]].
 rewrite actual_finish, finish_zero in Hprefix by (try exact Hberror; lia).
 rewrite success_factorization, generated_prepare_intern in Hprefix by lia.
 change (execObserved (funcdef_0__intern (fun _ => false) SeedBootstrapExecution.bootstrap_arguments)
    (store_meta before 20 1024,observations) = Some (tt,(boot,observations))) in Hboot.
 rewrite Hboot in Hprefix. cbn [optionBind fst snd] in Hprefix.
 rewrite generated_ready_observed in Hprefix. cbn [optionBind fst snd] in Hprefix.
 rewrite generated_commands_eof in Hprefix by exact Hinput.
 exists (withOutput boot (stdout boot ++ Protocol.ready_reply)). split.
 - rewrite Hprefix. rewrite Houtput,Hinput. reflexivity.
 - split; [now apply arena_output|]. split; [exact Hzero|]. split; [exact Herror|]. split; [exact Hinput|].
   change (stdout boot ++ Protocol.ready_reply = Protocol.handshake_output). now rewrite Houtput.
Qed.
End SeedSeparator.
