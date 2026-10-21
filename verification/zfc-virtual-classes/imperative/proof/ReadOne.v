From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte DecimalInput CommandInput CommandArgs ClassStorage ClassSet ArenaFrame FormulaProjection Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ReadOne.
Import IndexExecution SipHashExecution.
Definition opcode_state s ch chars value sep tail := CommandInput.parsed s ch chars (decimalBytes value ++ sep :: tail).
Definition argument_state s ch chars value sep tail := DecimalInput.encoded_result (opcode_state s ch chars value sep tail) value tail.
Lemma opcode_meta_length s ch chars value sep tail :
  length (memory (opcode_state s ch chars value sep tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. apply CommandInput.parsed_meta_length. Qed.
Lemma argument_meta_length s ch chars value sep tail :
  length (memory (argument_state s ch chars value sep tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold argument_state. now rewrite DecimalInput.encoded_meta_length, opcode_meta_length. Qed.
Lemma argument_other s ch chars value sep tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (argument_state s ch chars value sep tail) name = memory s name.
Proof. intros Hm Ht. unfold argument_state, opcode_state. rewrite DecimalInput.encoded_other by assumption.
  now apply CommandInput.parsed_other. Qed.
Lemma argument_meta_other s ch chars value sep tail i : (17 < length (memory s arraydef_0__meta))%nat ->
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (argument_state s ch chars value sep tail) i = meta_value s i.
Proof.
  intros Hmeta H6 H11 H14 H15 H17. unfold argument_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite opcode_meta_length; assumption).
  unfold opcode_state. now apply CommandInput.parsed_meta_other.
Qed.
Lemma argument_storage s ch chars value sep tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (argument_state s ch chars value sep tail).
Proof.
  intro Hmeta. refine (ArenaFrame.storage_trans s (opcode_state s ch chars value sep tail) _
    (CommandInput.parsed_storage s ch chars _) _).
  apply CommandArgs.encoded_storage. now rewrite opcode_meta_length.
Qed.
Theorem generated_reads s bs ns opcode ch chars value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat opcode <= maximum -> decimalBytes opcode = ch :: chars -> Z.of_nat value <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = chars ++ first_separator :: decimalBytes value ++ last_separator :: tail ->
  let op := opcode_state s ch chars value last_separator tail in
  let arg := argument_state s ch chars value last_separator tail in
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(op,observations)) /\
  execObserved (funcdef_0__readNat bs ns) (op,observations) = Some (tt,(arg,observations)) /\
  (17 < length (memory op arraydef_0__meta))%nat /\ meta_value op 11 = Z.of_nat opcode /\
  meta_value op 14 = 1 /\ meta_value op 8 = 0 /\
  (17 < length (memory arg arraydef_0__meta))%nat /\
  (20 <= length (memory arg arraydef_0__printBuffer))%nat /\
  meta_value arg 11 = Z.of_nat value /\ meta_value arg 14 = 1 /\ meta_value arg 8 = 0 /\
  stdin arg = tail /\ stdout arg = stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Hvalue Hsep1 Hsep2 Hin.
  set (op := opcode_state s ch chars value last_separator tail).
  set (arg := argument_state s ch chars value last_separator tail).
  assert (Hopcode : execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(op,observations))).
  { exact (CommandInput.generated_pending s bs ns opcode ch chars first_separator
      (decimalBytes value ++ last_separator :: tail) observations Hmeta Htoken Hpending Herror Hcode Hencoding Hsep1 Hin). }
  assert (Hopmeta : (17 < length (memory op arraydef_0__meta))%nat) by (unfold op; now rewrite opcode_meta_length).
  assert (Hoptoken : (1024 <= length (memory op arraydef_0__token))%nat).
  { unfold op, opcode_state. now rewrite CommandArgs.pending_token_length. }
  assert (Hopnumber : meta_value op 11 = Z.of_nat opcode).
  { exact (CommandInput.parsed_number s opcode ch chars _ Hmeta Hcode Hencoding). }
  assert (Hopvalid : meta_value op 14 = 1) by (now apply CommandInput.parsed_valid).
  assert (Hoperror : meta_value op 8 = 0).
  { unfold op, opcode_state. rewrite CommandInput.parsed_meta_other by lia. exact Herror. }
  assert (Hopclear : meta_value op 15 = 0) by (now apply CommandArgs.pending_cleared).
  assert (Hopinput : stdin op = decimalBytes value ++ last_separator :: tail) by reflexivity.
  assert (Hargument : execObserved (funcdef_0__readNat bs ns) (op,observations) = Some (tt,(arg,observations))).
  { exact (DecimalInput.generated_readNat_encoded_observed op bs ns value last_separator tail observations
      Hopmeta Hoptoken Hopclear Hoperror Hvalue Hsep2 Hopinput). }
  assert (Hargmeta : (17 < length (memory arg arraydef_0__meta))%nat) by (unfold arg; now rewrite argument_meta_length).
  assert (Hargbuffer : (20 <= length (memory arg arraydef_0__printBuffer))%nat).
  { unfold arg. rewrite argument_other by discriminate. exact Hbuffer. }
  destruct (DecimalInput.encoded_result_correct op value tail Hopmeta Hvalue) as [Hargnumber [Hargin Hargout]].
  assert (Hargvalid : meta_value arg 14 = 1) by (now apply CommandArgs.encoded_valid).
  assert (Hargerror : meta_value arg 8 = 0).
  { unfold arg. rewrite argument_meta_other by (try exact Hmeta; lia). exact Herror. }
  assert (Hinput : stdin arg = tail) by exact Hargin.
  assert (Houtput : stdout arg = stdout s).
  { transitivity (stdout op); [exact Hargout|]. unfold op, opcode_state. apply CommandInput.parsed_output. }
  repeat split; assumption.
Qed.
End ReadOne.
