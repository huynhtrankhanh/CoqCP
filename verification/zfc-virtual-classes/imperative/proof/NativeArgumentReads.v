From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte DecimalInput CommandInput CommandArgs ReadOne NativeArgumentWhitespace.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeArgumentReads.
Import IndexExecution SipHashExecution.
Theorem generated_reads s bs ns opcode ch chars value first_separator prefix last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat opcode <= maximum -> decimalBytes opcode = ch :: chars -> Z.of_nat value <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix ->
  stdin s = chars ++ first_separator :: prefix ++ decimalBytes value ++ last_separator :: tail ->
  let op := CommandInput.parsed s ch chars (prefix++decimalBytes value++last_separator::tail) in
  let arg := ReadOne.argument_state s ch chars value last_separator tail in
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(op,observations)) /\
  execObserved (funcdef_0__readNat bs ns) (op,observations) = Some (tt,(arg,observations)) /\
  (17 < length (memory op arraydef_0__meta))%nat /\ meta_value op 11 = Z.of_nat opcode /\
  meta_value op 14 = 1 /\ meta_value op 8 = 0 /\
  (17 < length (memory arg arraydef_0__meta))%nat /\
  (20 <= length (memory arg arraydef_0__printBuffer))%nat /\
  meta_value arg 11 = Z.of_nat value /\ meta_value arg 14 = 1 /\ meta_value arg 8 = 0 /\
  stdin arg = tail /\ stdout arg = stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Hvalue Hsep1 Hsep2 Hprefix Hin.
  set (op := CommandInput.parsed s ch chars (prefix++decimalBytes value++last_separator::tail)).
  set (arg := ReadOne.argument_state s ch chars value last_separator tail).
  destruct(NativeArgumentWhitespace.generated_opcode_and_argument s bs ns opcode ch chars value first_separator prefix last_separator tail observations
    Hmeta Htoken Hpending Herror Hcode Hencoding Hvalue Hsep1 Hsep2 Hprefix Hin) as [Hopcode Hargument].
  assert (Hopmeta : (17 < length (memory op arraydef_0__meta))%nat) by (unfold op; now rewrite CommandInput.parsed_meta_length).
  assert (Hoptoken : (1024 <= length (memory op arraydef_0__token))%nat).
  { unfold op. now rewrite CommandArgs.pending_token_length. }
  assert (Hopnumber : meta_value op 11 = Z.of_nat opcode).
  { exact (CommandInput.parsed_number s opcode ch chars _ Hmeta Hcode Hencoding). }
  assert (Hopvalid : meta_value op 14 = 1) by (now apply CommandInput.parsed_valid).
  assert (Hoperror : meta_value op 8 = 0).
  { unfold op. rewrite CommandInput.parsed_meta_other by lia. exact Herror. }
  assert (Hopclear : meta_value op 15 = 0) by (now apply CommandArgs.pending_cleared).
  assert (Hargmeta : (17 < length (memory arg arraydef_0__meta))%nat) by (unfold arg; now rewrite ReadOne.argument_meta_length).
  assert (Hargbuffer : (20 <= length (memory arg arraydef_0__printBuffer))%nat).
  { unfold arg. rewrite ReadOne.argument_other by discriminate. exact Hbuffer. }
  destruct (DecimalInput.encoded_result_correct (ReadOne.opcode_state s ch chars value last_separator tail) value tail ltac:(rewrite ReadOne.opcode_meta_length;exact Hmeta) Hvalue) as [Hargnumber [Hargin Hargout]].
  assert (Hargvalid : meta_value arg 14 = 1) by (now apply CommandArgs.encoded_valid).
  assert (Hargerror : meta_value arg 8 = 0).
  { unfold arg. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Herror. }
  assert (Hinput : stdin arg = tail) by exact Hargin.
  assert (Houtput : stdout arg = stdout s).
  { transitivity (stdout op); [exact Hargout|]. unfold ReadOne.opcode_state. apply CommandInput.parsed_output. }
  repeat split; assumption.
Qed.
End NativeArgumentReads.
