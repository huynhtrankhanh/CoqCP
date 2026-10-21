From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte DecimalInput CommandInput CommandArgs ClassStorage ClassSet ArenaFrame FormulaProjection Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ClassSetInput.
Import IndexExecution SipHashExecution.
Definition opcode_state s value sep tail := CommandInput.parsed s 53 [] (decimalBytes value ++ sep :: tail).
Definition argument_state s value sep tail := DecimalInput.encoded_result (opcode_state s value sep tail) value tail.
Definition result s n value sep tail := ClassStorage.result (argument_state s value sep tail) n (0%Z,Z.of_nat value).
Lemma opcode_meta_length s value sep tail :
  length (memory (opcode_state s value sep tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. apply CommandInput.parsed_meta_length. Qed.
Lemma argument_meta_length s value sep tail :
  length (memory (argument_state s value sep tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold argument_state. now rewrite DecimalInput.encoded_meta_length, opcode_meta_length. Qed.
Lemma argument_other s value sep tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (argument_state s value sep tail) name = memory s name.
Proof. intros Hm Ht. unfold argument_state, opcode_state. rewrite DecimalInput.encoded_other by assumption.
  now apply CommandInput.parsed_other. Qed.
Lemma argument_meta_other s value sep tail i : (17 < length (memory s arraydef_0__meta))%nat ->
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (argument_state s value sep tail) i = meta_value s i.
Proof.
  intros Hmeta H6 H11 H14 H15 H17. unfold argument_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite opcode_meta_length; assumption).
  unfold opcode_state. now apply CommandInput.parsed_meta_other.
Qed.
Lemma argument_storage s value sep tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (argument_state s value sep tail).
Proof.
  intro Hmeta. refine (ArenaFrame.storage_trans s (opcode_state s value sep tail) _
    (CommandInput.parsed_storage s 53 [] _) _).
  apply CommandArgs.encoded_storage. now rewrite opcode_meta_length.
Qed.
Theorem generated_pending s bs ns n value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 54 -> meta_value s 8 = 0 -> meta_value s 2 = Z.of_nat n ->
  Z.of_nat n < maximum -> Z.of_nat value <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(result s n value last_separator tail,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcount Hword Hvalue Hsep1 Hsep2 Hin.
  set (op := opcode_state s value last_separator tail).
  set (arg := argument_state s value last_separator tail).
  assert (Hfive : Z.of_nat 5 <= maximum) by (unfold maximum; cbn; lia).
  assert (Hopcode : execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations))).
  { exact (CommandInput.generated_pending s (fun _ => false) (fun _ => 0) 5 53 [] first_separator
      (decimalBytes value ++ last_separator :: tail) observations Hmeta Htoken Hpending Herror Hfive eq_refl Hsep1 Hin). }
  assert (Hopmeta : (17 < length (memory op arraydef_0__meta))%nat) by (unfold op; now rewrite opcode_meta_length).
  assert (Hoptoken : (1024 <= length (memory op arraydef_0__token))%nat).
  { unfold op, opcode_state. now rewrite CommandArgs.pending_token_length. }
  assert (Hopnumber : meta_value op 11 = 5).
  { exact (CommandInput.parsed_number s 5 53 [] _ Hmeta Hfive eq_refl). }
  assert (Hopvalid : meta_value op 14 = 1) by (now apply CommandInput.parsed_valid).
  assert (Hoperror : meta_value op 8 = 0).
  { unfold op, opcode_state. rewrite CommandInput.parsed_meta_other by lia. exact Herror. }
  assert (Hopclear : meta_value op 15 = 0) by (now apply CommandArgs.pending_cleared).
  assert (Hopinput : stdin op = decimalBytes value ++ last_separator :: tail) by reflexivity.
  assert (Hargument : execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(arg,observations))).
  { exact (DecimalInput.generated_readNat_encoded_observed op (fun _ => false) (fun _ => 0) value last_separator tail observations
      Hopmeta Hoptoken Hopclear Hoperror Hvalue Hsep2 Hopinput). }
  assert (Hargmeta : (17 < length (memory arg arraydef_0__meta))%nat) by (unfold arg; now rewrite argument_meta_length).
  assert (Hargbuffer : (20 <= length (memory arg arraydef_0__printBuffer))%nat).
  { unfold arg. rewrite argument_other by discriminate. exact Hbuffer. }
  destruct (DecimalInput.encoded_result_correct op value tail Hopmeta Hvalue) as [Hargnumber [Hargin Hargout]].
  assert (Hargvalid : meta_value arg 14 = 1) by (now apply CommandArgs.encoded_valid).
  assert (Hargerror : meta_value arg 8 = 0).
  { unfold arg. rewrite argument_meta_other by (try exact Hmeta; lia). exact Herror. }
  assert (Hargcount : meta_value arg 2 = Z.of_nat n).
  { unfold arg. rewrite argument_meta_other by (try exact Hmeta; lia). exact Hcount. }
  pose proof (ClassSetExecution.generated_command s bs ns op arg n (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargbuffer Hargnumber Hargvalid Hargerror Hargcount Hword) as Hrun.
  assert (Hinput : stdin arg = tail) by exact Hargin.
  assert (Houtput : stdout arg = stdout s).
  { transitivity (stdout op); [exact Hargout|]. unfold op, opcode_state. apply CommandInput.parsed_output. }
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
Lemma result_represents s meaning classes value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s meaning classes ->
  ClassStorage.represents (result s (length classes) value sep tail) meaning (classes ++ [VirtualClasses.set value]).
Proof.
  intros Hmeta [Hcount Hclasses]. unfold result. apply ClassStorage.append_represents.
  - rewrite argument_meta_length. lia.
  - split.
    + rewrite argument_meta_other by (try exact Hmeta; lia). exact Hcount.
    + rewrite argument_other by discriminate. exact Hclasses.
  - unfold ClassStorage.decode. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma result_arena s meaning n value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (result s n value sep tail) meaning.
Proof.
  intros Hmeta Harena. unfold result. apply ClassStorage.result_arena.
  exact (ArenaFrame.storage_arena s (argument_state s value sep tail) meaning (argument_storage s value sep tail Hmeta) Harena).
Qed.
End ClassSetInput.
