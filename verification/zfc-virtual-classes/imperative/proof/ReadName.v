From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken CommandInput CommandArgs NameRepresentation ClassStorage HistoryRefinement ArenaFrame FormulaProjection.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ReadName.
Import IndexExecution SipHashExecution.
Definition result := ReadTokenExecution.read_result.
Lemma name_bytes name : Protocol.valid_name name ->
  Forall (fun ch => 0 <= ch < 256 /\ ~ TokenByteExecution.separator ch) name.
Proof.
  intros [_ Hbytes]. eapply Forall_impl; [exact Hbytes|].
  intros ch [Hword [H32 [H9 [H10 H13]]]]. unfold TokenByteExecution.separator. tauto.
Qed.
Lemma token_length s name tail : length (memory (result s name tail) arraydef_0__token) = length (memory s arraydef_0__token).
Proof.
  unfold result,ReadTokenExecution.read_result. rewrite store_meta_other by discriminate.
  change (length (memory (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.reset s) 0 name) 17 1) arraydef_0__token) = length (memory s arraydef_0__token)).
  rewrite store_meta_other by discriminate. now rewrite ReadTokenExecution.put_many_token_length,ReadTokenExecution.reset_token.
Qed.
Theorem token_rep s name tail : (17 < length (memory s arraydef_0__meta))%nat ->
  (length name <= length (memory s arraydef_0__token))%nat -> NameRepresentation.token_rep (result s name tail) name.
Proof.
  intros Hmeta Htoken. split; [now apply ReadTokenExecution.result_count|]. split.
  - now rewrite token_length.
  - intros j Hj. exact (ReadTokenExecution.result_token_entry s name tail j Hj Htoken).
Qed.
Lemma storage s name tail : (17 < length (memory s arraydef_0__meta))%nat -> ArenaFrame.storage s (result s name tail).
Proof.
  intro Hmeta. split; [apply ReadTokenExecution.result_meta_length|]. split.
  - intros array Hm Ht. now apply ReadTokenExecution.result_other.
  - repeat split; apply ReadTokenExecution.result_meta_other; try exact Hmeta; lia.
Qed.
Lemma bindings s name tail bindings : (17 < length (memory s arraydef_0__meta))%nat ->
  NameRepresentation.represents s bindings -> NameRepresentation.represents (result s name tail) bindings.
Proof.
  intros Hmeta [Hcount [Hbytes [Hlimit [Hspan Hentries]]]]. unfold NameRepresentation.represents,result.
  rewrite (ReadTokenExecution.result_other s name tail arraydef_0__names ltac:(discriminate) ltac:(discriminate)),
    (ReadTokenExecution.result_other s name tail arraydef_0__bindings ltac:(discriminate) ltac:(discriminate)).
  rewrite !ReadTokenExecution.result_meta_other by (try exact Hmeta; lia). repeat split; assumption.
Qed.
Lemma classes s name tail fs cs : (17 < length (memory s arraydef_0__meta))%nat ->
  ClassStorage.represents s fs cs -> ClassStorage.represents (result s name tail) fs cs.
Proof.
  intros Hmeta [Hcount Hclasses]. unfold result. split.
  - rewrite ReadTokenExecution.result_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadTokenExecution.result_other by discriminate. exact Hclasses.
Qed.
Lemma history s name tail logical : (17 < length (memory s arraydef_0__meta))%nat ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents (result s name tail) logical.
Proof.
  intros Hmeta [Hcount Hhistory]. unfold result. split.
  - rewrite ReadTokenExecution.result_meta_other by (try exact Hmeta; lia). exact Hcount.
  - rewrite ReadTokenExecution.result_other by discriminate. exact Hhistory.
Qed.
Theorem generated_token s bs ns name sep tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 -> Protocol.valid_name name -> TokenByteExecution.separator sep ->
  stdin s = name ++ sep :: tail ->
  execObserved (funcdef_0__readToken bs ns) (s,observations) = Some (tt,(result s name tail,observations)).
Proof.
  intros Hmeta Htoken Hpending Herror Hvalid Hsep Hin. apply ReadTokenExecution.generated_readToken_observed.
  eapply ReadTokenExecution.generated_readToken_none with (sep := sep); try assumption.
  - exact (proj1 Hvalid).
  - now apply name_bytes.
Qed.
Definition opcode_state s ch chars name sep tail := CommandInput.parsed s ch chars (name ++ sep :: tail).
Definition name_state s ch chars name sep tail := result (opcode_state s ch chars name sep tail) name tail.
Lemma opcode_meta_length s ch chars name sep tail :
  length (memory (opcode_state s ch chars name sep tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. apply CommandInput.parsed_meta_length. Qed.
Lemma name_meta_length s ch chars name sep tail :
  length (memory (name_state s ch chars name sep tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold name_state. now rewrite ReadTokenExecution.result_meta_length,opcode_meta_length. Qed.
Lemma name_other s ch chars name sep tail array : array <> arraydef_0__meta -> array <> arraydef_0__token ->
  memory (name_state s ch chars name sep tail) array = memory s array.
Proof.
  intros Hm Ht. unfold name_state,opcode_state. rewrite ReadTokenExecution.result_other by assumption. now apply CommandInput.parsed_other.
Qed.
Lemma name_meta_other s ch chars name sep tail i : (17 < length (memory s arraydef_0__meta))%nat ->
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (name_state s ch chars name sep tail) i = meta_value s i.
Proof.
  intros Hmeta H6 H11 H14 H15 H17. unfold name_state.
  rewrite ReadTokenExecution.result_meta_other by (try rewrite opcode_meta_length; assumption).
  unfold opcode_state. now apply CommandInput.parsed_meta_other.
Qed.
Theorem generated_reads s opcode ch chars name first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 -> Z.of_nat opcode <= maximum -> decimalBytes opcode = ch :: chars ->
  Protocol.valid_name name -> TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = chars ++ first_separator :: name ++ last_separator :: tail ->
  let op := opcode_state s ch chars name last_separator tail in
  let named := name_state s ch chars name last_separator tail in
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) /\
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(named,observations)) /\
  (17 < length (memory op arraydef_0__meta))%nat /\ meta_value op 11 = Z.of_nat opcode /\
  meta_value op 14 = 1 /\ meta_value op 8 = 0 /\
  (17 < length (memory named arraydef_0__meta))%nat /\ meta_value named 14 = 1 /\ meta_value named 8 = 0 /\
  NameRepresentation.token_rep named name /\ stdin named = tail /\ stdout named = stdout s.
Proof.
  intros Hmeta Htoken Hpending Herror Hcode Hencoding Hvalid Hsep1 Hsep2 Hin.
  set (op := opcode_state s ch chars name last_separator tail).
  set (named := name_state s ch chars name last_separator tail).
  assert (Hopcode : execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations))).
  { exact (CommandInput.generated_pending s (fun _ => false) (fun _ => 0) opcode ch chars first_separator (name ++ last_separator :: tail)
      observations Hmeta Htoken Hpending Herror Hcode Hencoding Hsep1 Hin). }
  assert (Hopmeta : (17 < length (memory op arraydef_0__meta))%nat) by (unfold op; now rewrite opcode_meta_length).
  assert (Hoptoken : (1024 <= length (memory op arraydef_0__token))%nat)
    by (unfold op,opcode_state; now rewrite CommandArgs.pending_token_length).
  assert (Hopnumber : meta_value op 11 = Z.of_nat opcode)
    by exact (CommandInput.parsed_number s opcode ch chars _ Hmeta Hcode Hencoding).
  assert (Hopvalid : meta_value op 14 = 1) by (now apply CommandInput.parsed_valid).
  assert (Hoperror : meta_value op 8 = 0)
    by (unfold op,opcode_state; rewrite CommandInput.parsed_meta_other by lia; exact Herror).
  assert (Hopclear : meta_value op 15 = 0) by (now apply CommandArgs.pending_cleared).
  assert (Hopinput : stdin op = name ++ last_separator :: tail) by reflexivity.
  assert (Hname : execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(named,observations))).
  { exact (generated_token op (fun _ => false) (fun _ => 0) name last_separator tail observations Hopmeta Hoptoken Hopclear Hoperror Hvalid Hsep2 Hopinput). }
  assert (Hnamemeta : (17 < length (memory named arraydef_0__meta))%nat) by (unfold named; now rewrite name_meta_length).
  assert (Hnamevalid : meta_value named 14 = 1) by (now apply ReadTokenExecution.result_valid).
  assert (Hnameerror : meta_value named 8 = 0)
    by (unfold named; rewrite name_meta_other by (try exact Hmeta; lia); exact Herror).
  assert (Hnamerep : NameRepresentation.token_rep named name).
  { assert (Hfit : (length name <= length (memory op arraydef_0__token))%nat) by (pose proof (proj1 Hvalid); lia).
    exact (token_rep op name tail Hopmeta Hfit). }
  assert (Hinput : stdin named = tail) by reflexivity.
  assert (Houtput : stdout named = stdout s).
  { transitivity (stdout op); [apply ReadTokenExecution.result_output|apply CommandInput.parsed_output]. }
  destruct Hnamerep as [Hnamesize [Hnamelength Hnamebytes]]. repeat split; assumption.
Qed.
End ReadName.
