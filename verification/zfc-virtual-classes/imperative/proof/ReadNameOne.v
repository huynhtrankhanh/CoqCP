From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken DecimalInput CommandArgs ReadOne ReadName NameRepresentation ParsedState ClassStorage HistoryRefinement ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module ReadNameOne.
Import IndexExecution SipHashExecution.
Definition opcode_state s ch chars value middle name last tail := ReadOne.opcode_state s ch chars value middle (name ++ last :: tail).
Definition argument_state s ch chars value middle name last tail := ReadOne.argument_state s ch chars value middle (name ++ last :: tail).
Definition name_state s ch chars value middle name last tail := ReadName.result (argument_state s ch chars value middle name last tail) name tail.
Lemma argument_bindings s ch chars value middle suffix bs : (17 < length (memory s arraydef_0__meta))%nat ->
  NameRepresentation.represents s bs -> NameRepresentation.represents (ReadOne.argument_state s ch chars value middle suffix) bs.
Proof.
  intros Hmeta [Hcount [Hbytes [Hlimit [Hspan Hentries]]]]. unfold NameRepresentation.represents.
  rewrite (ReadOne.argument_other s ch chars value middle suffix arraydef_0__names ltac:(discriminate) ltac:(discriminate)),
    (ReadOne.argument_other s ch chars value middle suffix arraydef_0__bindings ltac:(discriminate) ltac:(discriminate)).
  rewrite !ReadOne.argument_meta_other by (try exact Hmeta; lia). repeat split; assumption.
Qed.
Lemma name_bindings s ch chars value middle name last tail bs : (17 < length (memory s arraydef_0__meta))%nat ->
  NameRepresentation.represents s bs -> NameRepresentation.represents (name_state s ch chars value middle name last tail) bs.
Proof.
  intros Hmeta Hrep. unfold name_state. apply ReadName.bindings.
  - unfold argument_state. rewrite ReadOne.argument_meta_length. exact Hmeta.
  - now apply argument_bindings.
Qed.
Lemma name_storage s ch chars value middle name last tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (name_state s ch chars value middle name last tail).
Proof.
  intro Hmeta. unfold name_state. eapply ArenaFrame.storage_trans; [apply ReadOne.argument_storage; exact Hmeta|].
  apply ReadName.storage. unfold argument_state. now rewrite ReadOne.argument_meta_length.
Qed.
Lemma name_classes s ch chars value middle name last tail fs cs : (17 < length (memory s arraydef_0__meta))%nat ->
  ClassStorage.represents s fs cs -> ClassStorage.represents (name_state s ch chars value middle name last tail) fs cs.
Proof.
  intros Hmeta Hrep. unfold name_state. apply ReadName.classes.
  - unfold argument_state. rewrite ReadOne.argument_meta_length. exact Hmeta.
  - exact (ParsedState.one_classes s fs cs ch chars value middle _ Hmeta Hrep).
Qed.
Lemma name_history s ch chars value middle name last tail logical : (17 < length (memory s arraydef_0__meta))%nat ->
  HistoryRefinement.represents s logical -> HistoryRefinement.represents (name_state s ch chars value middle name last tail) logical.
Proof.
  intros Hmeta Hrep. unfold name_state. apply ReadName.history.
  - unfold argument_state. rewrite ReadOne.argument_meta_length. exact Hmeta.
  - exact (ParsedState.one_history s logical ch chars value middle _ Hmeta Hrep).
Qed.
Lemma name_other s ch chars value middle name last tail array : array <> arraydef_0__meta -> array <> arraydef_0__token ->
  memory (name_state s ch chars value middle name last tail) array = memory s array.
Proof.
  intros Hm Ht. unfold name_state,ReadName.result. rewrite ReadTokenExecution.result_other by assumption.
  now apply ReadOne.argument_other.
Qed.
Theorem generated_reads s opcode ch chars value name first_separator middle_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat -> (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat -> meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat opcode <= maximum -> decimalBytes opcode = ch :: chars -> Z.of_nat value <= maximum -> Protocol.valid_name name ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle_separator -> TokenByteExecution.separator last_separator ->
  stdin s = chars ++ first_separator :: decimalBytes value ++ middle_separator :: name ++ last_separator :: tail ->
  let op := opcode_state s ch chars value middle_separator name last_separator tail in
  let arg := argument_state s ch chars value middle_separator name last_separator tail in
  let named := name_state s ch chars value middle_separator name last_separator tail in
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(op,observations)) /\
  execObserved (funcdef_0__readNat (fun _ => false) (fun _ => 0)) (op,observations) = Some (tt,(arg,observations)) /\
  execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)) /\
  (17 < length (memory op arraydef_0__meta))%nat /\ meta_value op 11 = Z.of_nat opcode /\ meta_value op 14 = 1 /\ meta_value op 8 = 0 /\
  (17 < length (memory arg arraydef_0__meta))%nat /\ meta_value arg 11 = Z.of_nat value /\ meta_value arg 14 = 1 /\ meta_value arg 8 = 0 /\
  (17 < length (memory named arraydef_0__meta))%nat /\ meta_value named 14 = 1 /\ meta_value named 8 = 0 /\
  NameRepresentation.token_rep named name /\ stdin named = tail /\ stdout named = stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Hvalue Hvalid Hsep1 Hsep2 Hsep3 Hin.
  destruct (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) opcode ch chars value first_separator middle_separator
    (name ++ last_separator :: tail) observations Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Hvalue Hsep1 Hsep2 Hin)
    as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Harginput Hargoutput]]]]]]]]]]]].
  set (op := opcode_state s ch chars value middle_separator name last_separator tail).
  set (arg := argument_state s ch chars value middle_separator name last_separator tail).
  set (named := name_state s ch chars value middle_separator name last_separator tail).
  change (17 < length (memory op arraydef_0__meta))%nat in Hopmeta.
  change (17 < length (memory arg arraydef_0__meta))%nat in Hargmeta.
  assert (Hargtoken : (1024 <= length (memory arg arraydef_0__token))%nat).
  { unfold arg,argument_state,ReadOne.argument_state,ReadOne.opcode_state.
    now rewrite DecimalInput.encoded_token_length,CommandArgs.pending_token_length. }
  assert (Hargclear : meta_value arg 15 = 0).
  { unfold arg,argument_state,ReadOne.argument_state. rewrite DecimalInput.encoded_meta_other by (try rewrite ReadOne.opcode_meta_length; try exact Hmeta; lia).
    apply CommandArgs.pending_cleared. exact Hmeta. }
  assert (Hname : execObserved (funcdef_0__readToken (fun _ => false) (fun _ => 0)) (arg,observations) = Some (tt,(named,observations)))
    by exact (ReadName.generated_token arg (fun _ => false) (fun _ => 0) name last_separator tail observations Hargmeta Hargtoken Hargclear Hargerror Hvalid Hsep3 Harginput).
  assert (Hnamemeta : (17 < length (memory named arraydef_0__meta))%nat).
  { change (17 < length (memory (ReadName.result arg name tail) arraydef_0__meta))%nat.
    rewrite ReadTokenExecution.result_meta_length. exact Hargmeta. }
  assert (Hnamevalid : meta_value named 14 = 1) by exact (ReadTokenExecution.result_valid arg name tail Hargmeta).
  assert (Hnameerror : meta_value named 8 = 0).
  { change (meta_value (ReadTokenExecution.read_result arg name tail) 8 = 0).
    rewrite ReadTokenExecution.result_meta_other by (try exact Hargmeta; lia). exact Hargerror. }
  assert (Hnamerep : NameRepresentation.token_rep named name).
  { assert (Hfit : (length name <= length (memory arg arraydef_0__token))%nat) by (pose proof (proj1 Hvalid); lia).
    exact (ReadName.token_rep arg name tail Hargmeta Hfit). }
  assert (Hinput : stdin named = tail) by reflexivity.
  assert (Houtput : stdout named = stdout s).
  { transitivity (stdout arg); [apply ReadTokenExecution.result_output|exact Hargoutput]. }
  destruct Hnamerep as [Hnamesize [Hnamelength Hnamebytes]]. repeat split; assumption.
Qed.
End ReadNameOne.
