From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadOne DecimalInput CommandInput CommandArgs ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ReadTwo.
Import IndexExecution SipHashExecution.
Definition opcode_state s ch chars a middle b last tail := ReadOne.opcode_state s ch chars a middle (decimalBytes b ++ last :: tail).
Definition first_state s ch chars a middle b last tail := ReadOne.argument_state s ch chars a middle (decimalBytes b ++ last :: tail).
Definition second_state s ch chars a middle b last tail := DecimalInput.encoded_result (first_state s ch chars a middle b last tail) b tail.
Lemma first_meta_length s ch chars a middle b last tail :
  length (memory (first_state s ch chars a middle b last tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. apply ReadOne.argument_meta_length. Qed.
Lemma second_meta_length s ch chars a middle b last tail :
  length (memory (second_state s ch chars a middle b last tail) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold second_state. now rewrite DecimalInput.encoded_meta_length, first_meta_length. Qed.
Lemma second_other s ch chars a middle b last tail name : name <> arraydef_0__meta -> name <> arraydef_0__token ->
  memory (second_state s ch chars a middle b last tail) name = memory s name.
Proof. intros Hm Ht. unfold second_state, first_state. rewrite DecimalInput.encoded_other by assumption.
  now apply ReadOne.argument_other. Qed.
Lemma second_meta_other s ch chars a middle b last tail i : (17 < length (memory s arraydef_0__meta))%nat ->
  i <> 6%nat -> i <> 11%nat -> i <> 14%nat -> i <> 15%nat -> i <> 17%nat ->
  meta_value (second_state s ch chars a middle b last tail) i = meta_value s i.
Proof.
  intros Hmeta H6 H11 H14 H15 H17. unfold second_state.
  rewrite DecimalInput.encoded_meta_other by (try rewrite first_meta_length; assumption).
  unfold first_state. now apply ReadOne.argument_meta_other.
Qed.
Lemma second_storage s ch chars a middle b last tail : (17 < length (memory s arraydef_0__meta))%nat ->
  ArenaFrame.storage s (second_state s ch chars a middle b last tail).
Proof.
  intro Hmeta. refine (ArenaFrame.storage_trans s (first_state s ch chars a middle b last tail) _
    (ReadOne.argument_storage s ch chars a middle _ Hmeta) _).
  apply CommandArgs.encoded_storage. now rewrite first_meta_length.
Qed.
Theorem generated_reads s bs ns opcode ch chars a b first_separator middle last tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat opcode <= maximum -> decimalBytes opcode = ch :: chars ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  stdin s = chars ++ first_separator :: decimalBytes a ++ middle :: decimalBytes b ++ last :: tail ->
  let op := opcode_state s ch chars a middle b last tail in
  let fstarg := first_state s ch chars a middle b last tail in
  let sndarg := second_state s ch chars a middle b last tail in
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(op,observations)) /\
  execObserved (funcdef_0__readNat bs ns) (op,observations) = Some (tt,(fstarg,observations)) /\
  execObserved (funcdef_0__readNat bs ns) (fstarg,observations) = Some (tt,(sndarg,observations)) /\
  (17 < length (memory op arraydef_0__meta))%nat /\ meta_value op 11 = Z.of_nat opcode /\ meta_value op 14 = 1 /\ meta_value op 8 = 0 /\
  (17 < length (memory fstarg arraydef_0__meta))%nat /\ meta_value fstarg 11 = Z.of_nat a /\ meta_value fstarg 14 = 1 /\ meta_value fstarg 8 = 0 /\
  (17 < length (memory sndarg arraydef_0__meta))%nat /\ (20 <= length (memory sndarg arraydef_0__printBuffer))%nat /\
  meta_value sndarg 11 = Z.of_nat b /\ meta_value sndarg 14 = 1 /\ meta_value sndarg 8 = 0 /\ stdin sndarg = tail /\ stdout sndarg = stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hin.
  pose proof (ReadOne.generated_reads s bs ns opcode ch chars a first_separator middle (decimalBytes b ++ last :: tail) observations
    Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hfirst [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstbuffer [Hfirstnumber [Hfirstvalid [Hfirsterror [Hfirstinput Hfirstoutput]]]]]]]]]]]].
  set (fstarg := first_state s ch chars a middle b last tail).
  set (sndarg := second_state s ch chars a middle b last tail).
  assert (Hfirsttoken : (1024 <= length (memory fstarg arraydef_0__token))%nat).
  { unfold fstarg, first_state, ReadOne.argument_state, ReadOne.opcode_state.
    now rewrite DecimalInput.encoded_token_length, CommandArgs.pending_token_length. }
  assert (Hfirstclear : meta_value fstarg 15 = 0).
  { unfold fstarg, first_state, ReadOne.argument_state.
    rewrite DecimalInput.encoded_meta_other by (try rewrite ReadOne.opcode_meta_length; try exact Hmeta; lia).
    now apply CommandArgs.pending_cleared. }
  assert (Hsecond : execObserved (funcdef_0__readNat bs ns) (fstarg,observations) = Some (tt,(sndarg,observations))).
  { exact (DecimalInput.generated_readNat_encoded_observed fstarg bs ns b last tail observations
      Hfirstmeta Hfirsttoken Hfirstclear Hfirsterror Hb Hsep3 Hfirstinput). }
  assert (Hsecondmeta : (17 < length (memory sndarg arraydef_0__meta))%nat) by (unfold sndarg; now rewrite second_meta_length).
  assert (Hsecondbuffer : (20 <= length (memory sndarg arraydef_0__printBuffer))%nat).
  { unfold sndarg. now rewrite second_other by discriminate. }
  destruct (DecimalInput.encoded_result_correct fstarg b tail Hfirstmeta Hb) as [Hsecondnumber [Hsecondinput Hsecondoutput]].
  assert (Hsecondvalid : meta_value sndarg 14 = 1) by (now apply CommandArgs.encoded_valid).
  assert (Hseconderror : meta_value sndarg 8 = 0).
  { unfold sndarg. rewrite second_meta_other by (try exact Hmeta; lia). exact Herror. }
  assert (Hinput : stdin sndarg = tail) by exact Hsecondinput.
  assert (Houtput : stdout sndarg = stdout s).
  { transitivity (stdout fstarg); [exact Hsecondoutput|exact Hfirstoutput]. }
  repeat split; assumption.
Qed.
End ReadTwo.
