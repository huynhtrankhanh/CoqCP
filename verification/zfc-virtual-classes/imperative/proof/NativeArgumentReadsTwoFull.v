From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadOne ReadTwo DecimalInput CommandInput CommandArgs NativeArgumentReads NativeArgumentReadsTwo.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeArgumentReadsTwoFull.
Import IndexExecution SipHashExecution.
Theorem generated_reads s bs ns opcode ch chars a b first_separator prefix1 middle prefix2 last tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  Z.of_nat opcode <= maximum -> decimalBytes opcode = ch :: chars ->
  Z.of_nat a <= maximum -> Z.of_nat b <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
  Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
  stdin s = chars ++ first_separator :: prefix1 ++ decimalBytes a ++ middle :: prefix2 ++ decimalBytes b ++ last :: tail ->
  let op := CommandInput.parsed s ch chars (prefix1++decimalBytes a++middle::prefix2++decimalBytes b++last::tail) in
  let fstarg := ReadOne.argument_state s ch chars a middle (prefix2++decimalBytes b++last::tail) in
  let sndarg := ReadTwo.second_state s ch chars a middle b last tail in
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(op,observations)) /\
  execObserved (funcdef_0__readNat bs ns) (op,observations) = Some (tt,(fstarg,observations)) /\
  execObserved (funcdef_0__readNat bs ns) (fstarg,observations) = Some (tt,(sndarg,observations)) /\
  (17 < length (memory op arraydef_0__meta))%nat /\ meta_value op 11 = Z.of_nat opcode /\ meta_value op 14 = 1 /\ meta_value op 8 = 0 /\
  (17 < length (memory fstarg arraydef_0__meta))%nat /\ meta_value fstarg 11 = Z.of_nat a /\ meta_value fstarg 14 = 1 /\ meta_value fstarg 8 = 0 /\
  (17 < length (memory sndarg arraydef_0__meta))%nat /\ (20 <= length (memory sndarg arraydef_0__printBuffer))%nat /\
  meta_value sndarg 11 = Z.of_nat b /\ meta_value sndarg 14 = 1 /\ meta_value sndarg 8 = 0 /\ stdin sndarg = tail /\ stdout sndarg = stdout s.
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin.
  pose proof (NativeArgumentReads.generated_reads s bs ns opcode ch chars a first_separator prefix1 middle
    (prefix2++decimalBytes b++last::tail) observations Hmeta Htoken Hbuffer Hpending Herror Hcode Hencoding Ha Hsep1 Hsep2 Hprefix1 Hin) as Hread.
  destruct Hread as [Hopcode [Hfirst [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hfirstmeta [Hfirstbuffer [Hfirstnumber [Hfirstvalid [Hfirsterror [Hfirstinput Hfirstoutput]]]]]]]]]]]].
  destruct(NativeArgumentReadsTwo.generated_reads s bs ns opcode ch chars a b first_separator prefix1 middle prefix2 last tail observations
    Hmeta Htoken Hpending Herror Hcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hin) as [_ [_ Hsecond]].
  set (fstarg := ReadOne.argument_state s ch chars a middle (prefix2++decimalBytes b++last::tail)).
  set (base := ReadTwo.first_state s ch chars a middle b last tail).
  set (sndarg := ReadTwo.second_state s ch chars a middle b last tail).
  assert(HbaseMeta:(17<length(memory base arraydef_0__meta))%nat) by (unfold base;rewrite ReadTwo.first_meta_length;exact Hmeta).
  assert (Hsecondmeta : (17 < length (memory sndarg arraydef_0__meta))%nat) by (unfold sndarg; now rewrite ReadTwo.second_meta_length).
  assert (Hsecondbuffer : (20 <= length (memory sndarg arraydef_0__printBuffer))%nat).
  { unfold sndarg. now rewrite ReadTwo.second_other by discriminate. }
  destruct (DecimalInput.encoded_result_correct base b tail HbaseMeta Hb) as [Hsecondnumber [Hsecondinput Hsecondoutput]].
  assert (Hsecondvalid : meta_value sndarg 14 = 1) by (now apply CommandArgs.encoded_valid).
  assert (Hseconderror : meta_value sndarg 8 = 0).
  { unfold sndarg. rewrite ReadTwo.second_meta_other by (try exact Hmeta; lia). exact Herror. }
  assert (Hinput : stdin sndarg = tail) by exact Hsecondinput.
  assert (Houtput : stdout sndarg = stdout s).
  { transitivity (stdout base); [exact Hsecondoutput|].
    rewrite (NativeArgumentReadsTwo.argument_suffix s ch chars a middle (prefix2++decimalBytes b++last::tail) (decimalBytes b++last::tail)) in Hfirstoutput.
    exact Hfirstoutput. }
  repeat split; assumption.
Qed.
End NativeArgumentReadsTwoFull.
