From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadOne ClassStorage ClassAbstract ReplyNO ArenaFrame Representation.
From NativeProof Require Import NativeArgumentReads ClassAbstractInput.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceClassAbstractInput.
Import IndexExecution SipHashExecution ClassAbstractInput.
Theorem generated_pending s bs ns n value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 -> meta_value s 2 = Z.of_nat n ->
  Z.of_nat n < maximum -> Z.of_nat value <= maximum -> Z.of_nat value < meta_value s 1 ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(result s n value last_separator tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcount Hword Hvalue Hreference Hsep1 Hsep2 Hspaces Hin.
  assert (Hsix : Z.of_nat 6 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 6 54 [] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hsix eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  assert (Hargreference : Z.of_nat value < meta_value (argument_state s value last_separator tail) 1).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hreference. }
  assert (Hargcount : meta_value (argument_state s value last_separator tail) 2 = Z.of_nat n).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount. }
  pose proof (ClassAbstractExecution.generated_command s bs ns _ _ n (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargbuffer Hargnumber Hargvalid Hargerror Hargreference Hargcount Hword) as Hrun.
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
Theorem generated_rejected s bs ns value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> meta_value s 1 <= Z.of_nat value ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(rejected s value last_separator tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hspaces Hin.
  assert (Hsix : Z.of_nat 6 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 6 54 [] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hsix eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  assert (Hargreference : meta_value (argument_state s value last_separator tail) 1 <= Z.of_nat value).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hreference. }
  pose proof (ClassAbstractExecution.generated_rejected_command s bs ns _ _ (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hargreference) as Hrun.
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
End NativeWhitespaceClassAbstractInput.
