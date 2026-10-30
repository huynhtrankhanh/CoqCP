From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte DecimalInput CommandInput CommandArgs ClassStorage ClassSet ArenaFrame FormulaProjection Representation.
From NativeProof Require Import NativeArgumentReads ClassSetInput.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module NativeWhitespaceClassSetInput.
Import IndexExecution SipHashExecution ClassSetInput.
Theorem generated_pending s bs ns n value first_separator spaces last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 54 -> meta_value s 8 = 0 -> meta_value s 2 = Z.of_nat n ->
  Z.of_nat n < maximum -> Z.of_nat value <= maximum ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator spaces ->
  stdin s = first_separator :: spaces ++ decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) =
    Some (tt,(result s n value last_separator tail,
      observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcount Hword Hvalue Hsep1 Hsep2 Hspaces Hin.
  assert (Hfive : Z.of_nat 5 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (NativeArgumentReads.generated_reads s (fun _ => false) (fun _ => 0) 5 53 [] value first_separator spaces last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hfive eq_refl Hvalue Hsep1 Hsep2 Hspaces Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  set (arg := argument_state s value last_separator tail).
  assert (Hargcount : meta_value arg 2 = Z.of_nat n).
  { unfold arg. rewrite argument_meta_other by (try exact Hmeta; lia). exact Hcount. }
  pose proof (ClassSetExecution.generated_command s bs ns _ arg n (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargbuffer Hargnumber Hargvalid Hargerror Hargcount Hword) as Hrun.
  change (stdin arg=tail) in Hinput. change (stdout arg=stdout s) in Houtput.
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
End NativeWhitespaceClassSetInput.
