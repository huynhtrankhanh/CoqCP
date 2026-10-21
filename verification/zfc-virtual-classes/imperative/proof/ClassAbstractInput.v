From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory VirtualClasses Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadOne ClassStorage ClassAbstract ReplyNO ArenaFrame Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module ClassAbstractInput.
Import IndexExecution SipHashExecution.
Definition argument_state s value sep tail := ReadOne.argument_state s 54 [] value sep tail.
Definition result s n value sep tail := ClassStorage.result (argument_state s value sep tail) n (1%Z,Z.of_nat value).
Definition rejected s value sep tail := ReplyNOExecution.reply_state (argument_state s value sep tail).
Theorem generated_pending s bs ns n value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 -> meta_value s 2 = Z.of_nat n ->
  Z.of_nat n < maximum -> Z.of_nat value <= maximum -> Z.of_nat value < meta_value s 1 ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(result s n value last_separator tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes (Protocol.OK n); unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hcount Hword Hvalue Hreference Hsep1 Hsep2 Hin.
  assert (Hsix : Z.of_nat 6 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 6 54 [] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hsix eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  assert (Hargreference : Z.of_nat value < meta_value (argument_state s value last_separator tail) 1).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hreference. }
  assert (Hargcount : meta_value (argument_state s value last_separator tail) 2 = Z.of_nat n).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount. }
  pose proof (ClassAbstractExecution.generated_command s bs ns _ _ n (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargbuffer Hargnumber Hargvalid Hargerror Hargreference Hargcount Hword) as Hrun.
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
Theorem generated_rejected s bs ns value first_separator last_separator tail observations :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  (20 <= length (memory s arraydef_0__printBuffer))%nat ->
  meta_value s 15 = 55 -> meta_value s 8 = 0 ->
  Z.of_nat value <= maximum -> meta_value s 1 <= Z.of_nat value ->
  TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator ->
  stdin s = first_separator :: decimalBytes value ++ last_separator :: tail ->
  execObserved (funcdef_0__command bs ns) (s,observations) = Some (tt,(rejected s value last_separator tail,
    observations ++ [{|flushedOutput := stdout s ++ Protocol.reply_bytes Protocol.NO; unreadInput := tail|}])).
Proof.
  intros Hmeta Htoken Hbuffer Hpending Herror Hvalue Hreference Hsep1 Hsep2 Hin.
  assert (Hsix : Z.of_nat 6 <= maximum) by (unfold maximum; cbn; lia).
  pose proof (ReadOne.generated_reads s (fun _ => false) (fun _ => 0) 6 54 [] value first_separator last_separator tail observations
    Hmeta Htoken Hbuffer Hpending Herror Hsix eq_refl Hvalue Hsep1 Hsep2 Hin) as Hread.
  destruct Hread as [Hopcode [Hargument [Hopmeta [Hopnumber [Hopvalid [Hoperror [Hargmeta [Hargbuffer [Hargnumber [Hargvalid [Hargerror [Hinput Houtput]]]]]]]]]]]].
  assert (Hargreference : meta_value (argument_state s value last_separator tail) 1 <= Z.of_nat value).
  { unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hreference. }
  pose proof (ClassAbstractExecution.generated_rejected_command s bs ns _ _ (Z.of_nat value) observations
    Hopcode Hopmeta Hopnumber Hopvalid Hoperror Hargument Hargmeta Hargnumber Hargvalid Hargerror Hargreference) as Hrun.
  rewrite Hinput, Houtput in Hrun. exact Hrun.
Qed.
Lemma argument_represents s meaning classes value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s meaning classes ->
  ClassStorage.represents (argument_state s value sep tail) meaning classes.
Proof.
  intros Hmeta [Hcount Hclasses]. split.
  - unfold argument_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta; lia). exact Hcount.
  - unfold argument_state. rewrite ReadOne.argument_other by discriminate. exact Hclasses.
Qed.
Lemma result_represents s meaning classes value p sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s meaning classes -> nth_error meaning value = Some p ->
  ClassStorage.represents (result s (length classes) value sep tail) meaning (classes ++ [VirtualClasses.abstract (VirtualClasses.core p)]).
Proof.
  intros Hmeta Hclasses Hlookup. unfold result. apply ClassStorage.append_represents.
  - unfold argument_state. rewrite ReadOne.argument_meta_length. lia.
  - now apply argument_represents.
  - change (option_map (fun f => VirtualClasses.abstract (VirtualClasses.core f))
      (nth_error meaning (Z.to_nat (Z.of_nat value))) = Some (VirtualClasses.abstract (VirtualClasses.core p))).
    now rewrite Nat2Z.id, Hlookup.
Qed.
Lemma result_arena s meaning n value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (result s n value sep tail) meaning.
Proof.
  intros Hmeta Harena. unfold result. apply ClassStorage.result_arena.
  exact (ArenaFrame.storage_arena s (argument_state s value sep tail) meaning (ReadOne.argument_storage s 54 [] value sep tail Hmeta) Harena).
Qed.
Lemma rejected_represents s meaning classes value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> ClassStorage.represents s meaning classes ->
  ClassStorage.represents (rejected s value sep tail) meaning classes.
Proof. exact (argument_represents s meaning classes value sep tail). Qed.
Lemma rejected_arena s meaning value sep tail :
  (17 < length (memory s arraydef_0__meta))%nat -> NativeRepresentation.canonical_arena s meaning ->
  NativeRepresentation.canonical_arena (rejected s value sep tail) meaning.
Proof.
  intros Hmeta Harena. apply (ArenaFrame.storage_arena s (rejected s value sep tail) meaning); [|exact Harena].
  exact (ArenaFrame.storage_trans s (argument_state s value sep tail) _
    (ReadOne.argument_storage s 54 [] value sep tail Hmeta) (ArenaFrame.storage_output _ _)).
Qed.
End ClassAbstractInput.
