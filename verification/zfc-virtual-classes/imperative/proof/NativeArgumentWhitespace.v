From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadNatLeading DecimalInput SeedSeparator ObservedLocal CommandQuit CommandInput CommandArgs ReadOne.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeArgumentWhitespace.
Import IndexExecution SipHashExecution.
Lemma encoded_result_input native input value tail :
 DecimalInput.encoded_result (withInput native input) value tail = DecimalInput.encoded_result native value tail.
Proof.
 unfold DecimalInput.encoded_result. now rewrite SeedSeparator.read_result_input.
Qed.
Theorem read native bs ns value prefix sep tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix ->
 execObserved(funcdef_0__readNat bs ns)(withInput native(prefix++decimalBytes value++sep::tail),observations)=
 Some(tt,(DecimalInput.encoded_result native value tail,observations)).
Proof.
 intros Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix.
 pose proof(ReadNatLeading.generated_encoded (withInput native(prefix++decimalBytes value++sep::tail)) bs ns value prefix sep tail
  Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix eq_refl) as Hrun.
 pose proof(ReadNatExecution.generated_readNat_observed _ _ _ _ observations Hrun) as Hobserved.
 now rewrite encoded_result_input in Hobserved.
Qed.
Theorem read_and_continue native bs ns value prefix sep tail observations
 (next:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix ->
 execObserved(funcdef_0__readNat bs ns >>= fun _=>next)
   (withInput native(prefix++decimalBytes value++sep::tail),observations)=
 execObserved next (DecimalInput.encoded_result native value tail,observations).
Proof.
 intros Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix.
 rewrite execObserved_bind, (read native bs ns value prefix sep tail observations Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix).
 reflexivity.
Qed.
Theorem interchangeable native bs ns value prefix1 prefix2 sep1 sep2 tail observations
 (next:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator sep1 -> TokenByteExecution.separator sep2 ->
 Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
 execObserved(funcdef_0__readNat bs ns >>= fun _=>next)
   (withInput native(prefix1++decimalBytes value++sep1::tail),observations)=
 execObserved(funcdef_0__readNat bs ns >>= fun _=>next)
   (withInput native(prefix2++decimalBytes value++sep2::tail),observations).
Proof.
 intros Hmeta Htoken Hpending Herror Hvalue Hsep1 Hsep2 Hprefix1 Hprefix2.
 rewrite (read_and_continue native bs ns value prefix1 sep1 tail observations next Hmeta Htoken Hpending Herror Hvalue Hsep1 Hprefix1).
 rewrite (read_and_continue native bs ns value prefix2 sep2 tail observations next Hmeta Htoken Hpending Herror Hvalue Hsep2 Hprefix2). reflexivity.
Qed.
Theorem local_read_and_continue (f:CommandQuitExecution.Frame) bs ns value prefix sep tail observations
 (next:CommandQuitExecution.LocalAction unit) :
 (17<length(memory (machine f) arraydef_0__meta))%nat -> (1024<=length(memory (machine f) arraydef_0__token))%nat ->
 meta_value (machine f) 15=0 -> meta_value (machine f) 8=0 -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator sep -> Forall TokenByteExecution.separator prefix ->
 ObservedLocal.execLocalObserved
   (liftToWithLocalVariables(funcdef_0__readNat bs ns) >>= fun _=>next)
   (setMachine f (withInput (machine f)(prefix++decimalBytes value++sep::tail)),observations)=
 ObservedLocal.execLocalObserved next (setMachine f (DecimalInput.encoded_result (machine f) value tail),observations).
Proof.
 intros Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix.
 rewrite ObservedLocal.local_bind,ObservedLocal.lift_correct.
 cbn [machine setMachine]. rewrite (read (machine f) bs ns value prefix sep tail observations Hmeta Htoken Hpending Herror Hvalue Hsep Hprefix).
 destruct f. reflexivity.
Qed.
Lemma parsed_suffix native ch chars suffix1 suffix2 :
 CommandInput.parsed native ch chars suffix1 = withInput (CommandInput.parsed native ch chars suffix2) suffix1.
Proof.
 unfold CommandInput.parsed,ReadNatExecution.token_number,ReadTokenExecution.pending_result.
 repeat rewrite SeedSeparator.store_input. reflexivity.
Qed.
Theorem generated_opcode_and_argument native bs ns opcode ch chars value first_separator prefix last_separator tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 ->
 Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars -> Z.of_nat value<=maximum ->
 TokenByteExecution.separator first_separator -> TokenByteExecution.separator last_separator -> Forall TokenByteExecution.separator prefix ->
 stdin native=chars++first_separator::prefix++decimalBytes value++last_separator::tail ->
 let op:=CommandInput.parsed native ch chars (prefix++decimalBytes value++last_separator::tail) in
 let canonical:=ReadOne.argument_state native ch chars value last_separator tail in
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(op,observations)) /\
 execObserved(funcdef_0__readNat bs ns)(op,observations)=Some(tt,(canonical,observations)).
Proof.
 intros Hmeta Htoken Hpending Herror Hopcode Hencoding Hvalue Hsep1 Hsep2 Hprefix Hinput. cbn zeta.
 set(op:=CommandInput.parsed native ch chars (prefix++decimalBytes value++last_separator::tail)).
 split.
 - exact(CommandInput.generated_pending native bs ns opcode ch chars first_separator
     (prefix++decimalBytes value++last_separator::tail) observations Hmeta Htoken Hpending Herror Hopcode Hencoding Hsep1 Hinput).
 - set(base:=ReadOne.opcode_state native ch chars value last_separator tail).
   assert(Hmeta':(17<length(memory base arraydef_0__meta))%nat) by (unfold base;rewrite ReadOne.opcode_meta_length;exact Hmeta).
   assert(Htoken':(1024<=length(memory base arraydef_0__token))%nat) by (unfold base,ReadOne.opcode_state;rewrite CommandArgs.pending_token_length;exact Htoken).
   assert(Hpending':meta_value base 15=0) by (unfold base,ReadOne.opcode_state;apply CommandArgs.pending_cleared;lia).
   assert(Herror':meta_value base 8=0) by (unfold base,ReadOne.opcode_state;rewrite CommandInput.parsed_meta_other by lia;exact Herror).
   unfold op. rewrite(parsed_suffix native ch chars _ (decimalBytes value++last_separator::tail)). fold base.
   exact(read base bs ns value prefix last_separator tail observations Hmeta' Htoken' Hpending' Herror' Hvalue Hsep2 Hprefix).
Qed.
End NativeArgumentWhitespace.
