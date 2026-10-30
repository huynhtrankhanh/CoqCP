From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat DecimalInput CommandInput CommandArgs ReadOne ReadTwo SeedSeparator NativeArgumentWhitespace NativeArgumentReads.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeArgumentReadsTwo.
Import IndexExecution SipHashExecution.
Lemma encoded_suffix native value tail1 tail2 :
 DecimalInput.encoded_result native value tail1 = withInput (DecimalInput.encoded_result native value tail2) tail1.
Proof.
 unfold DecimalInput.encoded_result,ReadNatExecution.token_number,ReadTokenExecution.read_result.
 rewrite SeedSeparator.store_input. reflexivity.
Qed.
Lemma argument_suffix s ch chars value sep tail1 tail2 :
 ReadOne.argument_state s ch chars value sep tail1 = withInput (ReadOne.argument_state s ch chars value sep tail2) tail1.
Proof.
 unfold ReadOne.argument_state,ReadOne.opcode_state.
 rewrite (NativeArgumentWhitespace.parsed_suffix s ch chars (decimalBytes value++sep::tail1) (decimalBytes value++sep::tail2)).
 rewrite NativeArgumentWhitespace.encoded_result_input. apply encoded_suffix.
Qed.
Theorem generated_reads s bs ns opcode ch chars a b first_separator prefix1 middle prefix2 last tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
 Z.of_nat a<=maximum -> Z.of_nat b<=maximum -> TokenByteExecution.separator first_separator ->
 TokenByteExecution.separator middle -> TokenByteExecution.separator last ->
 Forall TokenByteExecution.separator prefix1 -> Forall TokenByteExecution.separator prefix2 ->
 stdin s=chars++first_separator::prefix1++decimalBytes a++middle::prefix2++decimalBytes b++last::tail ->
 let op:=CommandInput.parsed s ch chars (prefix1++decimalBytes a++middle::prefix2++decimalBytes b++last::tail) in
 let first:=ReadOne.argument_state s ch chars a middle (prefix2++decimalBytes b++last::tail) in
 let final:=ReadTwo.second_state s ch chars a middle b last tail in
 execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(op,observations)) /\
 execObserved(funcdef_0__readNat bs ns)(op,observations)=Some(tt,(first,observations)) /\
 execObserved(funcdef_0__readNat bs ns)(first,observations)=Some(tt,(final,observations)).
Proof.
 intros Hmeta Htoken Hpending Herror Hopcode Hencoding Ha Hb Hsep1 Hsep2 Hsep3 Hprefix1 Hprefix2 Hinput. cbn zeta.
 destruct(NativeArgumentWhitespace.generated_opcode_and_argument s bs ns opcode ch chars a first_separator prefix1 middle
  (prefix2++decimalBytes b++last::tail) observations Hmeta Htoken Hpending Herror Hopcode Hencoding Ha Hsep1 Hsep2 Hprefix1 Hinput) as [Hop Hfirst].
 split;[exact Hop|]. split;[exact Hfirst|].
 set(base:=ReadTwo.first_state s ch chars a middle b last tail).
 assert(Hmeta':(17<length(memory base arraydef_0__meta))%nat) by (unfold base;rewrite ReadTwo.first_meta_length;exact Hmeta).
 assert(Htoken':(1024<=length(memory base arraydef_0__token))%nat).
 { unfold base,ReadTwo.first_state,ReadOne.argument_state,ReadOne.opcode_state. rewrite DecimalInput.encoded_token_length,CommandArgs.pending_token_length. exact Htoken. }
 assert(Hpending':meta_value base 15=0).
 { unfold base,ReadTwo.first_state,ReadOne.argument_state. rewrite DecimalInput.encoded_meta_other by (try rewrite ReadOne.opcode_meta_length;try exact Hmeta;lia).
   unfold ReadOne.opcode_state. apply CommandArgs.pending_cleared;lia. }
 assert(Herror':meta_value base 8=0).
 { unfold base,ReadTwo.first_state. rewrite ReadOne.argument_meta_other by (try exact Hmeta;lia). exact Herror. }
 rewrite(argument_suffix s ch chars a middle (prefix2++decimalBytes b++last::tail) (decimalBytes b++last::tail)). fold base.
 exact(NativeArgumentWhitespace.read base bs ns b prefix2 last tail observations Hmeta' Htoken' Hpending' Herror' Hb Hsep3 Hprefix2).
Qed.
End NativeArgumentReadsTwo.
