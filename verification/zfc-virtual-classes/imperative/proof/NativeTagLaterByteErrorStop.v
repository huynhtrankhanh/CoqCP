From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput NativeGeneralPrefixStop NativeSpacedFirstArgumentStop NativeByteErrorNumericReader NativeTagLaterByteErrorCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTagLaterByteErrorStop.
Import IndexExecution SipHashExecution.
Theorem generated_11_2 digit digits leading sep0 value1 space1 sep1 input tail :
 decimalBytes 11=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input)) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 11 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_11_2 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hinput Hbytes Hbad).
Qed.
Theorem generated_11_3 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 input tail :
 decimalBytes 11=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 11 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_11_3 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 value2 space2 sep2 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hinput Hbytes Hbad).
Qed.
Theorem generated_11_4 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail :
 decimalBytes 11=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 11 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_11_4 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hinput Hbytes Hbad).
Qed.
Theorem generated_22_2 digit digits leading sep0 value1 space1 sep1 input tail :
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::input)) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 22 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_22_2 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hinput Hbytes Hbad).
Qed.
Theorem generated_22_3 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 input tail :
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::input))) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 22 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_22_3 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 value2 space2 sep2 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hinput Hbytes Hbad).
Qed.
Theorem generated_22_4 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail :
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::input)))) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 22 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_22_4 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hinput Hbytes Hbad).
Qed.
Theorem generated_22_5 digit digits leading sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 value4 space4 sep4 input tail :
 decimalBytes 22=digit::digits -> Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 Z.of_nat value1<=maximum -> Forall TokenByteExecution.separator space1 -> TokenByteExecution.separator sep1 ->
 Z.of_nat value2<=maximum -> Forall TokenByteExecution.separator space2 -> TokenByteExecution.separator sep2 ->
 Z.of_nat value3<=maximum -> Forall TokenByteExecution.separator space3 -> TokenByteExecution.separator sep3 ->
 Z.of_nat value4<=maximum -> Forall TokenByteExecution.separator space4 -> TokenByteExecution.separator sep4 ->
 ByteProtocol.byte_stream input -> NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++sep0::(space1++decimalBytes value1++sep1::(space2++decimalBytes value2++sep2::(space3++decimalBytes value3++sep3::(space4++decimalBytes value4++sep4::input))))) tail.
Proof.
 intros Hencoding Hleading Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hvalue4 Hspace4 Hsep4 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word 22 ltac:(unfold maximum;lia)) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;unfold maximum;lia|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeTagLaterByteErrorCommand.generated_22_5 s (fun _=>false)(fun _=>0) digit digits sep0 value1 space1 sep1 value2 space2 sep2 value3 space3 sep3 value4 space4 sep4 input tail observations
 Hencoding Hmeta Htoken Hpending Herror Hsep0 Hvalue1 Hspace1 Hsep1 Hvalue2 Hspace2 Hsep2 Hvalue3 Hspace3 Hsep3 Hvalue4 Hspace4 Hsep4 Hinput Hbytes Hbad).
Qed.
End NativeTagLaterByteErrorStop.
