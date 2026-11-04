From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput NativeGeneralPrefixStop NativeSpacedFirstArgumentStop NativeByteErrorNumericReader NativeMalformedSecondArgumentHandlers NativeSecondByteModelErrorCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSecondByteModelErrorStop.
Import IndexExecution SipHashExecution.
Theorem generated opcode ch chars leading sep0 first_input value input ended tail :
 NativeMalformedSecondArgumentHandlers.supported (Z.of_nat opcode) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 ->
 ByteProtocol.byte_stream first_input -> ByteProtocol.byte_stream input ->
 ByteProtocol.read_number first_input=ByteProtocol.number_token value input ended ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(ch::chars)++sep0::first_input) tail.
Proof.
 intros Hsupported Hword Hencoding Hleading Hsep0 Hbytes Hbytes2 Hfirst Hbad.
 pose proof(DecimalInput.decimal_word opcode Hword) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;exact Hword|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeSecondByteModelErrorCommand.generated s (fun _=>false)(fun _=>0) opcode ch chars sep0 first_input value input ended tail observations
 Hsupported Hword Hencoding Hmeta Htoken Hpending Herror Hsep0 Hinput Hbytes Hbytes2 Hfirst Hbad).
Qed.
End NativeSecondByteModelErrorStop.
