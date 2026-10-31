From CoqCP Require Import Options DecimalEncoding Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput NativeGeneralPrefixStop NativeSpacedBufferedArgumentStop NativeByteErrorNumericReader NativeMalformedSecondArgumentHandlers NativeSecondArgumentByteErrorCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeSecondArgumentByteErrorStop.
Import IndexExecution SipHashExecution.
Theorem generated opcode ch chars leading sep0 spaces value sep1 input tail :
 NativeMalformedSecondArgumentHandlers.supported (Z.of_nat opcode) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=ch::chars ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator sep0 -> Forall TokenByteExecution.separator spaces ->
 Z.of_nat value<=maximum -> TokenByteExecution.separator sep1 -> ByteProtocol.byte_stream input ->
 NativeByteErrorNumericReader.error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec (leading++(ch::chars)++sep0::spaces++decimalBytes value++sep1::input) tail.
Proof.
 intros Hsupported Hword Hencoding Hleading Hsep0 Hspaces Hvalue Hsep1 Hbytes Hbad.
 pose proof(DecimalInput.decimal_word opcode Hword) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedBufferedArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;exact Hword|exact Hleading|exact Hsep0|].
 intros s observations Hmeta Htoken Hbuffer Hpending Herror Hinput.
 exact(NativeSecondArgumentByteErrorCommand.generated s (fun _=>false)(fun _=>0) opcode ch chars value sep0 spaces sep1 input tail observations
 Hsupported Hword Hencoding Hmeta Htoken Hbuffer Hpending Herror Hvalue Hsep0 Hsep1 Hspaces Hinput Hbytes Hbad).
Qed.
End NativeSecondArgumentByteErrorStop.
