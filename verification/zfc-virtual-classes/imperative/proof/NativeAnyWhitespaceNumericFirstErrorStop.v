From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat DecimalInput NativeMalformedFirstArgumentHandlers NativeMalformedTagHandlers NativeInvalidNumericFirstArgument NativeOverlongNumericFirstArgument NativeMissingNumericFirstArgument NativeGeneralPrefixStop NativeSpacedFirstArgumentStop NativeInvalidFirstArgument NativeOverlongFirstArgument NativeMissingFirstArgument NativeMalformedFirstArgumentCommand NativeReadTokenLeadingMissing ReadToken CommandInput.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeAnyWhitespaceNumericFirstErrorStop.
Import IndexExecution SipHashExecution ReadNatExecution.
Theorem invalid opcode digit digits leading separator chars spaces sep tail (ended:bool) prefix bad suffix :
 (NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) \/ NativeMalformedTagHandlers.supported (Z.of_nat opcode)) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator -> (0<length chars<=1024)%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces ->
 TokenByteExecution.separator sep -> (if ended then tail=[] else True) ->
 prefix++bad::suffix=chars -> Forall(fun c=>48<=c<=57)prefix -> number_from 0 prefix<=maximum ->
 ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48))) ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++separator::(if ended then spaces++chars else spaces++chars++sep::tail)) tail.
Proof.
 intros Hsupported Hword Hopencoding Hleading Hseparator Hlength Hbytes Hspaces Hsep Hended Hencoding Hdigits Hbound Hbad.
 pose proof(DecimalInput.decimal_word opcode Hword) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hopencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;exact Hword|exact Hleading|exact Hseparator|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 assert(Hinput':if ended then stdin s=digits++separator::spaces++chars /\ tail=[] else stdin s=digits++separator::spaces++chars++sep::tail).
 { destruct ended;cbn in *;tauto. }
 exact(NativeInvalidNumericFirstArgument.generated s (fun _=>false)(fun _=>0) opcode digit digits separator chars spaces sep tail ended prefix bad suffix observations
 Hsupported Hword Hopencoding Hmeta Htoken Hpending Herror Hseparator Hlength Hbytes Hspaces Hsep Hinput' Hencoding Hdigits Hbound Hbad).
Qed.
Theorem overlong opcode digit digits leading separator chars spaces extra tail :
 (NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) \/ NativeMalformedTagHandlers.supported (Z.of_nat opcode)) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator -> length chars=1024%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++separator::spaces++chars++extra::tail) tail.
Proof.
 intros Hsupported Hword Hopencoding Hleading Hseparator Hlength Hbytes Hspaces Hextra Hbad.
 pose proof(DecimalInput.decimal_word opcode Hword) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hopencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;exact Hword|exact Hleading|exact Hseparator|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeOverlongNumericFirstArgument.generated s (fun _=>false)(fun _=>0) opcode digit digits separator chars spaces extra tail observations
 Hsupported Hword Hopencoding Hmeta Htoken Hpending Herror Hseparator Hlength Hbytes Hspaces Hextra Hbad Hinput).
Qed.
Theorem missing opcode digit digits leading separator spaces :
 (NativeMalformedFirstArgumentHandlers.supported (Z.of_nat opcode) \/ NativeMalformedTagHandlers.supported (Z.of_nat opcode)) -> Z.of_nat opcode<=maximum -> decimalBytes opcode=digit::digits ->
 Forall TokenByteExecution.separator leading -> TokenByteExecution.separator separator -> Forall TokenByteExecution.separator spaces ->
 NativeGeneralPrefixStop.stop_spec (leading++(digit::digits)++separator::spaces) [].
Proof.
 intros Hsupported Hword Hopencoding Hleading Hseparator Hspaces.
 pose proof(DecimalInput.decimal_word opcode Hword) as [HopcodeValue [HopcodeDigits HopcodeLength]].
 rewrite Hopencoding in HopcodeValue,HopcodeDigits,HopcodeLength. cbn [length] in HopcodeLength.
 eapply NativeSpacedFirstArgumentStop.any_spaces;[lia|exact HopcodeDigits|rewrite HopcodeValue;exact Hword|exact Hleading|exact Hseparator|].
 intros s observations Hmeta Htoken Hpending Herror Hinput.
 exact(NativeMissingNumericFirstArgument.generated s (fun _=>false)(fun _=>0) opcode digit digits separator spaces observations
 Hsupported Hword Hopencoding Hmeta Htoken Hpending Herror Hseparator Hspaces Hinput).
Qed.
End NativeAnyWhitespaceNumericFirstErrorStop.
