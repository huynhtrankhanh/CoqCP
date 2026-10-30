From CoqCP Require Import Options Imperative Execution.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat NativeGeneralPrefixStop NativeMalformedOpcode NativeMalformedOpcodeStop NativeMalformedOpcodeEOF NativeMalformedEOFStop NativeTooLongOpcodeStop NativeWhitespaceMalformedStop NativeWhitespaceMalformedEOFStop NativeWhitespaceTooLongStop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeAnyWhitespaceErrorStop.
Import IndexExecution SipHashExecution.
Theorem malformed spaces chars sep tail prefix bad suffix :
 Forall TokenByteExecution.separator spaces -> (0<length chars<=1024)%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> TokenByteExecution.separator sep ->
 prefix++bad::suffix=chars -> Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 NativeGeneralPrefixStop.stop_spec (spaces++chars++sep::tail) tail.
Proof.
 intros Hspaces Hlength Hbytes Hsep Hencoding Hdigits Hbound Hbad.
 destruct spaces as [|ch spaces].
 - destruct chars as [|first chars];[cbn in Hlength;lia|]. inversion Hbytes as [|? ? [Hfirst Hnosep] Hrest];subst.
   cbn [app] in *. cbn [length] in Hlength. apply NativeMalformedOpcodeStop.malformed with (prefix:=prefix)(bad:=bad)(suffix:=suffix);try assumption;try reflexivity;lia.
 - inversion Hspaces as [|? ? Hch Hrest];subst. assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
   cbn [app]. apply NativeWhitespaceMalformedStop.malformed with (prefix:=prefix)(bad:=bad)(suffix:=suffix);try assumption;try reflexivity;lia.
Qed.
Theorem malformed_eof spaces chars prefix bad suffix :
 Forall TokenByteExecution.separator spaces -> (0<length chars<=1024)%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 prefix++bad::suffix=chars -> Forall(fun x=>48<=x<=57)prefix -> ReadNatExecution.number_from 0 prefix<=maximum -> NativeMalformedOpcode.malformed prefix bad ->
 NativeGeneralPrefixStop.stop_spec (spaces++chars) [].
Proof.
 intros Hspaces Hlength Hbytes Hencoding Hdigits Hbound Hbad.
 destruct spaces as [|ch spaces].
 - destruct chars as [|first chars];[cbn in Hlength;lia|]. inversion Hbytes as [|? ? [Hfirst Hnosep] Hrest];subst.
   cbn [app] in *. cbn [length] in Hlength. apply NativeMalformedEOFStop.malformed with (prefix:=prefix)(bad:=bad)(suffix:=suffix);try assumption;try reflexivity;lia.
 - inversion Hspaces as [|? ? Hch Hrest];subst. assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
   cbn [app]. apply NativeWhitespaceMalformedEOFStop.malformed with (prefix:=prefix)(bad:=bad)(suffix:=suffix);try assumption;try reflexivity;lia.
Qed.
Theorem too_long spaces chars extra tail :
 Forall TokenByteExecution.separator spaces -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars ->
 0<=extra<256 -> ~TokenByteExecution.separator extra ->
 NativeGeneralPrefixStop.stop_spec (spaces++chars++extra::tail) tail.
Proof.
 intros Hspaces Hlength Hbytes Hextra Hbad.
 destruct spaces as [|ch spaces].
 - destruct chars as [|first chars];[cbn in Hlength;lia|]. inversion Hbytes as [|? ? [Hfirst Hnosep] Hrest];subst.
   cbn [app]. apply NativeTooLongOpcodeStop.too_long;try assumption. cbn in Hlength;lia.
 - inversion Hspaces as [|? ? Hch Hrest];subst. assert(Hchbyte:0<=ch<256) by (unfold TokenByteExecution.separator in Hch;lia).
   cbn [app]. apply NativeWhitespaceTooLongStop.too_long;assumption.
Qed.
End NativeAnyWhitespaceErrorStop.
