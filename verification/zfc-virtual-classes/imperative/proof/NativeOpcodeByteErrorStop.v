From CoqCP Require Import DecimalEncoding Options Imperative Execution InteractiveExecution.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat ByteLexDecompose ByteLexErrors NativeByteReadNumber NativeByteBadDigit NativeByteOverflowEOF NativeGeneralPrefixStop NativeMalformedOpcode NativeAnyWhitespaceErrorStop.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeOpcodeByteErrorStop.
Import IndexExecution SipHashExecution ReadNatExecution.
Definition error_tail r := match r with
 | ByteProtocol.number_too_long tail=>Some tail | ByteProtocol.number_invalid _ tail _=>Some tail | _=>None end.
Theorem generated input tail : ByteProtocol.byte_stream input -> error_tail(ByteProtocol.read_number input)=Some tail ->
 NativeGeneralPrefixStop.stop_spec input tail.
Proof.
 intros Hrange Herror. unfold ByteProtocol.read_number in Herror.
 destruct(ByteProtocol.read_token input) as [|chars remaining ended|remaining] eqn:Hlex;[discriminate| |].
 - destruct(ByteProtocol.decode_number chars) as [value|reason] eqn:Hdecode;[discriminate|].
   cbn [error_tail] in Herror. inversion Herror;subst tail.
   destruct(ByteLexDecompose.token input chars remaining ended Hlex)
    as(spaces & payload & Hspaces & Hchars & Hnosep & Hnonempty & Hending). subst payload.
   pose proof(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [_ Hlength].
   assert(Hlength':(0<length chars<=1024)%nat) by (split;[destruct chars;[contradiction|cbn;lia]|exact Hlength]).
   apply NativeByteReadNumber.separators in Hspaces.
   assert(Hmalformed:exists prefix bad suffix, prefix++bad::suffix=chars /\
     Forall(fun c=>48<=c<=57)prefix /\ number_from 0 prefix<=maximum /\ NativeMalformedOpcode.malformed prefix bad).
   { destruct reason.
     - destruct(NativeByteBadDigit.decode_bad_prefix chars Hdecode Hnonempty) as(p & bad & suffix & Heq & Hd & Hb & Hbad).
       exists p,bad,suffix. repeat split;try assumption;[symmetry;exact Heq|now left].
     - destruct(NativeByteOverflowEOF.decode_overflow_prefix chars Hdecode Hnonempty) as(p & bad & suffix & Heq & Hd & Hb & Hbad & Hover).
       exists p,bad,suffix. repeat split;try assumption;[symmetry;exact Heq|right;split;assumption]. }
   destruct Hmalformed as(prefix & bad & suffix & Hencoding & Hdigits & Hbound & Hbad).
   destruct Hending as [[Hended [Htail Hinput]]|[Hended [sep [Hsep Hinput]]]].
   + subst ended remaining. assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
     { apply(NativeByteReadNumber.body_bytes spaces chars []);[|exact Hnosep]. rewrite app_nil_r. now rewrite <-Hinput. }
     rewrite Hinput. now apply(NativeAnyWhitespaceErrorStop.malformed_eof spaces chars prefix bad suffix).
   + subst ended. apply ByteProtocol.separator_spec in Hsep.
     assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
     { apply(NativeByteReadNumber.body_bytes spaces chars (sep::remaining));[|exact Hnosep]. now rewrite <-Hinput. }
     rewrite Hinput. now apply(NativeAnyWhitespaceErrorStop.malformed spaces chars sep remaining prefix bad suffix).
 - cbn [error_tail] in Herror. inversion Herror;subst tail.
   destruct(ByteLexErrors.too_long input remaining Hlex) as(spaces & chars & extra & Hinput & Hspaces & Hlength & Hnosep & Hbad).
   apply NativeByteReadNumber.separators in Hspaces.
   assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
   { apply(NativeByteReadNumber.body_bytes spaces chars (extra::remaining));[|exact Hnosep]. now rewrite <-Hinput. }
   assert(Hextra:0<=extra<256).
   { unfold ByteProtocol.byte_stream in Hrange. rewrite Hinput,!Forall_app in Hrange.
     destruct Hrange as [_ [_ Hlast]]. inversion Hlast;assumption. }
   assert(Hbad':~TokenByteExecution.separator extra) by (intro H;apply ByteProtocol.separator_spec in H;congruence).
   rewrite Hinput. exact(NativeAnyWhitespaceErrorStop.too_long spaces chars extra remaining Hspaces Hlength Hbytes Hextra Hbad').
Qed.
End NativeOpcodeByteErrorStop.
