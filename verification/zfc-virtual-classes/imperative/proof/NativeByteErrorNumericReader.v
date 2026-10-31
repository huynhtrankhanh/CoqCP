From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadNat ByteLexDecompose ByteLexErrors NativeByteReadNumber NativeByteBadDigit NativeByteOverflowEOF NativeGeneralPrefixStop NativeAnyWhitespaceUnaryErrorStop NativeMissingNumericReader NativeInvalidNumericReader NativeOverlongNumericReader.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeByteErrorNumericReader.
Import IndexExecution SipHashExecution ReadNatExecution.
Definition error_tail r := match r with
 | ByteProtocol.number_missing=>Some [] | ByteProtocol.number_too_long tail=>Some tail
 | ByteProtocol.number_invalid _ tail _=>Some tail | ByteProtocol.number_token _ _ _=>None end.
Theorem generated s bs ns observations tail :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> ByteProtocol.byte_stream(stdin s) ->
 error_tail(ByteProtocol.read_number(stdin s))=Some tail ->
 exists after, execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ meta_value after 14=0 /\ stdin after=tail /\ stdout after=stdout s.
Proof.
 intros Hmeta Htoken Hpending Hclear Hrange Herror.
 set(input:=stdin s) in *.
 unfold ByteProtocol.read_number in Herror.
 destruct(ByteProtocol.read_token input) as [|chars remaining ended|remaining] eqn:Hlex.
 - cbn [error_tail] in Herror. inversion Herror;subst tail.
   pose proof(ByteLexErrors.missing input Hlex) as Hspaces.
   apply NativeByteReadNumber.separators in Hspaces.
   pose proof(NativeMissingNumericReader.generated_number s bs ns input observations Hmeta Htoken Hpending Hclear Hspaces eq_refl)
    as(Hrun & Hlen & Hnum & Hvalid & Hin & Hout).
   exists(NativeMissingNumericReader.parsed s). repeat first [assumption|split].
 - destruct(ByteProtocol.decode_number chars) as [value|reason] eqn:Hdecode;[discriminate|].
   cbn [error_tail] in Herror. inversion Herror;subst tail.
   destruct(ByteLexDecompose.token input chars remaining ended Hlex)
     as(spaces & payload & Hspaces & Hchars & Hnosep & Hnonempty & Hending). subst payload.
   pose proof(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [_ Hlength].
   assert(Hlength':(0<length chars<=1024)%nat) by (split;[destruct chars;[contradiction|cbn;lia]|exact Hlength]).
   apply NativeByteReadNumber.separators in Hspaces.
   assert(Hmalformed:exists prefix bad suffix, prefix++bad::suffix=chars /\
     Forall(fun c=>48<=c<=57)prefix /\ number_from 0 prefix<=maximum /\
     ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48)))).
   { destruct reason.
     - destruct(NativeByteBadDigit.decode_bad_prefix chars Hdecode Hnonempty) as(p & bad & suffix & Heq & Hd & Hb & Hbad).
       exists p,bad,suffix. repeat split;try assumption;[symmetry;exact Heq|now left].
     - destruct(NativeByteOverflowEOF.decode_overflow_prefix chars Hdecode Hnonempty) as(p & bad & suffix & Heq & Hd & Hb & Hbad & Hover).
       exists p,bad,suffix. repeat split;try assumption;[symmetry;exact Heq|right;split;assumption]. }
   destruct Hmalformed as(prefix & bad & suffix & Hencoding & Hdigits & Hbound & Hbad).
   destruct Hending as [[Hended [Htail Hinput]]|[Hended [sep [Hsep Hinput]]]].
   + subst ended remaining. assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
     { apply(NativeByteReadNumber.body_bytes spaces chars []);[|exact Hnosep]. rewrite app_nil_r. now rewrite <-Hinput. }
     pose proof(NativeInvalidNumericReader.generated s bs ns chars spaces 32 [] true prefix bad suffix observations
       Hmeta Htoken Hpending Hclear Hlength' Hbytes Hspaces ltac:(unfold TokenByteExecution.separator;tauto)
       ltac:(cbn;split;[exact Hinput|reflexivity]) Hencoding Hdigits Hbound Hbad)
       as(Hrun & Hlen & Hnum & Hvalid & Hout & Hin).
     exists(NativeInvalidNumericReader.parsed s chars 32 [] true prefix). repeat first [assumption|split].
   + subst ended. apply ByteProtocol.separator_spec in Hsep.
     assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
     { apply(NativeByteReadNumber.body_bytes spaces chars (sep::remaining));[|exact Hnosep]. now rewrite <-Hinput. }
     pose proof(NativeInvalidNumericReader.generated s bs ns chars spaces sep remaining false prefix bad suffix observations
       Hmeta Htoken Hpending Hclear Hlength' Hbytes Hspaces Hsep Hinput Hencoding Hdigits Hbound Hbad)
       as(Hrun & Hlen & Hnum & Hvalid & Hout & Hin).
     exists(NativeInvalidNumericReader.parsed s chars sep remaining false prefix). repeat first [assumption|split].
 - cbn [error_tail] in Herror. inversion Herror;subst tail.
   destruct(ByteLexErrors.too_long input remaining Hlex) as(spaces & chars & extra & Hinput & Hspaces & Hlength & Hnosep & Hbad).
   apply NativeByteReadNumber.separators in Hspaces.
   assert(Hbytes:Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars).
   { apply(NativeByteReadNumber.body_bytes spaces chars (extra::remaining));[|exact Hnosep]. now rewrite <-Hinput. }
   assert(Hextra:0<=extra<256).
   { unfold ByteProtocol.byte_stream in Hrange. rewrite Hinput,!Forall_app in Hrange.
     destruct Hrange as [_ [_ Hlast]]. inversion Hlast;assumption. }
   assert(Hbad':~TokenByteExecution.separator extra) by (intro H;apply ByteProtocol.separator_spec in H;congruence).
   pose proof(NativeOverlongNumericReader.generated_number s bs ns spaces chars extra remaining observations
     Hmeta Htoken Hpending Hclear Hlength Hbytes Hextra Hbad' Hspaces Hinput) as(Hrun & Hlen & Hnum & Hvalid & Hfatal & Hin & Hout).
   exists(NativeOverlongNumericReader.parsed s chars remaining). repeat first [assumption|split].
Qed.
End NativeByteErrorNumericReader.
