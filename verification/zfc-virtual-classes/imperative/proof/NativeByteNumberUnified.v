From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadToken TokenByte NativeReadTokenEOF NativeByteNumber NativeByteNumberEOF NativeByteBadDigit NativeByteBadDigitEOF NativeByteOverflow NativeByteOverflowEOF.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteNumberUnified.
Import IndexExecution SipHashExecution ReadTokenExecution.
Theorem generated_token native bs ns chars sep tail ended observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> TokenByteExecution.separator sep ->
 Forall(fun byte=>0<=byte<256 /\ ~TokenByteExecution.separator byte)chars ->
 ByteProtocol.read_token (stdin native)=ByteProtocol.token chars tail ended ->
 (if ended then stdin native=chars /\ tail=[] else stdin native=chars++sep::tail) ->
 exists after, execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 stdin after=tail /\
 match ByteProtocol.decode_number chars with
 | ByteProtocol.number value=>meta_value after 14<>0 /\ meta_value after 11=value
 | ByteProtocol.number_error_result _=>meta_value after 14=0 end.
Proof.
 intros Hmeta Htoken Hpending Herror Hsep Hbytes Hlex Hinput.
 destruct ended.
 - cbn in Hinput. destruct Hinput as [Hin ->].
   destruct(ByteProtocol.decode_number chars) as [value|reason] eqn:Hdecode.
   + destruct(NativeByteNumberEOF.generated_number native bs ns chars value observations Hmeta Htoken Hpending Herror ltac:(rewrite <-Hin at 1;exact Hlex) Hdecode Hin) as [Hrun [Hvalue Hbound]].
     exists(ReadNatExecution.token_number(NativeReadTokenEOF.result native chars)chars). split;[exact Hrun|]. split;[reflexivity|].
     unfold ReadNatExecution.token_number. split.
     * rewrite meta_store_other by lia. unfold NativeReadTokenEOF.result. rewrite meta_store_same;[discriminate|].
       rewrite store_meta_length. change(14<length(memory(put_many(reset native)0 chars)arraydef_0__meta))%nat.
       rewrite put_many_meta_length,reset_length. lia.
     * rewrite meta_store_same;[symmetry;exact Hvalue|].
       unfold NativeReadTokenEOF.result. rewrite !store_meta_length.
       change(11<length(memory(put_many(reset native)0 chars)arraydef_0__meta))%nat.
       rewrite put_many_meta_length,reset_length. lia.
   + destruct reason.
     * destruct(NativeByteBadDigitEOF.generated_bad_number native bs ns chars observations Hmeta Htoken Hpending Herror ltac:(rewrite <-Hin at 1;exact Hlex) Hdecode Hbytes Hin)
        as(prefix & bad & suffix & after & Hchars & Hrun & Hbad & Htail).
       exists after. repeat split;assumption.
     * destruct(NativeByteOverflowEOF.generated_bad_number native bs ns chars observations Hmeta Htoken Hpending Herror ltac:(rewrite <-Hin at 1;exact Hlex) Hdecode Hbytes Hin)
        as(prefix & bad & suffix & after & Hchars & Hrun & Hbad & Htail).
       exists after. repeat split;assumption.
 - cbn in Hinput.
   destruct(ByteProtocol.decode_number chars) as [value|reason] eqn:Hdecode.
   + destruct(NativeByteNumber.generated_number native bs ns chars sep tail value observations Hmeta Htoken Hpending Herror ltac:(rewrite <-Hinput at 1;exact Hlex) Hdecode Hsep Hinput) as [Hrun [Hvalue Hbound]].
     exists(ReadNatExecution.token_number(ReadTokenExecution.read_result native chars tail)chars). split;[exact Hrun|]. split;[reflexivity|].
     unfold ReadNatExecution.token_number. split.
     * rewrite meta_store_other by lia. rewrite ReadTokenExecution.result_valid by exact Hmeta. discriminate.
     * rewrite meta_store_same;[symmetry;exact Hvalue|]. rewrite ReadTokenExecution.result_meta_length. lia.
   + destruct reason.
     * destruct(NativeByteBadDigit.generated_bad_number native bs ns chars sep tail observations Hmeta Htoken Hpending Herror ltac:(rewrite <-Hinput at 1;exact Hlex) Hdecode Hbytes Hsep Hinput)
        as(prefix & bad & suffix & after & Hchars & Hrun & Hbad & Htail).
       exists after. repeat split;assumption.
     * destruct(NativeByteOverflow.generated_bad_number native bs ns chars sep tail observations Hmeta Htoken Hpending Herror ltac:(rewrite <-Hinput at 1;exact Hlex) Hdecode Hbytes Hsep Hinput)
        as(prefix & bad & suffix & after & Hchars & Hrun & Hbad & Htail).
       exists after. repeat split;assumption.
Qed.
End NativeByteNumberUnified.
