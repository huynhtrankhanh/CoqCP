From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadNatInvalid ReadToken TokenByte NativeReadTokenEOF NativeByteBadDigit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteBadDigitEOF.
Import IndexExecution SipHashExecution ReadTokenExecution.
Theorem generated_bad_number native bs ns chars observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token chars=ByteProtocol.token chars [] true ->
 ByteProtocol.decode_number chars=ByteProtocol.number_error_result ByteProtocol.bad_digit ->
 Forall(fun byte=>0<=byte<256 /\ ~TokenByteExecution.separator byte)chars -> stdin native=chars ->
 exists prefix bad suffix after,
 chars=prefix++bad::suffix /\
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ stdin after=[].
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hbytes Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 destruct(NativeByteBadDigit.decode_bad_prefix chars Hdecode Hnonempty) as(prefix & bad & suffix & Hchars & Hprefix & Hbound & Hbad).
 subst chars.
 rewrite Hchars in Hbytes,Hlength.
 assert(Hinput:stdin native=prefix++bad::suffix) by exact Hchars.
 assert(Hpositive:(0<length(prefix++bad::suffix))%nat) by (rewrite length_app;cbn;lia).
 assert(Hbadbyte:0<=bad<256).
 { apply Forall_forall with (x:=bad) in Hbytes;[tauto|]. apply list_elem_of_In. apply in_or_app. right. now left. }
 set(tokenstate:=NativeReadTokenEOF.result native(prefix++bad::suffix)).
 set(after:=store_meta(store_meta tokenstate 14 0)11(ReadNatExecution.number_from 0 prefix)).
 assert(Hstate_meta:(17<length(memory tokenstate arraydef_0__meta))%nat).
 { unfold tokenstate,NativeReadTokenEOF.result. rewrite !store_meta_length.
   change (17<length(memory(put_many(reset native)0(prefix++bad::suffix))arraydef_0__meta))%nat.
   now rewrite put_many_meta_length,reset_length. }
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold after. apply(ReadNatInvalid.generated_readNat_nondigit native bs ns tokenstate prefix bad suffix).
   - unfold tokenstate. apply NativeReadTokenEOF.generated;try eassumption;lia.
   - exact Hstate_meta.
   - unfold tokenstate,NativeReadTokenEOF.result. rewrite meta_store_same;[discriminate|].
     rewrite store_meta_length. change (14<length(memory(put_many(reset native)0(prefix++bad::suffix))arraydef_0__meta))%nat.
     rewrite put_many_meta_length,reset_length. lia.
   - unfold tokenstate,NativeReadTokenEOF.result. rewrite !meta_store_other by lia.
     change(meta_value(put_many(reset native)0(prefix++bad::suffix))6=Z.of_nat(length(prefix++bad::suffix))).
     rewrite put_many_count;[reflexivity|rewrite reset_length;lia|rewrite reset_meta by exact Hmeta;reflexivity].
   - unfold tokenstate,NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
     change(length(prefix++bad::suffix)<=length(memory(put_many(reset native)0(prefix++bad::suffix))arraydef_0__token))%nat.
     rewrite put_many_token_length,reset_token. exact(Nat.le_trans _ _ _ Hlength Htoken).
   - intros i Hi. unfold tokenstate,NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
     change(List.nth (0+i)(memory(put_many(reset native)0(prefix++bad::suffix))arraydef_0__token)0=List.nth i(prefix++bad::suffix)0).
     apply put_many_entry;[exact Hi|rewrite reset_token;exact(Nat.le_trans _ _ _ Hlength Htoken)].
   - exact Hprefix.
   - exact Hbound.
   - exact Hbadbyte.
   - exact Hbad. }
 exists prefix,bad,suffix,after. split;[exact Hchars|]. split.
 - exact(ReadNatExecution.generated_readNat_observed native bs ns after observations Hrun).
 - split.
   + unfold after. rewrite meta_store_other by lia. apply meta_store_same. lia.
   + reflexivity.
Qed.
End NativeByteBadDigitEOF.
