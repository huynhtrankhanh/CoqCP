From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadToken TokenByte NativeReadTokenEOF NativeByteNumber.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteNumberEOF.
Import IndexExecution SipHashExecution ReadTokenExecution.
Theorem generated_number native bs ns chars value observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token chars=ByteProtocol.token chars [] true ->
 ByteProtocol.decode_number chars=ByteProtocol.number value -> stdin native=chars ->
 execObserved(funcdef_0__readNat bs ns)(native,observations)=
 Some(tt,(ReadNatExecution.token_number(NativeReadTokenEOF.result native chars)chars,observations)) /\
 value=ReadNatExecution.number_from 0 chars /\ 0<=value<=IndexExecution.maximum.
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 pose proof(NativeByteNumber.decode_ascii chars value Hdecode) as Hdigits.
 destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
 pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbounded.
 assert(Hpositive:(0<length chars)%nat) by (destruct chars;[contradiction|cbn;lia]).
 assert(Hnumber:value=ReadNatExecution.number_from 0 chars).
 { rewrite NativeByteNumber.number_from_fold. exact Hvalue. }
 assert(Hbytes:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
 { clear Hlex Hdecode Hinput Hnonempty Hlength Hvalue Hpositive Hnumber.
   induction Hdigits as [|ch tail Hch Hrest IH];[constructor|]. constructor;[|exact IH].
   unfold TokenByteExecution.separator;lia. }
 split.
 - apply ReadNatExecution.generated_readNat_observed.
   eapply ReadNatExecution.generated_readNat_from_token.
   + apply NativeReadTokenEOF.generated;try eassumption;lia.
   + unfold NativeReadTokenEOF.result. rewrite !store_meta_length. change (17<length(memory (put_many (reset native) 0 chars) arraydef_0__meta))%nat. now rewrite put_many_meta_length,reset_length.
   + unfold NativeReadTokenEOF.result. rewrite meta_store_same.
     * discriminate.
     * rewrite store_meta_length. change (14<length(memory (put_many (reset native) 0 chars) arraydef_0__meta))%nat. rewrite put_many_meta_length,reset_length. lia.
   + unfold NativeReadTokenEOF.result. rewrite !meta_store_other by lia.
     change (meta_value (put_many (reset native) 0 chars) 6 = Z.of_nat(length chars)).
     rewrite put_many_count;[|rewrite reset_length;lia|rewrite reset_meta by exact Hmeta;reflexivity]. reflexivity.
   + unfold NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
     change (length chars<=length(memory(put_many(reset native)0 chars)arraydef_0__token))%nat.
     rewrite put_many_token_length,reset_token. lia.
   + intros i Hi. unfold NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
     change (List.nth i (memory(put_many(reset native)0 chars)arraydef_0__token) 0=List.nth i chars 0).
     change (List.nth (0+i) (memory(put_many(reset native)0 chars)arraydef_0__token) 0=List.nth i chars 0).
     apply put_many_entry;[exact Hi|rewrite reset_token;exact (Nat.le_trans _ _ _ Hlength Htoken)].
   + exact Hdigits.
   + rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia.
 - split;[exact Hnumber|]. unfold ByteProtocol.maximum,IndexExecution.maximum in *. exact Hbounded.
Qed.
End NativeByteNumberEOF.
