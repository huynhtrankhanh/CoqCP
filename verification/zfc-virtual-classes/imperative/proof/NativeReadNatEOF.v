From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadNatInvalid ReadToken TokenByte NativeReadTokenEOF NativeByteNumber NativeByteBadDigit.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeReadNatEOF.
Import IndexExecution SipHashExecution.
Lemma result_meta_length native chars :
 length(memory(NativeReadTokenEOF.result native chars)arraydef_0__meta)=length(memory native arraydef_0__meta).
Proof. unfold NativeReadTokenEOF.result. rewrite !store_meta_length. change(length(memory(ReadTokenExecution.put_many(ReadTokenExecution.reset native)0 chars)arraydef_0__meta)=length(memory native arraydef_0__meta)). now rewrite ReadTokenExecution.put_many_meta_length,ReadTokenExecution.reset_length. Qed.
Lemma result_token native chars :
 memory(NativeReadTokenEOF.result native chars)arraydef_0__token=memory(ReadTokenExecution.read_result native chars [])arraydef_0__token.
Proof. unfold NativeReadTokenEOF.result,ReadTokenExecution.read_result. repeat rewrite store_meta_other by discriminate. reflexivity. Qed.
Lemma result_token_length native chars :
 length(memory(NativeReadTokenEOF.result native chars)arraydef_0__token)=length(memory native arraydef_0__token).
Proof.
 unfold NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
 change(length(memory(ReadTokenExecution.put_many(ReadTokenExecution.reset native)0 chars)arraydef_0__token)=length(memory native arraydef_0__token)).
 now rewrite ReadTokenExecution.put_many_token_length,ReadTokenExecution.reset_token.
Qed.
Lemma result_valid native chars : (17<length(memory native arraydef_0__meta))%nat ->
 meta_value(NativeReadTokenEOF.result native chars)14=1.
Proof. intro H. unfold NativeReadTokenEOF.result. apply meta_store_same. rewrite store_meta_length. change(14<length(memory(ReadTokenExecution.put_many(ReadTokenExecution.reset native)0 chars)arraydef_0__meta))%nat. rewrite ReadTokenExecution.put_many_meta_length,ReadTokenExecution.reset_length. lia. Qed.
Lemma result_count native chars : (17<length(memory native arraydef_0__meta))%nat ->
 meta_value(NativeReadTokenEOF.result native chars)6=Z.of_nat(length chars).
Proof.
 intro H. unfold NativeReadTokenEOF.result. rewrite !meta_store_other by lia.
 change(meta_value(ReadTokenExecution.put_many(ReadTokenExecution.reset native)0 chars)6=Z.of_nat(length chars)).
 rewrite ReadTokenExecution.put_many_count.
 - reflexivity.
 - rewrite ReadTokenExecution.reset_length. lia.
 - rewrite ReadTokenExecution.reset_meta by exact H. reflexivity.
Qed.
Lemma result_entries native chars : (1024<=length(memory native arraydef_0__token))%nat -> (length chars<=1024)%nat ->
 forall i,(i<length chars)%nat -> List.nth i(memory(NativeReadTokenEOF.result native chars)arraydef_0__token)0=List.nth i chars 0.
Proof. intros Htoken Hlength i Hi. rewrite result_token. exact(ReadTokenExecution.result_token_entry native chars [] i Hi ltac:(lia)). Qed.
Theorem generated_valid native bs ns chars value observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token chars=ByteProtocol.token chars [] true ->
 ByteProtocol.decode_number chars=ByteProtocol.number value -> stdin native=chars ->
 execObserved(funcdef_0__readNat bs ns)(native,observations)=
 Some(tt,(ReadNatExecution.token_number(NativeReadTokenEOF.result native chars)chars,observations)) /\
 value=ReadNatExecution.number_from 0 chars /\ 0<=value<=IndexExecution.maximum /\
 stdin(ReadNatExecution.token_number(NativeReadTokenEOF.result native chars)chars)=[].
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 pose proof(NativeByteNumber.decode_ascii chars value Hdecode) as Hdigits.
 destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
 pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbound.
 assert(Hpositive:(0<length chars)%nat) by (destruct chars;[contradiction|cbn;lia]).
 assert(Hbytes:Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars).
 { apply Forall_impl with (P:=fun ch=>48<=ch<=57);[exact Hdigits|]. intros ch Hch. split;[lia|unfold TokenByteExecution.separator;lia]. }
 assert(Hnumber:value=ReadNatExecution.number_from 0 chars) by (rewrite NativeByteNumber.number_from_fold;exact Hvalue).
 split.
 - apply ReadNatExecution.generated_readNat_observed. apply ReadNatExecution.generated_readNat_from_token.
   + exact(NativeReadTokenEOF.generated native (fun _=>false)(fun _=>0) chars Hmeta Htoken Hpending Herror ltac:(lia) Hbytes Hinput).
   + rewrite result_meta_length. exact Hmeta.
   + rewrite result_valid by exact Hmeta. discriminate.
   + now apply result_count.
   + rewrite result_token_length. lia.
   + now apply result_entries.
   + exact Hdigits.
   + rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia.
 - split;[exact Hnumber|]. split;[unfold ByteProtocol.maximum,IndexExecution.maximum in *;exact Hbound|reflexivity].
Qed.
Theorem generated_bad native bs ns chars observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token chars=ByteProtocol.token chars [] true ->
 ByteProtocol.decode_number chars=ByteProtocol.number_error_result ByteProtocol.bad_digit ->
 Forall(fun byte=>0<=byte<256 /\ ~TokenByteExecution.separator byte)chars -> stdin native=chars ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ stdin after=[].
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hbytes Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 destruct(NativeByteBadDigit.decode_bad_prefix chars Hdecode Hnonempty) as(prefix & bad & suffix & Hchars & Hprefix & Hbound & Hbad).
 rewrite Hchars in Hbytes,Hlength,Hinput.
 assert(Hpositive:(0<length(prefix++bad::suffix))%nat) by (rewrite length_app;cbn [length];lia).
 assert(Hbyte:0<=bad<256).
 { apply List.Forall_forall with (x:=bad) in Hbytes;[tauto|]. apply in_or_app. right. now left. }
 set(after:=store_meta(store_meta(NativeReadTokenEOF.result native (prefix++bad::suffix))14 0)11(ReadNatExecution.number_from 0 prefix)).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold after. eapply ReadNatInvalid.generated_readNat_nondigit.
   - exact(NativeReadTokenEOF.generated native (fun _=>false)(fun _=>0) (prefix++bad::suffix) Hmeta Htoken Hpending Herror ltac:(lia) Hbytes Hinput).
   - rewrite result_meta_length. exact Hmeta.
   - rewrite result_valid by exact Hmeta. discriminate.
   - now apply result_count.
   - rewrite result_token_length. lia.
   - now apply result_entries.
   - exact Hprefix.
   - exact Hbound.
   - exact Hbyte.
   - exact Hbad. }
 exists after. split;[exact(ReadNatExecution.generated_readNat_observed native bs ns after observations Hrun)|].
 split.
 - unfold after. rewrite meta_store_other by lia. apply meta_store_same. rewrite result_meta_length. lia.
 - reflexivity.
Qed.
End NativeReadNatEOF.
