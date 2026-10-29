From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadNatInvalid ReadToken TokenByte.
From Stdlib Require Import Lists.List ZArith.ZArith Bool.Bool Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteBadDigit.
Import IndexExecution SipHashExecution.
Lemma checked_accumulator acc byte :
 0<=acc<=ByteProtocol.maximum -> 48<=byte<=57 ->
 acc<=(ByteProtocol.maximum-(byte-48))/10 -> 0<=10*acc+(byte-48)<=ByteProtocol.maximum.
Proof.
 intros Hacc Hbyte Hroom. unfold ByteProtocol.maximum in *.
 assert(Hdiv:10*((18446744073709551615-(byte-48))/10)<=18446744073709551615-(byte-48)) by (apply Z.mul_div_le;lia).
 split;[lia|nia].
Qed.
Lemma digits_bad_prefix acc bytes : 0<=acc<=ByteProtocol.maximum ->
 ByteProtocol.digits acc bytes=ByteProtocol.number_error_result ByteProtocol.bad_digit ->
 exists prefix bad suffix,bytes=prefix++bad::suffix /\
 Forall(fun digit=>48<=digit<=57)prefix /\
 ReadNatExecution.number_from acc prefix<=IndexExecution.maximum /\ (bad<48 \/ 57<bad).
Proof.
 induction bytes as [|byte tail IH] in acc|-*;intros Hacc Hrun;cbn [ByteProtocol.digits] in Hrun;[discriminate|].
 destruct((48<=?byte)&&(byte<=?57)) eqn:Hdigit.
 - apply Bool.andb_true_iff in Hdigit as [Hlo Hhi]. apply Z.leb_le in Hlo,Hhi.
   destruct(acc <=? (ByteProtocol.maximum-(byte-48))/10) eqn:Hroom;[|discriminate].
   apply Z.leb_le in Hroom.
   destruct(IH (10*acc+(byte-48)) (checked_accumulator acc byte Hacc ltac:(lia) Hroom) Hrun)
    as(prefix & bad & suffix & Hbytes & Hprefix & Hbound & Hbad).
   exists(byte::prefix),bad,suffix. cbn [app ReadNatExecution.number_from]. split;[now rewrite Hbytes|].
   split;[constructor;[lia|exact Hprefix]|]. split;assumption.
 - exists [],byte,tail. cbn [app ReadNatExecution.number_from]. split;[reflexivity|].
   split;[constructor|]. split;[unfold ByteProtocol.maximum,IndexExecution.maximum in *;lia|].
   apply Bool.andb_false_iff in Hdigit. destruct Hdigit as [Hlo|Hhi].
   + apply Z.leb_gt in Hlo. lia.
   + apply Z.leb_gt in Hhi. lia.
Qed.
Theorem decode_bad_prefix bytes : ByteProtocol.decode_number bytes=ByteProtocol.number_error_result ByteProtocol.bad_digit -> bytes<>[] ->
 exists prefix bad suffix,bytes=prefix++bad::suffix /\
 Forall(fun digit=>48<=digit<=57)prefix /\
 ReadNatExecution.number_from 0 prefix<=IndexExecution.maximum /\ (bad<48 \/ 57<bad).
Proof.
 destruct bytes as [|byte tail];[tauto|]. cbn [ByteProtocol.decode_number]. intros Hrun Hnonempty.
 exact(digits_bad_prefix 0 (byte::tail) ltac:(unfold ByteProtocol.maximum;lia) Hrun).
Qed.
Theorem generated_bad_number native bs ns chars sep tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token (chars++sep::tail)=ByteProtocol.token chars tail false ->
 ByteProtocol.decode_number chars=ByteProtocol.number_error_result ByteProtocol.bad_digit ->
 Forall(fun byte=>0<=byte<256 /\ ~TokenByteExecution.separator byte)chars ->
 TokenByteExecution.separator sep -> stdin native=chars++sep::tail ->
 exists prefix bad suffix after,
 chars=prefix++bad::suffix /\
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ stdin after=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hbytes Hsep Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 destruct(decode_bad_prefix chars Hdecode Hnonempty) as(prefix & bad & suffix & Hchars & Hprefix & Hbound & Hbad).
 subst chars. set(result:=store_meta(store_meta(ReadTokenExecution.read_result native (prefix++bad::suffix) tail)14 0)11(ReadNatExecution.number_from 0 prefix)).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,result)).
 { unfold result. exact(ReadNatInvalid.generated_bad_token native bs ns prefix bad suffix sep tail Hmeta Htoken Hpending Herror Hlength Hbytes Hsep Hinput Hprefix Hbound Hbad). }
 exists prefix,bad,suffix,result. split;[reflexivity|]. split.
 - exact(ReadNatExecution.generated_readNat_observed native bs ns result observations Hrun).
 - split.
   + unfold result. rewrite meta_store_other by lia. apply meta_store_same.
     rewrite ReadTokenExecution.result_meta_length. lia.
   + reflexivity.
Qed.
End NativeByteBadDigit.
