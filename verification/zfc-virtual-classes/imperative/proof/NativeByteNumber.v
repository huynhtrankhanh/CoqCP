From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash ReadNat ReadToken TokenByte.
From Stdlib Require Import Lists.List ZArith.ZArith Bool.Bool Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteNumber.
Import IndexExecution SipHashExecution.
Lemma digits_ascii acc bytes value :
 ByteProtocol.digits acc bytes=ByteProtocol.number value -> Forall(fun byte=>48<=byte<=57)bytes.
Proof.
 induction bytes as [|byte tail IH] in acc|-*;cbn [ByteProtocol.digits];intro Hrun;[constructor|].
 destruct ((48<=?byte)&&(byte<=?57)) eqn:Hdigit;[|discriminate].
 destruct (acc <=? (ByteProtocol.maximum-(byte-48))/10) eqn:Hroom;[|discriminate].
 apply Bool.andb_true_iff in Hdigit as [Hlow Hhigh]. apply Z.leb_le in Hlow,Hhigh.
 constructor;[lia|now apply IH with (acc:=10*acc+(byte-48))].
Qed.
Lemma decode_ascii bytes value : ByteProtocol.decode_number bytes=ByteProtocol.number value ->
 Forall(fun byte=>48<=byte<=57)bytes.
Proof. destruct bytes as [|byte tail];[discriminate|]. cbn [ByteProtocol.decode_number]. apply digits_ascii. Qed.
Lemma number_from_fold acc bytes :
 ReadNatExecution.number_from acc bytes=fold_left(fun running byte=>10*running+(byte-48))bytes acc.
Proof. induction bytes as [|byte tail IH] in acc|-*;cbn [ReadNatExecution.number_from fold_left];[reflexivity|apply IH]. Qed.
Theorem generated_number native bs ns chars sep tail value observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 ->
 ByteProtocol.read_token (chars++sep::tail)=ByteProtocol.token chars tail false ->
 ByteProtocol.decode_number chars=ByteProtocol.number value ->
 TokenByteExecution.separator sep -> stdin native=chars++sep::tail ->
 execObserved(funcdef_0__readNat bs ns)(native,observations)=
 Some(tt,(ReadNatExecution.token_number(ReadTokenExecution.read_result native chars tail)chars,observations)) /\
 value=ReadNatExecution.number_from 0 chars /\ 0<=value<=IndexExecution.maximum.
Proof.
 intros Hmeta Htoken Hpending Herror Hlex Hdecode Hsep Hinput.
 destruct(ByteProtocol.read_token_valid _ _ _ _ Hlex) as [Hnonempty Hlength].
 pose proof(decode_ascii chars value Hdecode) as Hdigits.
 destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
 pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbounded.
 assert(Hpositive:(0<length chars)%nat) by (destruct chars;[contradiction|cbn;lia]).
 assert(Hnumber:value=ReadNatExecution.number_from 0 chars).
 { rewrite number_from_fold. exact Hvalue. }
 split.
 - apply ReadNatExecution.generated_readNat_observed.
   apply (ReadNatExecution.generated_readNat_none native bs ns chars sep tail);try assumption;try lia.
   rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia.
 - split;[exact Hnumber|]. unfold ByteProtocol.maximum,IndexExecution.maximum in *. exact Hbounded.
Qed.
End NativeByteNumber.
