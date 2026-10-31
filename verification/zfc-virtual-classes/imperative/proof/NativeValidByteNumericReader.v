From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import ByteProtocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat NativeReadTokenEOF NativeByteTokenInfo NativeByteNumber NativeTooLongSeed.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeValidByteNumericReader.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Theorem generated s bs ns chars spaces sep tail (ended:bool) value observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces -> TokenByteExecution.separator sep ->
 (if ended then stdin s=spaces++chars /\ tail=[] else stdin s=spaces++chars++sep::tail) ->
 ByteProtocol.decode_number chars=ByteProtocol.number value ->
 exists after, execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ (1024<=length(memory after arraydef_0__token))%nat /\
 meta_value after 15=0 /\ meta_value after 8=0 /\ meta_value after 14=1 /\ meta_value after 11=value /\
 stdin after=tail /\ stdout after=stdout s.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hspaces Hsep Hinput Hdecode.
 destruct(NativeByteTokenInfo.generated s chars spaces sep tail ended Hmeta Htoken Hpending Herror Hlength Hbytes Hspaces Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=NativeByteTokenInfo.state s chars sep tail ended) in *.
 pose proof(NativeByteNumber.decode_ascii chars value Hdecode) as Hdigits.
 destruct(ByteProtocol.decode_number_value chars value Hdecode) as [_ Hvalue].
 pose proof(ByteProtocol.decode_number_bounded chars value Hdecode) as Hbounded.
 assert(Hnumber:value=number_from 0 chars) by (rewrite NativeByteNumber.number_from_fold;exact Hvalue).
 assert(Hrun:exec(funcdef_0__readNat bs ns)s=Some(tt,token_number target chars)).
 { apply(ReadNatExecution.generated_readNat_from_token s bs ns target chars);try assumption.
   rewrite <-Hnumber. unfold ByteProtocol.maximum,IndexExecution.maximum in *. lia. }
 assert(Htoklength:length(memory target arraydef_0__token)=length(memory s arraydef_0__token)).
 { unfold target,NativeByteTokenInfo.state. destruct ended.
   - unfold NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
     change(length(memory(put_many(reset s)0 chars)arraydef_0__token)=length(memory s arraydef_0__token)). rewrite put_many_token_length,reset_token. reflexivity.
   - unfold read_result. rewrite !store_meta_other by discriminate.
     change(length(memory(put_many(reset s)0 chars)arraydef_0__token)=length(memory s arraydef_0__token)). rewrite put_many_token_length,reset_token. reflexivity. }
 assert(Htargetpending:meta_value target 15=0).
 { unfold target,NativeByteTokenInfo.state. destruct ended.
   - unfold NativeReadTokenEOF.result. rewrite !meta_store_other by lia.
     change(meta_value(put_many(reset s)0 chars)15=0). rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. exact Hpending.
   - rewrite result_meta_other by (try exact Hmeta;lia). exact Hpending. }
 assert(Htargetvalid:meta_value target 14=1).
 { unfold target,NativeByteTokenInfo.state. destruct ended.
   - unfold NativeReadTokenEOF.result. rewrite meta_store_same;[reflexivity|]. rewrite store_meta_length.
     change(14<length(memory(put_many(reset s)0 chars)arraydef_0__meta))%nat. rewrite put_many_meta_length,reset_length. lia.
   - now apply result_valid. }
 assert(Htargetout:stdout target=stdout s).
 { unfold target,NativeByteTokenInfo.state. destruct ended.
   - unfold NativeReadTokenEOF.result. change(stdout(put_many(reset s)0 chars)=stdout s). now rewrite NativeTooLongSeed.put_many_output.
   - apply result_output. }
 exists(token_number target chars). split;[now apply ReadNatExecution.generated_readNat_observed|].
 unfold token_number. split;[now rewrite store_meta_length|]. split;[rewrite store_meta_other by discriminate;now rewrite Htoklength|].
 repeat rewrite meta_store_other by lia. split;[exact Htargetpending|]. split;[exact Hclear|]. split;[exact Htargetvalid|].
 split;[rewrite Hnumber;apply meta_store_same;lia|]. split;[exact Htail|exact Htargetout].
Qed.
End NativeValidByteNumericReader.
