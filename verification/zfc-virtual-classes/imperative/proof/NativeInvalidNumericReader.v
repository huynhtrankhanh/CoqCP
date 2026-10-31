From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadNatInvalid ReadNatOverflow NativeByteTokenInfo NativeReadTokenEOF NativeTooLongSeed.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeInvalidNumericReader.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Definition parsed s chars sep tail ended prefix := store_meta(store_meta(NativeByteTokenInfo.state s chars sep tail ended)14 0)11(number_from 0 prefix).
Theorem generated s bs ns chars spaces sep tail (ended:bool) prefix bad suffix observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=0 -> meta_value s 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> Forall TokenByteExecution.separator spaces -> TokenByteExecution.separator sep ->
 (if ended then stdin s=spaces++chars /\ tail=[] else stdin s=spaces++chars++sep::tail) ->
 prefix++bad::suffix=chars -> Forall(fun c=>48<=c<=57)prefix -> number_from 0 prefix<=maximum ->
 ((bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48))) ->
 let after:=parsed s chars sep tail ended prefix in
 execObserved(funcdef_0__readNat bs ns)(s,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ meta_value after 11=number_from 0 prefix /\ meta_value after 14=0 /\
 stdout after=stdout s /\ stdin after=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hspaces Hsep Hinput Hencoding Hdigits Hbound Hbad. cbn zeta.
 destruct(NativeByteTokenInfo.generated s chars spaces sep tail ended Hmeta Htoken Hpending Herror Hlength Hbytes Hspaces Hsep Hinput)
  as(Hreader & Htargetmeta & Hvalid & Hcount & Hcapacity & Hentries & Hclear & Htail).
 set(target:=NativeByteTokenInfo.state s chars sep tail ended) in *.
 assert(Hbadbyte:0<=bad<256).
 { apply Forall_forall with (x:=bad) in Hbytes;[tauto|]. rewrite <-Hencoding. apply in_or_app. right. now left. }
 assert(Hnumeric:exec(funcdef_0__readNat bs ns)s=Some(tt,parsed s chars sep tail ended prefix)).
 { unfold parsed. fold target. rewrite <-Hencoding in Hcount,Hcapacity,Hentries.
   destruct Hbad as [Hbad|[Hbad Hoverflow]].
   - exact(ReadNatInvalid.generated_readNat_nondigit s bs ns target prefix bad suffix Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbadbyte Hbad).
   - exact(ReadNatOverflow.generated_readNat_overflow s bs ns target prefix bad suffix Hreader Htargetmeta Hvalid Hcount Hcapacity Hentries Hdigits Hbound Hbad Hoverflow). }
 split;[now apply ReadNatExecution.generated_readNat_observed|].
 unfold parsed. fold target. split;[rewrite !store_meta_length;exact Htargetmeta|].
 split;[apply meta_store_same;rewrite store_meta_length;lia|].
 split;[rewrite meta_store_other by lia;apply meta_store_same;lia|].
 split.
 - change(stdout target=stdout s). unfold target,NativeByteTokenInfo.state. destruct ended.
   + unfold NativeReadTokenEOF.result. change(stdout(put_many(reset s)0 chars)=stdout s). rewrite NativeTooLongSeed.put_many_output. reflexivity.
   + apply ReadTokenExecution.result_output.
 - exact Htail.
Qed.
End NativeInvalidNumericReader.
