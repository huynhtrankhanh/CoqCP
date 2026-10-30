From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken NativePendingTokenEOF.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativePendingByteTokenInfo.
Import IndexExecution SipHashExecution ReadTokenExecution.
Definition state native ch chars tail (ended:bool) := if ended then NativePendingTokenEOF.eof_result native ch chars else pending_result native ch chars tail.
Lemma eof_token native ch chars tail :
 memory(NativePendingTokenEOF.eof_result native ch chars)arraydef_0__token=memory(pending_result native ch chars tail)arraydef_0__token.
Proof.
 unfold NativePendingTokenEOF.eof_result,pending_result. rewrite !store_meta_other by discriminate.
 change(memory(put_many(started native ch)1 chars)arraydef_0__token=memory(store_meta(put_many(started native ch)1 chars)17 1)arraydef_0__token).
 now rewrite store_meta_other by discriminate.
Qed.
Theorem generated native ch chars sep tail (ended:bool) :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars -> TokenByteExecution.separator sep ->
 (if ended then stdin native=chars /\ tail=[] else stdin native=chars++sep::tail) ->
 let target:=state native ch chars tail ended in
 exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,target) /\
 (17<length(memory target arraydef_0__meta))%nat /\ meta_value target 14<>0 /\
 meta_value target 6=Z.of_nat(S(length chars)) /\
 (S(length chars)<=length(memory target arraydef_0__token))%nat /\
 (forall i,(i<S(length chars))%nat -> List.nth i(memory target arraydef_0__token)0=List.nth i(ch::chars)0) /\
 meta_value target 8=0 /\ stdin target=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput. cbn zeta.
 destruct ended.
 - cbn in Hinput. destruct Hinput as [Hin ->]. cbn [state]. split.
   + exact(NativePendingTokenEOF.generated_pending_eof native (fun _=>false)(fun _=>0) ch chars Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hin).
   + assert(Hstate_meta:(17<length(memory(NativePendingTokenEOF.eof_result native ch chars)arraydef_0__meta))%nat).
     { unfold NativePendingTokenEOF.eof_result. rewrite !store_meta_length. change(17<length(memory(put_many(started native ch)1 chars)arraydef_0__meta))%nat.
       now rewrite put_many_meta_length,started_length. }
     split;[exact Hstate_meta|]. split.
     * unfold NativePendingTokenEOF.eof_result. rewrite meta_store_same;[discriminate|].
       rewrite store_meta_length. change(14<length(memory(put_many(started native ch)1 chars)arraydef_0__meta))%nat.
       rewrite put_many_meta_length,started_length. lia.
     * split.
       -- unfold NativePendingTokenEOF.eof_result. rewrite !meta_store_other by lia.
          change(meta_value(put_many(started native ch)1 chars)6=Z.of_nat(S(length chars))).
          rewrite put_many_count;[reflexivity|rewrite started_length;lia|now apply started_count].
       -- split.
          ++ rewrite(eof_token native ch chars []). rewrite pending_token_length. lia.
          ++ split.
             ** intros i Hi. rewrite(eof_token native ch chars []). apply pending_token_entry;[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)].
             ** split;[|reflexivity]. unfold NativePendingTokenEOF.eof_result. rewrite !meta_store_other by lia.
                change(meta_value(put_many(started native ch)1 chars)8=0). rewrite put_many_meta_other by lia.
                apply started_zero;[exact Hmeta|right;auto].
 - cbn in Hinput. cbn [state]. split.
   + exact(ReadTokenExecution.generated_readToken_pending native (fun _=>false)(fun _=>0) ch chars sep tail Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput).
   + split;[now rewrite pending_meta_length|]. split;[rewrite pending_valid by exact Hmeta;discriminate|].
     split;[exact(pending_count native ch chars tail Hmeta)|]. split;[rewrite pending_token_length;lia|].
     split;[intros i Hi;apply pending_token_entry;[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)]|]. split.
     * unfold pending_result. rewrite meta_store_other by lia.
       change(meta_value(store_meta(put_many(started native ch)1 chars)17 1)8=0).
       rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. apply started_zero;[exact Hmeta|right;auto].
     * reflexivity.
Qed.
End NativePendingByteTokenInfo.
