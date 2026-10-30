From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenPendingLeading NativePendingSeparatorEOF.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativePendingSeparatorTokenInfo.
Import IndexExecution SipHashExecution ReadTokenExecution ReadTokenPendingLeading NativePendingSeparatorEOF.
Theorem generated native ch chars prefix sep tail :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch ->
 (0<length chars<=1024)%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars ->
 Forall TokenByteExecution.separator prefix -> TokenByteExecution.separator sep -> stdin native=prefix++chars++sep::tail ->
 let target:=pending_separator_result native chars tail in
 exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,target) /\
 (17<length(memory target arraydef_0__meta))%nat /\ meta_value target 14<>0 /\
 meta_value target 6=Z.of_nat(length chars) /\ (length chars<=length(memory target arraydef_0__token))%nat /\
 (forall i,(i<length chars)%nat -> List.nth i(memory target arraydef_0__token)0=List.nth i chars 0) /\
 meta_value target 8=0 /\ stdin target=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hbytes Hprefix Hsep Hinput. cbn zeta.
 split;[now apply (generated_pending_leading native (fun _=>false) (fun _=>0) ch prefix chars sep tail)|].
 split;[now rewrite result_meta_length|]. split;[rewrite result_valid by exact Hmeta;discriminate|].
 split;[now apply result_count|]. split;[rewrite result_token_length;lia|]. split.
 - intros i Hi. apply result_token_entry;[exact Hi|exact(Nat.le_trans _ _ _ (proj2 Hlength) Htoken)].
 - split;[|reflexivity]. unfold pending_separator_result. rewrite meta_store_other by lia.
   change(meta_value(store_meta(put_many(pending_base native)0 chars)17 1)8=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia.
   rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
Qed.
Theorem generated_eof native ch chars prefix :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> TokenByteExecution.separator ch ->
 (0<length chars<=1024)%nat -> Forall(fun c=>0<=c<256 /\ ~TokenByteExecution.separator c)chars ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars ->
 let target:=NativePendingSeparatorEOF.eof_result native chars in
 exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,target) /\
 (17<length(memory target arraydef_0__meta))%nat /\ meta_value target 14<>0 /\
 meta_value target 6=Z.of_nat(length chars) /\ (length chars<=length(memory target arraydef_0__token))%nat /\
 (forall i,(i<length chars)%nat -> List.nth i(memory target arraydef_0__token)0=List.nth i chars 0) /\
 meta_value target 8=0 /\ stdin target=[].
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hchsep Hlength Hbytes Hprefix Hinput. cbn zeta.
 split;[now apply (NativePendingSeparatorEOF.generated native (fun _=>false)(fun _=>0) ch prefix chars)|].
 assert(Hstate_meta:(17<length(memory(NativePendingSeparatorEOF.eof_result native chars)arraydef_0__meta))%nat).
     { unfold NativePendingSeparatorEOF.eof_result. rewrite !store_meta_length. change(17<length(memory(put_many(pending_base native)0 chars)arraydef_0__meta))%nat.
       now rewrite put_many_meta_length,pending_base_length. }
     split;[exact Hstate_meta|]. split.
     * unfold NativePendingSeparatorEOF.eof_result. rewrite meta_store_same;[discriminate|].
       rewrite store_meta_length. change(14<length(memory(put_many(pending_base native)0 chars)arraydef_0__meta))%nat.
       rewrite put_many_meta_length,pending_base_length. lia.
     * split.
       -- unfold NativePendingSeparatorEOF.eof_result. rewrite !meta_store_other by lia.
          change(meta_value(put_many(pending_base native)0 chars)6=Z.of_nat(length chars)).
          rewrite put_many_count;[reflexivity|rewrite pending_base_length;lia|rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity].
       -- split.
          ++ unfold NativePendingSeparatorEOF.eof_result. rewrite !store_meta_other by discriminate.
             change(length chars<=length(memory(put_many(pending_base native)0 chars)arraydef_0__token))%nat.
             rewrite put_many_token_length,pending_base_token. lia.
          ++ split.
             ** intros i Hi. unfold NativePendingSeparatorEOF.eof_result. rewrite !store_meta_other by discriminate.
                change(List.nth (0+i)(memory(put_many(pending_base native)0 chars)arraydef_0__token)0=List.nth i chars 0).
                apply put_many_entry;[exact Hi|rewrite pending_base_token;exact(Nat.le_trans _ _ _ (proj2 Hlength) Htoken)].
             ** split;[|reflexivity]. unfold NativePendingSeparatorEOF.eof_result. rewrite !meta_store_other by lia.
                change(meta_value(put_many(pending_base native)0 chars)8=0). rewrite put_many_meta_other by lia.
                rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
Qed.
End NativePendingSeparatorTokenInfo.
