From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenLeading NativeReadTokenEOF NativeReadTokenLeadingEOF.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeByteTokenInfo.
Import IndexExecution SipHashExecution ReadTokenExecution.
Definition state native chars (sep:Z) tail (ended:bool) := if ended then NativeReadTokenEOF.result native chars else ReadTokenExecution.read_result native chars tail.
Theorem generated native chars prefix sep tail (ended:bool) :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~TokenByteExecution.separator ch)chars ->
 Forall TokenByteExecution.separator prefix -> TokenByteExecution.separator sep ->
 (if ended then stdin native=prefix++chars /\ tail=[] else stdin native=prefix++chars++sep::tail) ->
 let target:=state native chars sep tail ended in
 exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,target) /\
 (17<length(memory target arraydef_0__meta))%nat /\ meta_value target 14<>0 /\
 meta_value target 6=Z.of_nat(length chars) /\
 (length chars<=length(memory target arraydef_0__token))%nat /\
 (forall i,(i<length chars)%nat -> List.nth i(memory target arraydef_0__token)0=List.nth i chars 0) /\
 meta_value target 8=0 /\ stdin target=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hprefix Hsep Hinput. cbn zeta.
 destruct ended.
 - cbn in Hinput. destruct Hinput as [Hin ->]. cbn [state].
   split.
   + exact(NativeReadTokenLeadingEOF.generated native (fun _=>false)(fun _=>0) prefix chars Hmeta Htoken Hpending Herror Hlength Hbytes Hprefix Hin).
   + assert(Hstate_meta:(17<length(memory(NativeReadTokenEOF.result native chars)arraydef_0__meta))%nat).
     { unfold NativeReadTokenEOF.result. rewrite !store_meta_length. change(17<length(memory(put_many(reset native)0 chars)arraydef_0__meta))%nat.
       now rewrite put_many_meta_length,reset_length. }
     split;[exact Hstate_meta|]. split.
     * unfold NativeReadTokenEOF.result. rewrite meta_store_same;[discriminate|].
       rewrite store_meta_length. change(14<length(memory(put_many(reset native)0 chars)arraydef_0__meta))%nat.
       rewrite put_many_meta_length,reset_length. lia.
     * split.
       -- unfold NativeReadTokenEOF.result. rewrite !meta_store_other by lia.
          change(meta_value(put_many(reset native)0 chars)6=Z.of_nat(length chars)).
          rewrite put_many_count;[reflexivity|rewrite reset_length;lia|rewrite reset_meta by exact Hmeta;reflexivity].
       -- split.
          ++ unfold NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
             change(length chars<=length(memory(put_many(reset native)0 chars)arraydef_0__token))%nat.
             rewrite put_many_token_length,reset_token. lia.
          ++ split.
             ** intros i Hi. unfold NativeReadTokenEOF.result. rewrite !store_meta_other by discriminate.
                change(List.nth (0+i)(memory(put_many(reset native)0 chars)arraydef_0__token)0=List.nth i chars 0).
                apply put_many_entry;[exact Hi|rewrite reset_token;exact(Nat.le_trans _ _ _ (proj2 Hlength) Htoken)].
             ** split;[|reflexivity]. unfold NativeReadTokenEOF.result. rewrite !meta_store_other by lia.
                change(meta_value(put_many(reset native)0 chars)8=0). rewrite put_many_meta_other by lia.
                rewrite reset_meta by exact Hmeta. exact Herror.
 - cbn in Hinput. cbn [state]. split.
   + exact(ReadTokenLeading.generated_readToken_leading native (fun _=>false)(fun _=>0) prefix chars sep tail Hmeta Htoken Hpending Herror Hlength Hbytes Hsep Hprefix Hinput).
   + split;[now rewrite result_meta_length|]. split;[rewrite result_valid by exact Hmeta;discriminate|].
     split;[exact(result_count native chars tail Hmeta)|]. split.
     * unfold read_result. rewrite store_meta_other by discriminate.
       change(length chars<=length(memory(store_meta(put_many(reset native)0 chars)17 (1%Z))arraydef_0__token))%nat.
       rewrite store_meta_other by discriminate. rewrite put_many_token_length,reset_token. lia.
     * split;[intros i Hi;apply result_token_entry;[exact Hi|exact(Nat.le_trans _ _ _ (proj2 Hlength) Htoken)]|]. split.
       -- rewrite result_meta_other by lia. exact Herror.
       -- reflexivity.
Qed.
End NativeByteTokenInfo.
