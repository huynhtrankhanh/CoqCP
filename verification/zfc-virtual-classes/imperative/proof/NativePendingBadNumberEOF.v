From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow SipHash TokenByte ReadToken ReadNat ReadNatInvalid ReadNatOverflow NativePendingTokenEOF.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingBadNumberEOF.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadNatExecution.
Definition tokenstate s ch chars := NativePendingTokenEOF.eof_result s ch chars.
Definition parsed s ch chars prefix := store_meta(store_meta(tokenstate s ch chars)14 0)11(number_from 0 prefix).
Lemma token_meta_length s ch chars : length(memory(tokenstate s ch chars)arraydef_0__meta)=length(memory s arraydef_0__meta).
Proof. unfold tokenstate,NativePendingTokenEOF.eof_result. rewrite !store_meta_length. change(length(memory(put_many(started s ch)1 chars)arraydef_0__meta)=length(memory s arraydef_0__meta)). now rewrite put_many_meta_length,started_length. Qed.
Lemma token_valid s ch chars : (17<length(memory s arraydef_0__meta))%nat -> meta_value(tokenstate s ch chars)14=1.
Proof. intro H. unfold tokenstate,NativePendingTokenEOF.eof_result. apply meta_store_same. rewrite store_meta_length. change(14<length(memory(put_many(started s ch)1 chars)arraydef_0__meta))%nat. rewrite put_many_meta_length,started_length. lia. Qed.
Lemma token_count s ch chars : (17<length(memory s arraydef_0__meta))%nat -> meta_value(tokenstate s ch chars)6=Z.of_nat(S(length chars)).
Proof. intro H. unfold tokenstate,NativePendingTokenEOF.eof_result. rewrite !meta_store_other by lia. change(meta_value(put_many(started s ch)1 chars)6=Z.of_nat(S(length chars))). rewrite put_many_count;[reflexivity|rewrite started_length;lia|now apply started_count]. Qed.
Lemma token_length s ch chars : length(memory(tokenstate s ch chars)arraydef_0__token)=length(memory s arraydef_0__token).
Proof. unfold tokenstate,NativePendingTokenEOF.eof_result. rewrite !store_meta_other by discriminate. change(length(memory(put_many(started s ch)1 chars)arraydef_0__token)=length(memory s arraydef_0__token)). now rewrite put_many_token_length,started_token_length. Qed.
Lemma token_entry s ch chars i : (i<S(length chars))%nat -> (S(length chars)<=length(memory s arraydef_0__token))%nat ->
 List.nth i(memory(tokenstate s ch chars)arraydef_0__token)0=List.nth i(ch::chars)0.
Proof.
 intros Hindex Hcapacity. unfold tokenstate,NativePendingTokenEOF.eof_result. rewrite !store_meta_other by discriminate.
 change(List.nth i(memory(put_many(started s ch)1 chars)arraydef_0__token)0=List.nth i(ch::chars)0).
 destruct i as [|i].
 - rewrite put_many_before by lia. unfold started. rewrite store_meta_other by discriminate. rewrite put_byte_token.
   rewrite OverflowExecution.nth_insert_same;[reflexivity|rewrite reset_token;lia].
 - change(List.nth (1+i)(memory(put_many(started s ch)1 chars)arraydef_0__token)0=List.nth i chars 0).
   apply put_many_entry;[lia|]. rewrite started_token_length. exact Hcapacity.
Qed.
Theorem bad_digit s bs ns ch chars prefix bad suffix :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars ->
 stdin s=chars -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> number_from 0 prefix<=maximum -> (bad<48 \/ 57<bad) ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,parsed s ch chars prefix).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput Hencoding Hdigits Hbound Hbad.
 assert(Hbadbyte:0<=bad<256).
 { assert(Hall:Forall(fun x=>0<=x<256 /\ ~separator x)(prefix++bad::suffix)).
   { rewrite Hencoding. constructor;[auto|exact Hbytes]. }
   apply Forall_forall with(x:=bad)in Hall;[tauto|]. apply in_or_app. right;now left. }
 unfold parsed. apply(ReadNatInvalid.generated_readNat_nondigit s bs ns _ prefix bad suffix).
 - exact(NativePendingTokenEOF.generated_pending_eof s (fun _=>false)(fun _=>0) ch chars Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput).
 - now rewrite token_meta_length.
 - rewrite token_valid by exact Hmeta. discriminate.
 - rewrite Hencoding. cbn [length]. now apply token_count.
 - rewrite Hencoding. cbn [length]. rewrite token_length. lia.
 - intros i Hi. rewrite Hencoding in Hi|-*. apply token_entry;[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)].
 - exact Hdigits.
 - exact Hbound.
 - exact Hbadbyte.
 - exact Hbad.
Qed.
Theorem overflow s bs ns ch chars prefix bad suffix :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars ->
 stdin s=chars -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> number_from 0 prefix<=maximum -> 48<=bad<=57 ->
 maximum<10*(number_from 0 prefix)+(bad-48) ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,parsed s ch chars prefix).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput Hencoding Hdigits Hbound Hbad Hoverflow.
 unfold parsed. apply(ReadNatOverflow.generated_readNat_overflow s bs ns _ prefix bad suffix).
 - exact(NativePendingTokenEOF.generated_pending_eof s (fun _=>false)(fun _=>0) ch chars Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput).
 - now rewrite token_meta_length.
 - rewrite token_valid by exact Hmeta. discriminate.
 - rewrite Hencoding. cbn [length]. now apply token_count.
 - rewrite Hencoding. cbn [length]. rewrite token_length. lia.
 - intros i Hi. rewrite Hencoding in Hi|-*. apply token_entry;[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)].
 - exact Hdigits.
 - exact Hbound.
 - exact Hbad.
 - exact Hoverflow.
Qed.
End NativePendingBadNumberEOF.
