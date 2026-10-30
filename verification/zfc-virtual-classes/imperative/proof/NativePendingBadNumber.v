From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadNatInvalid ReadNatOverflow.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingBadNumber.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadNatExecution.
Definition parsed s ch chars tail prefix := store_meta(store_meta(pending_result s ch chars tail)14 0)11(number_from 0 prefix).
Theorem bad_digit s bs ns ch chars sep tail prefix bad suffix :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> separator sep ->
 stdin s=chars++sep::tail -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> number_from 0 prefix<=maximum -> (bad<48 \/ 57<bad) ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,parsed s ch chars tail prefix).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput Hencoding Hdigits Hbound Hbad.
 assert(Hbadbyte:0<=bad<256).
 { assert(Hall:Forall(fun x=>0<=x<256 /\ ~separator x)(prefix++bad::suffix)).
   { rewrite Hencoding. constructor;[auto|exact Hbytes]. }
   apply Forall_forall with(x:=bad)in Hall;[tauto|]. apply in_or_app. right;now left. }
 unfold parsed. apply(ReadNatInvalid.generated_readNat_nondigit s bs ns _ prefix bad suffix).
 - exact(generated_readToken_pending s (fun _=>false)(fun _=>0) ch chars sep tail Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput).
 - now rewrite pending_meta_length.
 - rewrite pending_valid by exact Hmeta. discriminate.
 - rewrite Hencoding. cbn [length]. now apply pending_count.
 - rewrite Hencoding. cbn [length]. rewrite pending_token_length. lia.
 - intros i Hi. rewrite Hencoding in Hi|-*. apply pending_token_entry;[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)].
 - exact Hdigits.
 - exact Hbound.
 - exact Hbadbyte.
 - exact Hbad.
Qed.
Theorem overflow s bs ns ch chars sep tail prefix bad suffix :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> separator sep ->
 stdin s=chars++sep::tail -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> number_from 0 prefix<=maximum -> 48<=bad<=57 ->
 maximum<10*(number_from 0 prefix)+(bad-48) ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,parsed s ch chars tail prefix).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput Hencoding Hdigits Hbound Hbad Hoverflow.
 unfold parsed. apply(ReadNatOverflow.generated_readNat_overflow s bs ns _ prefix bad suffix).
 - exact(generated_readToken_pending s (fun _=>false)(fun _=>0) ch chars sep tail Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput).
 - now rewrite pending_meta_length.
 - rewrite pending_valid by exact Hmeta. discriminate.
 - rewrite Hencoding. cbn [length]. now apply pending_count.
 - rewrite Hencoding. cbn [length]. rewrite pending_token_length. lia.
 - intros i Hi. rewrite Hencoding in Hi|-*. apply pending_token_entry;[exact Hi|exact(Nat.le_trans _ _ _ Hlength Htoken)].
 - exact Hdigits.
 - exact Hbound.
 - exact Hbad.
 - exact Hoverflow.
Qed.
End NativePendingBadNumber.
