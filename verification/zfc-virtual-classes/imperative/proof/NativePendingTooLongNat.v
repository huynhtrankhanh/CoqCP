From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat NativePendingTooLong NativeTooLongSeed.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingTooLongNat.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Theorem generated s bs ns ch chars extra tail :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 length chars=1023%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=extra<256 -> ~separator extra ->
 stdin s=chars++extra::tail ->
 exec(funcdef_0__readNat bs ns)s=Some(tt,store_meta(NativePendingTooLong.result s ch chars tail)11 0).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hextra Hbad Hinput.
 set(after:=NativePendingTooLong.result s ch chars tail).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))s=Some(tt,after)).
 { unfold after. exact(NativePendingTooLong.generated_readToken_pending s (fun _=>false)(fun _=>0) ch chars extra tail Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hextra Hbad Hinput). }
 assert(Hafter:(14<length(memory after arraydef_0__meta))%nat).
 { unfold after,NativePendingTooLong.result. change(14<length(memory(store_meta(put_many(started s ch)1 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,started_length. lia. }
 assert(Hinvalid:meta_value after 14=0).
 { unfold after,NativePendingTooLong.result. change(meta_value(store_meta(put_many(started s ch)1 chars)8 1)14=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. unfold started. rewrite meta_store_other by lia.
   rewrite put_byte_meta_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
 rewrite(NativeTooLongSeed.invalid_number funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=s;bools:=bs;nums:=ns|} after Hreader Hafter Hinvalid). reflexivity.
Qed.
End NativePendingTooLongNat.
