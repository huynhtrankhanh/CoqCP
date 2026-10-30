From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ObservedLocal CommandQuit NativeTooLongSeed NativePendingTooLong NativePendingTooLongNat NativeInvalidCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTooLongOpcode.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Definition readstate s ch chars tail := store_meta(NativePendingTooLong.result s ch chars tail)11 0.
Theorem generated_pending s bs ns ch chars extra tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 length chars=1023%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=extra<256 -> ~separator extra ->
 stdin s=chars++extra::tail ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(NativeInvalidCommand.final(readstate s ch chars tail),
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hextra Hbad Hinput.
 set(parsed:=readstate s ch chars tail).
 assert(Hreader:execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(parsed,observations))).
 { apply ReadNatExecution.generated_readNat_observed. unfold parsed,readstate.
   exact(NativePendingTooLongNat.generated s (fun _=>false)(fun _=>0) ch chars extra tail Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hextra Hbad Hinput). }
 assert(Hparsedmeta:(17<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,readstate,NativePendingTooLong.result. change(17<length(memory(store_meta(store_meta(put_many(started s ch)1 chars)8 1%Z)11 0%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length,put_many_meta_length,started_length. exact Hmeta. }
 assert(Hnumber:meta_value parsed 11=0).
 { unfold parsed,readstate. apply meta_store_same. unfold NativePendingTooLong.result.
   change(11<length(memory(store_meta(put_many(started s ch)1 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,started_length. lia. }
 assert(Hvalid:meta_value parsed 14=0).
 { unfold parsed,readstate,NativePendingTooLong.result. change(meta_value(store_meta(store_meta(put_many(started s ch)1 chars)8 1)11 0)14=0).
   rewrite !meta_store_other by lia. rewrite put_many_meta_other by lia. unfold started. rewrite meta_store_other by lia.
   rewrite put_byte_meta_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 assert(Herr:meta_value parsed 8=1).
 { unfold parsed,readstate,NativePendingTooLong.result. change(meta_value(store_meta(store_meta(put_many(started s ch)1 chars)8 1)11 0)8=1).
   rewrite meta_store_other by lia. apply meta_store_same. rewrite put_many_meta_length,started_length. lia. }
 assert(Hcount:meta_value parsed 6=1024).
 { unfold parsed,readstate,NativePendingTooLong.result. change(meta_value(store_meta(store_meta(put_many(started s ch)1 chars)8 1)11 0)6=1024).
   rewrite !meta_store_other by lia. rewrite put_many_count;[|rewrite started_length;lia|now apply started_count].
   change(Z.of_nat(1+length chars)=1024). now rewrite Hlength. }
 assert(Hin:stdin parsed=tail) by reflexivity.
 assert(Hout:stdout parsed=stdout s).
 { unfold parsed,readstate,NativePendingTooLong.result. change(stdout(put_many(started s ch)1 chars)=stdout s).
   rewrite NativeTooLongSeed.put_many_output. reflexivity. }
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:CommandQuitExecution.Frame).
 unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body. fold f.
 pose proof(NativeInvalidCommand.generated_body funcdef_0__readNat f parsed observations Hreader Hparsedmeta Hnumber Hvalid Herr Hcount) as Hrun.
 unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun,Hout,Hin. reflexivity.
Qed.
End NativeTooLongOpcode.
