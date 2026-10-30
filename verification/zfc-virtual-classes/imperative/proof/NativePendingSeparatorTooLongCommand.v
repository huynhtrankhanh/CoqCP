From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ObservedLocal CommandQuit NativeTooLongSeed NativePendingSeparatorTooLong NativeInvalidCommand ReadTokenPendingLeading NativeMissingNumberEOF NativeTooLongSeed.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingSeparatorTooLongCommand.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Definition readstate s chars tail := store_meta(NativePendingSeparatorTooLong.result s chars tail)11 0.
Theorem generated_pending s bs ns initial spaces chars extra tail observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=initial+1 -> meta_value s 8=0 -> 0<=initial<256 -> separator initial -> Forall separator spaces ->
 length chars=1024%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=extra<256 -> ~separator extra ->
 stdin s=spaces++chars++extra::tail ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(NativeInvalidCommand.final(readstate s chars tail),
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])).
Proof.
 intros Hmeta Htoken Hpending Herror Hinitial Hsep Hspaces Hlength Hbytes Hextra Hbad Hinput.
 set(parsed:=readstate s chars tail).
 assert(Htokenreader:exec(funcdef_0__readToken(fun _=>false)(fun _=>0))s=Some(tt,NativePendingSeparatorTooLong.result s chars tail)).
 { exact(NativePendingSeparatorTooLong.generated_readToken s (fun _=>false)(fun _=>0) initial spaces chars extra tail Hmeta Htoken Hpending Herror Hinitial Hsep Hlength Hbytes Hextra Hbad Hspaces Hinput). }
 assert(Htokenmeta:(17<length(memory(NativePendingSeparatorTooLong.result s chars tail)arraydef_0__meta))%nat).
 { unfold NativePendingSeparatorTooLong.result. change(17<length(memory(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,ReadTokenPendingLeading.pending_base_length. exact Hmeta. }
 assert(Htokenvalid:meta_value(NativePendingSeparatorTooLong.result s chars tail)14=0).
 { unfold NativePendingSeparatorTooLong.result. change(meta_value(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1)14=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite ReadTokenPendingLeading.pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Hreader:execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(parsed,observations))).
 { apply ReadNatExecution.generated_readNat_observed. unfold parsed,readstate,funcdef_0__readNat.
   rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=s;bools:=fun _=>false;nums:=fun _=>0|} (NativePendingSeparatorTooLong.result s chars tail) Htokenreader ltac:(lia) Htokenvalid). reflexivity. }
 assert(Hparsedmeta:(17<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,readstate,NativePendingSeparatorTooLong.result. change(17<length(memory(store_meta(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1%Z)11 0%Z)arraydef_0__meta))%nat.
   rewrite !store_meta_length,put_many_meta_length,ReadTokenPendingLeading.pending_base_length. exact Hmeta. }
 assert(Hnumber:meta_value parsed 11=0).
 { unfold parsed,readstate. apply meta_store_same. unfold NativePendingSeparatorTooLong.result.
   change(11<length(memory(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,ReadTokenPendingLeading.pending_base_length. lia. }
 assert(Hvalid:meta_value parsed 14=0).
 { unfold parsed,readstate,NativePendingSeparatorTooLong.result. change(meta_value(store_meta(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1)11 0)14=0).
   rewrite !meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite ReadTokenPendingLeading.pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Herr:meta_value parsed 8=1).
 { unfold parsed,readstate,NativePendingSeparatorTooLong.result. change(meta_value(store_meta(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1)11 0)8=1).
   rewrite meta_store_other by lia. apply meta_store_same. rewrite put_many_meta_length,ReadTokenPendingLeading.pending_base_length. lia. }
 assert(Hcount:meta_value parsed 6=1024).
 { unfold parsed,readstate,NativePendingSeparatorTooLong.result. change(meta_value(store_meta(store_meta(put_many(ReadTokenPendingLeading.pending_base s)0 chars)8 1)11 0)6=1024).
   rewrite !meta_store_other by lia. rewrite put_many_count;[|rewrite ReadTokenPendingLeading.pending_base_length;lia|rewrite ReadTokenPendingLeading.pending_base_meta by (try exact Hmeta;lia);reflexivity].
   change(Z.of_nat(0+length chars)=1024). now rewrite Hlength. }
 assert(Hin:stdin parsed=tail) by reflexivity.
 assert(Hout:stdout parsed=stdout s).
 { unfold parsed,readstate,NativePendingSeparatorTooLong.result. change(stdout(put_many(ReadTokenPendingLeading.pending_base s)0 chars)=stdout s).
   rewrite NativeTooLongSeed.put_many_output. reflexivity. }
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:CommandQuitExecution.Frame).
 unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body. fold f.
 pose proof(NativeInvalidCommand.generated_body funcdef_0__readNat f parsed observations Hreader Hparsedmeta Hnumber Hvalid Herr Hcount) as Hrun.
 unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun,Hout,Hin. reflexivity.
Qed.
End NativePendingSeparatorTooLongCommand.
