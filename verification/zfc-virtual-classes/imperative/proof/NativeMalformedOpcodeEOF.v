From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat TokenFrame ObservedLocal CommandQuit NativePendingBadNumberEOF NativeMalformedCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedOpcodeEOF.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadNatExecution.
Definition malformed prefix bad := (bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48)).
Theorem generated_pending s bs ns ch chars prefix bad suffix observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars ->
 stdin s=chars -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> number_from 0 prefix<=maximum -> malformed prefix bad ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(NativeMalformedCommand.final(NativePendingBadNumberEOF.parsed s ch chars prefix),
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=[]|}])).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput Hencoding Hdigits Hbound Hbad.
 set(parsed:=NativePendingBadNumberEOF.parsed s ch chars prefix).
 assert(Hreader:execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(parsed,observations))).
 { apply ReadNatExecution.generated_readNat_observed. unfold parsed,malformed in *.
   destruct Hbad as [Hbad|[Hbad Hoverflow]].
   - exact(NativePendingBadNumberEOF.bad_digit s (fun _=>false)(fun _=>0) ch chars prefix bad suffix Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput Hencoding Hdigits Hbound Hbad).
   - exact(NativePendingBadNumberEOF.overflow s (fun _=>false)(fun _=>0) ch chars prefix bad suffix Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hinput Hencoding Hdigits Hbound Hbad Hoverflow). }
 assert(Hparsedmeta:(17<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,NativePendingBadNumberEOF.parsed. rewrite !store_meta_length,NativePendingBadNumberEOF.token_meta_length. exact Hmeta. }
 assert(Hnumber:meta_value parsed 11=number_from 0 prefix).
 { unfold parsed,NativePendingBadNumberEOF.parsed. apply meta_store_same. rewrite store_meta_length,NativePendingBadNumberEOF.token_meta_length. lia. }
 assert(Hvalid:meta_value parsed 14=0).
 { unfold parsed,NativePendingBadNumberEOF.parsed. rewrite meta_store_other by lia. apply meta_store_same. rewrite NativePendingBadNumberEOF.token_meta_length. lia. }
 assert(Hcount:meta_value parsed 6<>0).
 { unfold parsed,NativePendingBadNumberEOF.parsed. rewrite !meta_store_other by lia. rewrite NativePendingBadNumberEOF.token_count by exact Hmeta.
   intro Hzero. change(Z.of_nat(S(length chars))=Z.of_nat 0) in Hzero. apply Nat2Z.inj in Hzero. lia. }
 assert(Hin:stdin parsed=[]) by reflexivity.
 assert(Hout:stdout parsed=stdout s).
 { unfold parsed,NativePendingBadNumberEOF.parsed. change(stdout(put_many(started s ch)1 chars)=stdout s). rewrite put_many_output. reflexivity. }
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:CommandQuitExecution.Frame).
 unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body. fold f.
 pose proof(NativeMalformedCommand.generated_body funcdef_0__readNat f parsed (number_from 0 prefix) observations Hreader Hparsedmeta Hnumber Hvalid Hcount) as Hrun.
 unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun,Hout,Hin. reflexivity.
Qed.
End NativeMalformedOpcodeEOF.
