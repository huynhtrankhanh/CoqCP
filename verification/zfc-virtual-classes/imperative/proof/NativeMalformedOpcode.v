From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat TokenFrame ObservedLocal CommandQuit NativePendingBadNumber NativeMalformedCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMalformedOpcode.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadNatExecution.
Definition malformed prefix bad := (bad<48 \/ 57<bad) \/ (48<=bad<=57 /\ maximum<10*(number_from 0 prefix)+(bad-48)).
Theorem generated_pending s bs ns ch chars sep tail prefix bad suffix observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 (S(length chars)<=1024)%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> separator sep ->
 stdin s=chars++sep::tail -> prefix++bad::suffix=ch::chars ->
 Forall(fun x=>48<=x<=57)prefix -> number_from 0 prefix<=maximum -> malformed prefix bad ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,(NativeMalformedCommand.final(NativePendingBadNumber.parsed s ch chars tail prefix),
 observations++[{|flushedOutput:=stdout s++Protocol.reply_bytes Protocol.ERR;unreadInput:=tail|}])).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput Hencoding Hdigits Hbound Hbad.
 set(parsed:=NativePendingBadNumber.parsed s ch chars tail prefix).
 assert(Hreader:execObserved(funcdef_0__readNat (fun _=>false)(fun _=>0))(s,observations)=Some(tt,(parsed,observations))).
 { apply ReadNatExecution.generated_readNat_observed. unfold parsed,malformed in *.
   destruct Hbad as [Hbad|[Hbad Hoverflow]].
   - exact(NativePendingBadNumber.bad_digit s (fun _=>false)(fun _=>0) ch chars sep tail prefix bad suffix Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput Hencoding Hdigits Hbound Hbad).
   - exact(NativePendingBadNumber.overflow s (fun _=>false)(fun _=>0) ch chars sep tail prefix bad suffix Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hsep Hinput Hencoding Hdigits Hbound Hbad Hoverflow). }
 assert(Hparsedmeta:(17<length(memory parsed arraydef_0__meta))%nat).
 { unfold parsed,NativePendingBadNumber.parsed. rewrite !store_meta_length,pending_meta_length. exact Hmeta. }
 assert(Hnumber:meta_value parsed 11=number_from 0 prefix).
 { unfold parsed,NativePendingBadNumber.parsed. apply meta_store_same. rewrite store_meta_length,pending_meta_length. lia. }
 assert(Hvalid:meta_value parsed 14=0).
 { unfold parsed,NativePendingBadNumber.parsed. rewrite meta_store_other by lia. apply meta_store_same. rewrite pending_meta_length. lia. }
 assert(Hcount:meta_value parsed 6<>0).
 { unfold parsed,NativePendingBadNumber.parsed. rewrite !meta_store_other by lia. rewrite pending_count by exact Hmeta.
   intro Hzero. change(Z.of_nat(S(length chars))=Z.of_nat 0) in Hzero. apply Nat2Z.inj in Hzero. lia. }
 assert(Hin:stdin parsed=tail) by reflexivity.
 assert(Hout:stdout parsed=stdout s).
 { unfold parsed,NativePendingBadNumber.parsed. change(stdout(pending_result s ch chars tail)=stdout s). apply TokenFrame.pending_output. }
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:CommandQuitExecution.Frame).
 unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body. fold f.
 pose proof(NativeMalformedCommand.generated_body funcdef_0__readNat f parsed (number_from 0 prefix) observations Hreader Hparsedmeta Hnumber Hvalid Hcount) as Hrun.
 unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun,Hout,Hin. reflexivity.
Qed.
End NativeMalformedOpcode.
