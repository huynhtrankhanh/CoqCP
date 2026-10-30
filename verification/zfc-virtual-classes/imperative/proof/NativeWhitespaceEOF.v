From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadNat ObservedLocal CommandQuit NativePendingWhitespaceEOF NativeWhitespaceEOFCommand.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeWhitespaceEOF.
Import IndexExecution SipHashExecution TokenByteExecution.
Theorem generated s bs ns ch prefix observations :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> separator ch -> Forall separator prefix -> stdin s=prefix ->
 execObserved(funcdef_0__command bs ns)(s,observations)=Some(tt,
 (store_meta(NativePendingWhitespaceEOF.number_result s)9 1,observations)) /\
 stdin(store_meta(NativePendingWhitespaceEOF.number_result s)9 1)=[] /\
 stdout(store_meta(NativePendingWhitespaceEOF.number_result s)9 1)=stdout s /\
 meta_value(store_meta(NativePendingWhitespaceEOF.number_result s)9 1)9=1 /\
 meta_value(store_meta(NativePendingWhitespaceEOF.number_result s)9 1)8=0.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hsep Hprefix Hinput.
 destruct(NativePendingWhitespaceEOF.generated_number s (fun _=>false)(fun _=>0) ch prefix observations Hmeta Htoken Hpending Herror Hch Hsep Hprefix Hinput)
 as (Hreader & Hvalid & Hnumber & Heof & Hcount & Herr & Hin & Hout & Hlength).
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:CommandQuitExecution.Frame).
 split.
 - unfold funcdef_0__command. rewrite ObservedLocal.eliminate_correct,CommandQuitExecution.actual_body. fold f.
   pose proof(NativeWhitespaceEOFCommand.generated_body funcdef_0__readNat f (NativePendingWhitespaceEOF.number_result s) observations Hreader Hlength Hnumber Hvalid Herr Hcount Heof) as Hrun.
   unfold CommandQuitExecution.Frame in Hrun. rewrite Hrun. reflexivity.
 - split;[exact Hin|]. split;[exact Hout|]. split.
   + apply meta_store_same. lia.
   + rewrite meta_store_other by lia. exact Herr.
Qed.
End NativeWhitespaceEOF.
