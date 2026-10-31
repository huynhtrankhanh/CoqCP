From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat NativeTokenTooLong NativeMissingNumberEOF NativeReadTokenLeadingTooLong NativeTooLongSeed.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeOverlongNumericReader.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Definition parsed native chars tail := store_meta(NativeTokenTooLong.result native chars tail)11 0.
Theorem generated_number native bs ns prefix chars ch tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars++ch::tail ->
 let after:=parsed native chars tail in
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ meta_value after 11=0 /\ meta_value after 14=0 /\ meta_value after 8=1 /\
 stdin after=tail /\ stdout after=stdout native.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hprefix Hinput. cbn zeta.
 set(tokenstate:=NativeTokenTooLong.result native chars tail).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,tokenstate)).
 { unfold tokenstate. exact(NativeReadTokenLeadingTooLong.generated_readToken native (fun _=>false)(fun _=>0) prefix chars ch tail Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hprefix Hinput). }
 assert(Hstate_meta:(17<length(memory tokenstate arraydef_0__meta))%nat).
 { unfold tokenstate,NativeTokenTooLong.result. change(17<length(memory(store_meta(put_many(reset native)0 chars)8 (1%Z))arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,reset_length. exact Hmeta. }
 assert(Hvalid:meta_value tokenstate 14=0).
 { unfold tokenstate,NativeTokenTooLong.result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)14=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 assert(Hfatal:meta_value tokenstate 8=1).
 { unfold tokenstate,NativeTokenTooLong.result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)8=1).
   apply meta_store_same. rewrite put_many_meta_length,reset_length. lia. }
 set(after:=parsed native chars tail).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold after,parsed,funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=native;bools:=bs;nums:=ns|} tokenstate Hreader ltac:(lia) Hvalid). reflexivity. }
 split;[now apply ReadNatExecution.generated_readNat_observed|].
 assert(Haftermeta:(17<length(memory after arraydef_0__meta))%nat) by (unfold after,parsed;rewrite store_meta_length;exact Hstate_meta).
 split;[exact Haftermeta|].
 assert(Hnumber:meta_value after 11=0) by (unfold after,parsed;apply meta_store_same;change(11<length(memory tokenstate arraydef_0__meta))%nat;lia).
 split;[exact Hnumber|].
 split;[unfold after,parsed;rewrite meta_store_other by lia;exact Hvalid|].
 split;[unfold after,parsed;rewrite meta_store_other by lia;exact Hfatal|].
 split;[reflexivity|].
 unfold after,parsed,NativeTokenTooLong.result. change(stdout(put_many(reset native)0 chars)=stdout native).
 rewrite NativeTooLongSeed.put_many_output. reflexivity.
Qed.
End NativeOverlongNumericReader.
