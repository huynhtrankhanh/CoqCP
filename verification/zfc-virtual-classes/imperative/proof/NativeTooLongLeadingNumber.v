From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat NativeTokenTooLong NativeMissingNumberEOF NativeReadTokenLeadingTooLong.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NativeTooLongLeadingNumber.
Import IndexExecution SipHashExecution ReadTokenExecution ReadNatExecution.
Theorem generated_number native bs ns prefix chars ch tail observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~TokenByteExecution.separator x)chars -> 0<=ch<256 -> ~TokenByteExecution.separator ch ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars++ch::tail ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ meta_value after 8=1 /\ stdin after=tail.
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hprefix Hinput.
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
 set(after:=store_meta tokenstate 11 0).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=native;bools:=bs;nums:=ns|} tokenstate Hreader ltac:(lia) Hvalid). reflexivity. }
 exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. split.
 - unfold after. now rewrite meta_store_other by lia.
 - split.
   + unfold after. now rewrite meta_store_other by lia.
   + reflexivity.
Qed.
End NativeTooLongLeadingNumber.
