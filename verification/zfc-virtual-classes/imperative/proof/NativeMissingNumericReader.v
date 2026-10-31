From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadTokenLeading NativeMissingNumberEOF NativeReadTokenLeadingMissing.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeMissingNumericReader.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Definition result native := store_meta(withInput(reset native)[])7 1.
Import ReadNatExecution.
Definition parsed native := store_meta(NativeReadTokenLeadingMissing.result native)11 0.
Theorem generated_number native bs ns prefix observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> Forall TokenByteExecution.separator prefix -> stdin native=prefix ->
 let after:=parsed native in
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 (17<length(memory after arraydef_0__meta))%nat /\ meta_value after 11=0 /\ meta_value after 14=0 /\ stdin after=[] /\ stdout after=stdout native.
Proof.
 intros Hmeta Htoken Hpending Herror Hprefix Hinput. cbn zeta.
 set(tokenstate:=NativeReadTokenLeadingMissing.result native).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,tokenstate)).
 { unfold tokenstate. now apply(NativeReadTokenLeadingMissing.generated_token native (fun _=>false)(fun _=>0)prefix). }
 assert(Hlength:(17<length(memory tokenstate arraydef_0__meta))%nat).
 { unfold tokenstate,NativeReadTokenLeadingMissing.result. rewrite store_meta_length. change(17<length(memory(reset native)arraydef_0__meta))%nat. now rewrite reset_length. }
 assert(Hvalid:meta_value tokenstate 14=0).
 { unfold tokenstate,NativeReadTokenLeadingMissing.result. rewrite meta_store_other by lia. change(meta_value(reset native)14=0). rewrite reset_meta by exact Hmeta. reflexivity. }
 set(after:=parsed native).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold after,parsed,funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=native;bools:=bs;nums:=ns|} tokenstate Hreader ltac:(lia) Hvalid). reflexivity. }
 split;[now apply ReadNatExecution.generated_readNat_observed|].
 assert(Haftermeta:(17<length(memory after arraydef_0__meta))%nat) by (unfold after,parsed;rewrite store_meta_length;exact Hlength).
 split;[exact Haftermeta|].
 split;[unfold after,parsed;apply meta_store_same;change(11<length(memory tokenstate arraydef_0__meta))%nat;lia|].
 split;[unfold after,parsed;rewrite meta_store_other by lia;exact Hvalid|].
 split;[reflexivity|reflexivity].
Qed.
End NativeMissingNumericReader.
