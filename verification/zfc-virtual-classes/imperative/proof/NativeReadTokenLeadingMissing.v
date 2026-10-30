From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadTokenLeading NativeMissingNumberEOF.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeReadTokenLeadingMissing.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Definition result native := store_meta(withInput(reset native)[])7 1.
Theorem generated_token native bs ns prefix :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> Forall separator prefix -> stdin native=prefix ->
 exec(funcdef_0__readToken bs ns)native=Some(tt,result native).
Proof.
 intros Hmeta Htoken Hpending Herror Hprefix Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:ReadTokenExecution.Frame).
 set(after:=withInput(reset native)[]).
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(reset native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after.
   eapply(ReadTokenLeading.skip_tape prefix (setMachine f(reset native)) []);cbn [machine setMachine].
   - exact Hprefix.
   - change(stdin native=prefix++[]). now rewrite app_nil_r.
   - now rewrite reset_length.
   - now rewrite reset_token.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. exact Herror.
   - apply tape_eof. reflexivity. }
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after. change(17<length(memory(reset native)arraydef_0__meta))%nat. now rewrite reset_length. }
 assert(Hdone:meta_value after 17=0) by (unfold after;change(meta_value(reset native)17=0);rewrite reset_meta by exact Hmeta;reflexivity).
 assert(Herr:meta_value after 8=0) by (unfold after;change(meta_value(reset native)8=0);rewrite reset_meta by exact Hmeta;exact Herror).
 assert(Hsize:meta_value after 6=0) by (unfold after;change(meta_value(reset native)6=0);rewrite reset_meta by exact Hmeta;reflexivity).
 rewrite(NativeMissingNumberEOF.read_empty_composition (tapeEnd byte_body) funcdef_0__tokenByte f after Hmeta Hpending Herror Htape Hafter Hdone Herr Hsize).
 reflexivity.
Qed.
Import ReadNatExecution.
Theorem generated_number native bs ns prefix observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> Forall TokenByteExecution.separator prefix -> stdin native=prefix ->
 exists after,execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(after,observations)) /\
 meta_value after 14=0 /\ meta_value after 11=0 /\ stdin after=[].
Proof.
 intros Hmeta Htoken Hpending Herror Hprefix Hinput.
 set(tokenstate:=result native).
 assert(Hreader:exec(funcdef_0__readToken (fun _=>false)(fun _=>0))native=Some(tt,tokenstate)).
 { unfold tokenstate. now apply(generated_token native (fun _=>false)(fun _=>0)prefix). }
 assert(Hlength:(17<length(memory tokenstate arraydef_0__meta))%nat).
 { unfold tokenstate,result. rewrite store_meta_length. change(17<length(memory(reset native)arraydef_0__meta))%nat. now rewrite reset_length. }
 assert(Hvalid:meta_value tokenstate 14=0).
 { unfold tokenstate,result. rewrite meta_store_other by lia. change(meta_value(reset native)14=0). rewrite reset_meta by exact Hmeta. reflexivity. }
 set(after:=store_meta tokenstate 11 0).
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,after)).
 { unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop {|machine:=native;bools:=bs;nums:=ns|} tokenstate Hreader ltac:(lia) Hvalid). reflexivity. }
 exists after. split;[now apply ReadNatExecution.generated_readNat_observed|]. split.
 - unfold after. rewrite meta_store_other by lia. exact Hvalid.
 - split;[unfold after;apply meta_store_same;lia|reflexivity].
Qed.
End NativeReadTokenLeadingMissing.
