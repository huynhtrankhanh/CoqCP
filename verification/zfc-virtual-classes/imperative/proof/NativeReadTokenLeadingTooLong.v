From CoqCP Require Import Options Imperative Execution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenLeading SeedSeparator NativeTokenTooLong.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeReadTokenLeadingTooLong.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Theorem generated_readToken native bs ns prefix chars ch tail :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=ch<256 -> ~separator ch ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars++ch::tail -> exec(funcdef_0__readToken bs ns)native=Some(tt,NativeTokenTooLong.result native chars tail).
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hprefix Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:Frame).
 set(after:=NativeTokenTooLong.result native chars tail).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after,NativeTokenTooLong.result. change(17<length(memory(store_meta(put_many(reset native)0 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,reset_length. exact Hmeta. }
 assert(Herr:meta_value after 8=1).
 { unfold after,NativeTokenTooLong.result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)8=1).
   apply meta_store_same. rewrite put_many_meta_length,reset_length. lia. }
 assert(Hdone:meta_value after 17=0).
 { unfold after,NativeTokenTooLong.result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)17=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 assert(Hsize:meta_value after 6=1024).
 { unfold after,NativeTokenTooLong.result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)6=1024).
   rewrite meta_store_other by lia. rewrite put_many_count;[|rewrite reset_length;lia|rewrite reset_meta by exact Hmeta;reflexivity].
   cbn. now rewrite Hlength. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(reset native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after,NativeTokenTooLong.result. change(tape_execution byte_body (setMachine f(reset native))
    (setMachine(setMachine f(reset native))(withInput(store_meta(put_many(reset native)0 chars)8 1)tail))).
   eapply(ReadTokenLeading.skip_tape prefix (setMachine f(reset native)) (chars++ch::tail));cbn [machine setMachine].
   - exact Hprefix.
   - change(stdin native=prefix++chars++ch::tail). exact Hinput.
   - now rewrite reset_length.
   - now rewrite reset_token.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. exact Herror.
   - pose proof(NativeTokenTooLong.payload_full chars (setMachine f(withInput(reset native)(chars++ch::tail))) 0 ch tail
      ltac:(change(17<length(memory(reset native)arraydef_0__meta))%nat;now rewrite reset_length)
      ltac:(change(meta_value(reset native)6=Z.of_nat 0);rewrite reset_meta by exact Hmeta;reflexivity)
      ltac:(cbn;exact Hlength)
      ltac:(change(1024<=length(memory(reset native)arraydef_0__token))%nat;now rewrite reset_token)
      ltac:(change(meta_value(reset native)17=0);rewrite reset_meta by exact Hmeta;reflexivity)
      ltac:(change(meta_value(reset native)8=0);rewrite reset_meta by exact Hmeta;exact Herror)
      Hbytes Hch Hnosep eq_refl) as Hpayload.
     cbn [machine setMachine] in Hpayload. rewrite put_many_input,SeedSeparator.store_input in Hpayload.
     cbn [withInput] in Hpayload. exact Hpayload. }
 rewrite(NativeTokenTooLong.read_none_full_composition (tapeEnd byte_body) funcdef_0__tokenByte f after Hmeta Hpending Herror Htape Hafter Herr Hdone Hsize).
 reflexivity.
Qed.
End NativeReadTokenLeadingTooLong.
