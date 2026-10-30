From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken InternTail ReadTokenLeading SeedSeparator NativeReadTokenEOF.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeReadTokenLeadingEOF.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Import NativeReadTokenEOF.
Theorem generated native bs ns prefix chars :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~separator ch)chars -> Forall separator prefix -> stdin native=prefix++chars ->
 exec(funcdef_0__readToken bs ns)native=Some(tt,result native chars).
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hprefix Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:Frame).
 set(after:=withInput(put_many(reset native)0 chars)[]).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after. change(17<length(memory(put_many(reset native)0 chars)arraydef_0__meta))%nat. now rewrite put_many_meta_length,reset_length. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(reset native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after. change(tape_execution byte_body (setMachine f(reset native))
    (setMachine(setMachine f(reset native))(withInput(put_many(reset native)0 chars)[]))).
   eapply (ReadTokenLeading.skip_tape prefix (setMachine f(reset native)) chars);cbn [machine setMachine].
   - exact Hprefix.
   - change(stdin native=prefix++chars). exact Hinput.
   - now rewrite reset_length.
   - now rewrite reset_token.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. exact Herror.
   - pose proof(payload_eof chars (setMachine f(withInput(reset native)chars)) 0
       ltac:(change(17<length(memory(reset native)arraydef_0__meta))%nat;now rewrite reset_length)
       ltac:(change(meta_value(reset native)6=Z.of_nat 0);rewrite reset_meta by exact Hmeta;reflexivity)
       (proj2 Hlength)
       ltac:(change(1024<=length(memory(reset native)arraydef_0__token))%nat;now rewrite reset_token)
       ltac:(change(meta_value(reset native)17=0);rewrite reset_meta by exact Hmeta;reflexivity)
       ltac:(change(meta_value(reset native)8=0);rewrite reset_meta by exact Hmeta;exact Herror)
       Hbytes eq_refl) as Hpayload.
     cbn [machine setMachine] in Hpayload. rewrite put_many_input in Hpayload.
     cbn [withInput] in Hpayload. exact Hpayload. }
 assert(Hdone:meta_value after 17=0).
 { unfold after. change(meta_value(put_many(reset native)0 chars)17=0). rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 assert(Herr:meta_value after 8=0).
 { unfold after. change(meta_value(put_many(reset native)0 chars)8=0). rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. exact Herror. }
 assert(Hsize:meta_value after 6<>0).
 { unfold after. change(meta_value(put_many(reset native)0 chars)6<>0). rewrite put_many_count.
   - change(Z.of_nat(length chars)<>0). intro Hzero. change(Z.of_nat(length chars)=Z.of_nat 0) in Hzero. apply Nat2Z.inj in Hzero. lia.
   - rewrite reset_length. lia.
   - rewrite reset_meta by exact Hmeta. reflexivity. }
 rewrite(read_none_eof_composition (tapeEnd byte_body) funcdef_0__tokenByte f after Hmeta Hpending Herror Htape Hafter Hdone Herr Hsize).
 reflexivity.
Qed.
End NativeReadTokenLeadingEOF.
