From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken InternTail.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeReadTokenEOF.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Theorem payload_eof chars (f:Frame) size :
 (17<length(memory(machine f) arraydef_0__meta))%nat -> meta_value(machine f) 6=Z.of_nat size ->
 (size+length chars<=1024)%nat -> (1024<=length(memory(machine f) arraydef_0__token))%nat ->
 meta_value(machine f) 17=0 -> meta_value(machine f) 8=0 ->
 Forall(fun ch=>0<=ch<256 /\ ~separator ch)chars -> stdin(machine f)=chars ->
 tape_execution byte_body f (setMachine f (withInput (put_many(machine f) size chars) [])).
Proof.
 induction chars as [|ch chars IH] in f,size|-*.
 - intros Hmeta Hsize Hlimit Htoken Hdone Herror Hchars Hin.
   cbn [put_many]. assert(Hsame:setMachine f (withInput (machine f) [])=f).
   { destruct f as [s bs ns]. destruct s as [memory input output]. cbn in *. subst input. reflexivity. }
   rewrite Hsame. apply tape_eof. exact Hin.
 - intros Hmeta Hsize Hlimit Htoken Hdone Herror Hchars Hin.
   inversion Hchars as [|ch' chars' Hhead Hrest];subst ch' chars'. destruct Hhead as [Hbyte Hnosep].
   set(read:=setMachine f (withInput(machine f)chars)).
   set(next:=setMachine read (put_byte(machine read)size ch)).
   assert(Hbody:execLocal(byte_body ch)read=Some(KeepGoing,next)).
   { apply generated_data_byte;try assumption;cbn [length] in Hlimit;lia. }
   assert(Hnext:tape_execution byte_body next (setMachine next (withInput(put_many(machine next)(S size)chars)[]))).
   { apply IH.
     - change(17<length(memory(put_byte(machine read)size ch)arraydef_0__meta))%nat. now rewrite put_meta_length.
     - change(meta_value(put_byte(machine read)size ch)6=Z.of_nat(S size)). apply put_byte_count. change(6<length(memory(machine f)arraydef_0__meta))%nat;lia.
     - cbn [length] in Hlimit. lia.
     - change(1024<=length(memory(put_byte(machine read)size ch)arraydef_0__token))%nat. now rewrite put_token_length.
     - change(meta_value(put_byte(machine read)size ch)17=0). now rewrite put_byte_meta_other by lia.
     - change(meta_value(put_byte(machine read)size ch)8=0). now rewrite put_byte_meta_other by lia.
     - exact Hrest.
     - reflexivity. }
   assert(Hrel:setMachine next (withInput(put_many(machine next)(S size)chars)[])=
    setMachine f (withInput(put_many(machine f)size(ch::chars))[])).
   { unfold next,read. cbn [machine setMachine put_many]. rewrite put_byte_input,put_many_input. reflexivity. }
   rewrite <-Hrel. apply(tape_next byte_body f ch chars next);try assumption. unfold separator in Hnosep. lia.
Qed.
Lemma read_none_eof_composition tape_proc byte_proc (f:Frame) after :
 (17<length(memory(machine f)arraydef_0__meta))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 ->
 execLocal tape_proc (setMachine f (reset(machine f)))=Some(tt,setMachine f after) ->
 (17<length(memory after arraydef_0__meta))%nat ->
 meta_value after 17=0 -> meta_value after 8=0 -> meta_value after 6<>0 ->
 execLocal(read_with tape_proc byte_proc)f=Some(tt,setMachine f(store_meta(store_meta after 7 1)14 1)).
Proof.
 intros Hlength Hpending Herror Htape Hafter Hdone Herr Hsize.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold read_with. unfold reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
  |rewrite local_put_meta by (cbn [machine setMachine];rewrite ?store_meta_length;lia)
  |rewrite local_read_meta by (cbn [machine setMachine];rewrite ?store_meta_length;lia)
  |rewrite Htape |rewrite meta_store_other by lia |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr
  |progress replace (Z.to_nat 17) with 17%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 15) with 15%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 6) with 6%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by congruence|rewrite (bool_decide_false P) by congruence] end
  |progress cbn [bind optionBind machine setMachine fst snd shortCircuitAnd]
  |progress cbv beta iota zeta delta [machine setMachine bools nums]].
 reflexivity.
Qed.
Definition result native chars := store_meta(store_meta(withInput(put_many(reset native)0 chars)[])7 1)14 1.
Theorem generated native bs ns chars :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~separator ch)chars -> stdin native=chars ->
 exec(funcdef_0__readToken bs ns)native=Some(tt,result native chars).
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:Frame).
 set(after:=withInput(put_many(reset native)0 chars)[]).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after. change(17<length(memory(put_many(reset native)0 chars)arraydef_0__meta))%nat. now rewrite put_many_meta_length,reset_length. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(reset native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after. change(tape_execution byte_body (setMachine f(reset native))
    (setMachine(setMachine f(reset native))(withInput(put_many(reset native)0 chars)[]))).
   apply(payload_eof chars (setMachine f(reset native)) 0);cbn [machine setMachine].
   - now rewrite reset_length.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - exact(proj2 Hlength).
   - now rewrite reset_token.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. exact Herror.
   - exact Hbytes.
   - exact Hinput. }
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
End NativeReadTokenEOF.
