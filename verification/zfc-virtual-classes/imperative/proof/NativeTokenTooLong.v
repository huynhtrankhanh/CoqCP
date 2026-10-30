From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken InternTail.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativeTokenTooLong.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Lemma generated_full_byte (f:Frame) ch :
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)6=1024 ->
 (1024<=length(memory(machine f)arraydef_0__token))%nat -> 0<=ch<256 -> ~separator ch ->
 meta_value(machine f)17=0 ->
 execLocal(byte_body ch) f=Some(Stop,setMachine f(store_meta(machine f)8 1)).
Proof.
 intros Hmeta Hsize Htoken Hbyte Hnosep Hdone.
 rewrite(generated_byte_body f 1024 ch Hmeta Hsize ltac:(lia) Htoken Hbyte).
 unfold tick. rewrite bool_decide_false by exact Hnosep. rewrite bool_decide_true by reflexivity.
 unfold byte_outcome. rewrite meta_store_other by lia. rewrite Hdone,bool_decide_false by congruence.
 rewrite meta_store_same by lia. rewrite bool_decide_true by discriminate. reflexivity.
Qed.
Theorem payload_full chars (f:Frame) size ch tail :
 (17<length(memory(machine f)arraydef_0__meta))%nat -> meta_value(machine f)6=Z.of_nat size ->
 (size+length chars=1024)%nat -> (1024<=length(memory(machine f)arraydef_0__token))%nat ->
 meta_value(machine f)17=0 -> meta_value(machine f)8=0 ->
 Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=ch<256 -> ~separator ch ->
 stdin(machine f)=chars++ch::tail ->
 tape_execution byte_body f (setMachine f(withInput(store_meta(put_many(machine f)size chars)8 1)tail)).
Proof.
 induction chars as [|x chars IH] in f,size|-*.
 - intros Hmeta Hsize Hlen Htoken Hdone Herror Hchars Hch Hnosep Hin.
   cbn [length] in Hlen. assert(HsizeEq:size=1024%nat) by lia. subst size. cbn [put_many List.app] in *.
   apply(tape_stop byte_body f ch tail).
   + exact Hin.
   + lia.
   + rewrite(generated_full_byte (setMachine f(withInput(machine f)tail)) ch Hmeta Hsize Htoken Hch Hnosep Hdone). reflexivity.
 - intros Hmeta Hsize Hlen Htoken Hdone Herror Hchars Hch Hnosep Hin.
   inversion Hchars as [|x' xs Hhead Hrest];subst x' xs. destruct Hhead as [Hx Hxsep].
   set(read:=setMachine f(withInput(machine f)(chars++ch::tail))).
   set(next:=setMachine read(put_byte(machine read)size x)).
   assert(Hbody:execLocal(byte_body x)read=Some(KeepGoing,next)).
   { apply generated_data_byte;try assumption;cbn [length] in Hlen;lia. }
   assert(Hnext:tape_execution byte_body next
    (setMachine next(withInput(store_meta(put_many(machine next)(S size)chars)8 1)tail))).
   { apply IH.
     - change(17<length(memory(put_byte(machine read)size x)arraydef_0__meta))%nat. now rewrite put_meta_length.
     - change(meta_value(put_byte(machine read)size x)6=Z.of_nat(S size)). apply put_byte_count. change(6<length(memory(machine f)arraydef_0__meta))%nat;lia.
     - cbn [length] in Hlen. lia.
     - change(1024<=length(memory(put_byte(machine read)size x)arraydef_0__token))%nat. now rewrite put_token_length.
     - change(meta_value(put_byte(machine read)size x)17=0). now rewrite put_byte_meta_other by lia.
     - change(meta_value(put_byte(machine read)size x)8=0). now rewrite put_byte_meta_other by lia.
     - exact Hrest.
     - exact Hch.
     - exact Hnosep.
     - reflexivity. }
   assert(Hrel:setMachine next(withInput(store_meta(put_many(machine next)(S size)chars)8 1)tail)=
    setMachine f(withInput(store_meta(put_many(machine f)size(x::chars))8 1)tail)).
   { unfold next,read. cbn [machine setMachine put_many]. rewrite put_byte_input,put_many_input. reflexivity. }
   rewrite <-Hrel. apply(tape_next byte_body f x (chars++ch::tail) next);try assumption. lia.
Qed.
Lemma read_none_full_composition tape_proc byte_proc (f:Frame) after :
 (17<length(memory(machine f)arraydef_0__meta))%nat ->
 meta_value(machine f)15=0 -> meta_value(machine f)8=0 ->
 execLocal tape_proc (setMachine f(reset(machine f)))=Some(tt,setMachine f after) ->
 (17<length(memory after arraydef_0__meta))%nat -> meta_value after 8=1 -> meta_value after 17=0 -> meta_value after 6=1024 ->
 execLocal(read_with tape_proc byte_proc)f=Some(tt,setMachine f after).
Proof.
 intros Hlength Hpending Herror Htape Hafter Herr Hdone Hsize.
 destruct f as [s bs ns]. cbn [machine] in *.
 unfold read_with. unfold reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
  |rewrite local_put_meta by (cbn [machine setMachine];rewrite ?store_meta_length;lia)
  |rewrite local_read_meta by (cbn [machine setMachine];rewrite ?store_meta_length;lia)
  |rewrite Htape |rewrite meta_store_other by lia |rewrite meta_store_same by (rewrite ?store_meta_length;lia)
  |rewrite Hpending |rewrite Herror |rewrite Herr |rewrite Hdone |rewrite Hsize
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
Definition result native chars tail := withInput(store_meta(put_many(reset native)0 chars)8 1)tail.
Theorem generated_readToken native bs ns chars ch tail :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=0 -> meta_value native 8=0 -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=ch<256 -> ~separator ch ->
 stdin native=chars++ch::tail -> exec(funcdef_0__readToken bs ns)native=Some(tt,result native chars tail).
Proof.
 intros Hmeta Htoken Hpending Herror Hlength Hbytes Hch Hnosep Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:Frame).
 set(after:=result native chars tail).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after,result. change(17<length(memory(store_meta(put_many(reset native)0 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,reset_length. exact Hmeta. }
 assert(Herr:meta_value after 8=1).
 { unfold after,result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)8=1).
   apply meta_store_same. rewrite put_many_meta_length,reset_length. lia. }
 assert(Hdone:meta_value after 17=0).
 { unfold after,result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)17=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. reflexivity. }
 assert(Hsize:meta_value after 6=1024).
 { unfold after,result. change(meta_value(store_meta(put_many(reset native)0 chars)8 1)6=1024).
   rewrite meta_store_other by lia. rewrite put_many_count;[|rewrite reset_length;lia|rewrite reset_meta by exact Hmeta;reflexivity].
   cbn. now rewrite Hlength. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(reset native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after,result. change(tape_execution byte_body (setMachine f(reset native))
    (setMachine(setMachine f(reset native))(withInput(store_meta(put_many(reset native)0 chars)8 1)tail))).
   apply(payload_full chars (setMachine f(reset native)) 0 ch tail);cbn [machine setMachine].
   - now rewrite reset_length.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - cbn. exact Hlength.
   - now rewrite reset_token.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - rewrite reset_meta by exact Hmeta. exact Herror.
   - exact Hbytes.
   - exact Hch.
   - exact Hnosep.
   - exact Hinput. }
 rewrite(read_none_full_composition (tapeEnd byte_body) funcdef_0__tokenByte f after Hmeta Hpending Herror Htape Hafter Herr Hdone Hsize).
 reflexivity.
Qed.
End NativeTokenTooLong.
