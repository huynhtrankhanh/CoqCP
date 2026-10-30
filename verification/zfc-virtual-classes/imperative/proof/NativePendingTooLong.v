From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken NativeTokenTooLong.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingTooLong.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution NativeTokenTooLong.
Lemma pending_full_composition tape_proc byte_proc (f:Frame) ch after :
 (17<length(memory(machine f)arraydef_0__meta))%nat ->
 meta_value(machine f)15=ch+1 -> 0<=ch<256 -> ~separator ch -> meta_value(machine f)8=0 ->
 exec(byte_proc (fun _=>false)(byte_arguments ch))(reset(machine f))=Some(tt,put_byte(reset(machine f))0 ch) ->
 execLocal tape_proc(setMachine f(started(machine f)ch))=Some(tt,setMachine f after) ->
 (17<length(memory after arraydef_0__meta))%nat -> meta_value after 17=0 -> meta_value after 8=1 -> meta_value after 6=1024 ->
 execLocal(read_with tape_proc byte_proc)f=Some(tt,setMachine f after).
Proof.
 intros Hlength Hpending Hch Hsep Herror Hbyte Htape Hafter Hdone Herr Hsize.
 destruct f as [s bs ns]. cbn [machine] in *.
 assert(Hcoerce:coerceInt(ch+1-1)64=ch).
 { replace(ch+1-1)with ch by lia. apply coerce_word. unfold word,maximum;lia. }
 unfold read_with. unfold reset in Hbyte. unfold byte_arguments in Hbyte.
 unfold started,reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
 repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
  |rewrite local_put_meta by (cbn [machine setMachine];repeat first [rewrite store_meta_length|rewrite put_meta_length|rewrite reset_length];lia)
  |rewrite local_read_meta by (cbn [machine setMachine];repeat first [rewrite store_meta_length|rewrite put_meta_length|rewrite reset_length];lia)
  |rewrite Htape |rewrite Hbyte |rewrite Hcoerce
  |rewrite put_byte_meta_other by lia
  |rewrite meta_store_other by lia |rewrite meta_store_same by (repeat first [rewrite store_meta_length|rewrite put_meta_length];lia)
  |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr |rewrite Hsize
  |progress replace (Z.to_nat 17) with 17%nat by reflexivity
  |progress replace (Z.to_nat 15) with 15%nat by reflexivity
  |progress replace (Z.to_nat 14) with 14%nat by reflexivity
  |progress replace (Z.to_nat 8) with 8%nat by reflexivity
  |progress replace (Z.to_nat 6) with 6%nat by reflexivity
  |match goal with |- context [bool_decide ?P] => first [rewrite (bool_decide_true P) by (try congruence;lia)|rewrite (bool_decide_false P) by (try congruence;lia)] end
  |progress cbn [subInt bind optionBind machine setMachine fst snd shortCircuitAnd]
  |progress cbv beta iota zeta delta [machine setMachine bools nums]]. reflexivity.
Qed.
Definition result native ch chars tail := withInput(store_meta(put_many(started native ch)1 chars)8 1)tail.
Theorem generated_readToken_pending s bs ns ch chars extra tail :
 (17<length(memory s arraydef_0__meta))%nat -> (1024<=length(memory s arraydef_0__token))%nat ->
 meta_value s 15=ch+1 -> meta_value s 8=0 -> 0<=ch<256 -> ~separator ch ->
 length chars=1023%nat -> Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=extra<256 -> ~separator extra ->
 stdin s=chars++extra::tail -> exec(funcdef_0__readToken bs ns)s=Some(tt,result s ch chars tail).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hnosep Hlength Hbytes Hextra Hbad Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=s;bools:=bs;nums:=ns|}:Frame).
 set(after:=result s ch chars tail).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after,result. change(17<length(memory(store_meta(put_many(started s ch)1 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,started_length. exact Hmeta. }
 assert(Herr:meta_value after 8=1).
 { unfold after,result. change(meta_value(store_meta(put_many(started s ch)1 chars)8 1)8=1).
   apply meta_store_same. rewrite put_many_meta_length,started_length. lia. }
 assert(Hdone:meta_value after 17=0).
 { unfold after,result. change(meta_value(store_meta(put_many(started s ch)1 chars)8 1)17=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. apply started_zero;[exact Hmeta|now left]. }
 assert(Hsize:meta_value after 6=1024).
 { unfold after,result. change(meta_value(store_meta(put_many(started s ch)1 chars)8 1)6=1024).
   rewrite meta_store_other by lia. rewrite put_many_count;[|rewrite started_length;lia|now apply started_count].
   change(Z.of_nat (1+length chars)=1024). rewrite Hlength. reflexivity. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(started s ch))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after,result. change(tape_execution byte_body (setMachine f(started s ch))
    (setMachine(setMachine f(started s ch))(withInput(store_meta(put_many(started s ch)1 chars)8 1)tail))).
   apply(payload_full chars (setMachine f(started s ch)) 1 extra tail);cbn [machine setMachine].
   - now rewrite started_length.
   - now apply started_count.
   - rewrite Hlength. reflexivity.
   - rewrite started_token_length. exact Htoken.
   - apply started_zero;[exact Hmeta|now left].
   - apply started_zero;[exact Hmeta|right;auto].
   - exact Hbytes.
   - exact Hextra.
   - exact Hbad.
   - exact Hinput. }
 assert(Hbyte:exec(funcdef_0__tokenByte (fun _=>false)(byte_arguments ch))(reset s)=Some(tt,put_byte(reset s)0 ch)).
 { rewrite(generated_tokenByte (reset s) (fun _=>false)(byte_arguments ch) 0).
   - rewrite tick_data by (try exact Hnosep;lia). reflexivity.
   - now rewrite reset_length.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - lia.
   - rewrite reset_token. exact Htoken.
   - exact Hch. }
 rewrite(pending_full_composition (tapeEnd byte_body) funcdef_0__tokenByte f ch after Hmeta Hpending Hch Hnosep Herror Hbyte Htape Hafter Hdone Herr Hsize). reflexivity.
Qed.
End NativePendingTooLong.
