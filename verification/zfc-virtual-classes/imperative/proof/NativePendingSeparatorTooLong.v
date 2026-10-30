From CoqCP Require Import Options Imperative Execution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenLeading ReadTokenPendingLeading SeedSeparator NativeTokenTooLong.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingSeparatorTooLong.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadTokenPendingLeading.
Lemma read_pending_full_composition tape_proc byte_proc (f : Frame) ch after :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 15 = ch + 1 -> 0 <= ch < 256 -> separator ch ->
  meta_value (machine f) 8 = 0 ->
  exec (byte_proc (fun _ => false) (byte_arguments ch)) (reset (machine f)) = Some (tt,reset (machine f)) ->
  execLocal tape_proc (setMachine f (store_meta (reset (machine f)) 15 0)) = Some (tt,setMachine f after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  meta_value after 17 = 0 -> meta_value after 8 = 1 -> meta_value after 6 = 1024 ->
  execLocal (read_with tape_proc byte_proc) f = Some (tt,setMachine f after).
Proof.
  intros Hlength Hpending Hch Hsep Herror Hbyte Htape Hafter Hdone Herr Hsize.
  destruct f as [s bs ns]. cbn [machine] in *.
  assert (Hcoerce : coerceInt (ch + 1 - 1) 64 = ch).
  { replace (ch + 1 - 1) with ch by lia. apply coerce_word. unfold word, maximum. lia. }
  unfold read_with. unfold reset in Hbyte. unfold byte_arguments in Hbyte.
  unfold reset in Htape. cbv beta iota zeta delta [machine setMachine bools nums] in Htape.
  repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
    |rewrite local_put_meta by (cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite put_meta_length |rewrite reset_length]; lia)
    |rewrite local_read_meta by (cbn [machine setMachine]; repeat first [rewrite store_meta_length |rewrite put_meta_length |rewrite reset_length]; lia)
    |rewrite Htape |rewrite Hbyte |rewrite Hcoerce
    |rewrite put_byte_meta_other by lia
    |rewrite meta_store_other by lia |rewrite meta_store_same by (repeat first [rewrite store_meta_length |rewrite put_meta_length]; lia)
    |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr |rewrite Hsize
    |progress replace (Z.to_nat 7) with 7%nat by reflexivity
    |progress replace (Z.to_nat 17) with 17%nat by reflexivity
    |progress replace (Z.to_nat 15) with 15%nat by reflexivity
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by (try congruence; lia) |rewrite (bool_decide_false P) by (try congruence; lia)] end
    |progress cbn [subInt bind optionBind machine setMachine fst snd shortCircuitAnd]
    |progress cbv beta iota zeta delta [machine setMachine bools nums]
  ]. reflexivity.
Qed.

Definition result native chars tail := withInput(store_meta(put_many(pending_base native)0 chars)8 1)tail.
Theorem generated_readToken native bs ns initial prefix chars ch tail :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=initial+1 -> meta_value native 8=0 -> 0<=initial<256 -> separator initial -> length chars=1024%nat ->
 Forall(fun x=>0<=x<256 /\ ~separator x)chars -> 0<=ch<256 -> ~separator ch ->
 Forall TokenByteExecution.separator prefix -> stdin native=prefix++chars++ch::tail -> exec(funcdef_0__readToken bs ns)native=Some(tt,result native chars tail).
Proof.
 intros Hmeta Htoken Hpending Herror Hinitial Hsep Hlength Hbytes Hch Hnosep Hprefix Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:Frame).
 set(after:=result native chars tail).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after,result. change(17<length(memory(store_meta(put_many(pending_base native)0 chars)8 1%Z)arraydef_0__meta))%nat.
   rewrite store_meta_length,put_many_meta_length,pending_base_length. exact Hmeta. }
 assert(Herr:meta_value after 8=1).
 { unfold after,result. change(meta_value(store_meta(put_many(pending_base native)0 chars)8 1)8=1).
   apply meta_store_same. rewrite put_many_meta_length,pending_base_length. lia. }
 assert(Hdone:meta_value after 17=0).
 { unfold after,result. change(meta_value(store_meta(put_many(pending_base native)0 chars)8 1)17=0).
   rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Hsize:meta_value after 6=1024).
 { unfold after,result. change(meta_value(store_meta(put_many(pending_base native)0 chars)8 1)6=1024).
   rewrite meta_store_other by lia. rewrite put_many_count;[|rewrite pending_base_length;lia|rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity].
   cbn. now rewrite Hlength. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(pending_base native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after,result. change(tape_execution byte_body (setMachine f(pending_base native))
    (setMachine(setMachine f(pending_base native))(withInput(store_meta(put_many(pending_base native)0 chars)8 1)tail))).
   eapply(ReadTokenLeading.skip_tape prefix (setMachine f(pending_base native)) (chars++ch::tail));cbn [machine setMachine].
   - exact Hprefix.
   - change(stdin native=prefix++chars++ch::tail). exact Hinput.
   - now rewrite pending_base_length.
   - now rewrite pending_base_token.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   - rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
   - pose proof(NativeTokenTooLong.payload_full chars (setMachine f(withInput(pending_base native)(chars++ch::tail))) 0 ch tail
      ltac:(change(17<length(memory(pending_base native)arraydef_0__meta))%nat;now rewrite pending_base_length)
      ltac:(change(meta_value(pending_base native)6=Z.of_nat 0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity)
      ltac:(cbn;exact Hlength)
      ltac:(change(1024<=length(memory(pending_base native)arraydef_0__token))%nat;now rewrite pending_base_token)
      ltac:(change(meta_value(pending_base native)17=0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity)
      ltac:(change(meta_value(pending_base native)8=0);rewrite pending_base_meta by (try exact Hmeta;lia);exact Herror)
      Hbytes Hch Hnosep eq_refl) as Hpayload.
     cbn [machine setMachine] in Hpayload. rewrite put_many_input,SeedSeparator.store_input in Hpayload.
     cbn [withInput] in Hpayload. exact Hpayload. }
 assert(Hbyte:exec(funcdef_0__tokenByte(fun _=>false)(byte_arguments initial))(reset native)=Some(tt,reset native)).
 { rewrite (generated_tokenByte (reset native) (fun _=>false) (byte_arguments initial) 0).
   - unfold tick. rewrite bool_decide_true by exact Hsep. rewrite bool_decide_true by reflexivity. reflexivity.
   - now rewrite reset_length.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - lia.
   - now rewrite reset_token.
   - exact Hinitial. }
 rewrite(read_pending_full_composition (tapeEnd byte_body) funcdef_0__tokenByte f initial after Hmeta Hpending Hinitial Hsep Herror Hbyte Htape Hafter Hdone Herr Hsize).
 reflexivity.
Qed.
End NativePendingSeparatorTooLong.
