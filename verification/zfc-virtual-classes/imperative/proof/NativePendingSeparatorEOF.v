From CoqCP Require Import Options Imperative Execution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenLeading ReadTokenPendingLeading NativeReadTokenEOF.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingSeparatorEOF.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadTokenPendingLeading NativeReadTokenEOF.
Lemma read_pending_eof_composition tape_proc byte_proc (f : Frame) ch after :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 15 = ch + 1 -> 0 <= ch < 256 -> separator ch ->
  meta_value (machine f) 8 = 0 ->
  exec (byte_proc (fun _ => false) (byte_arguments ch)) (reset (machine f)) = Some (tt,reset (machine f)) ->
  execLocal tape_proc (setMachine f (store_meta (reset (machine f)) 15 0)) = Some (tt,setMachine f after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  meta_value after 17 = 0 -> meta_value after 8 = 0 -> meta_value after 6 <> 0 ->
  execLocal (read_with tape_proc byte_proc) f = Some (tt,setMachine f (store_meta(store_meta after 7 1)14 1)).
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

Definition eof_result native chars := store_meta(store_meta(withInput(put_many(pending_base native)0 chars)[])7 1)14 1.
Theorem generated native bs ns ch prefix chars :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> separator ch -> (0<length chars<=1024)%nat ->
 Forall(fun ch=>0<=ch<256 /\ ~separator ch)chars -> Forall separator prefix -> stdin native=prefix++chars ->
 exec(funcdef_0__readToken bs ns)native=Some(tt,eof_result native chars).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hsep Hlength Hbytes Hprefix Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:Frame).
 set(after:=withInput(put_many(pending_base native)0 chars)[]).
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after. change(17<length(memory(put_many(pending_base native)0 chars)arraydef_0__meta))%nat. now rewrite put_many_meta_length,pending_base_length. }
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(pending_base native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after. change(tape_execution byte_body (setMachine f(pending_base native))
    (setMachine(setMachine f(pending_base native))(withInput(put_many(pending_base native)0 chars)[]))).
   eapply (ReadTokenLeading.skip_tape prefix (setMachine f(pending_base native)) chars);cbn [machine setMachine].
   - exact Hprefix.
   - change(stdin native=prefix++chars). exact Hinput.
   - now rewrite pending_base_length.
   - now rewrite pending_base_token.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   - rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
   - pose proof(payload_eof chars (setMachine f(withInput(pending_base native)chars)) 0
       ltac:(change(17<length(memory(pending_base native)arraydef_0__meta))%nat;now rewrite pending_base_length)
       ltac:(change(meta_value(pending_base native)6=Z.of_nat 0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity)
       (proj2 Hlength)
       ltac:(change(1024<=length(memory(pending_base native)arraydef_0__token))%nat;now rewrite pending_base_token)
       ltac:(change(meta_value(pending_base native)17=0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity)
       ltac:(change(meta_value(pending_base native)8=0);rewrite pending_base_meta by (try exact Hmeta;lia);exact Herror)
       Hbytes eq_refl) as Hpayload.
     cbn [machine setMachine] in Hpayload. rewrite put_many_input in Hpayload.
     cbn [withInput] in Hpayload. exact Hpayload. }
 assert(Hdone:meta_value after 17=0).
 { unfold after. change(meta_value(put_many(pending_base native)0 chars)17=0). rewrite put_many_meta_other by lia. rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Herr:meta_value after 8=0).
 { unfold after. change(meta_value(put_many(pending_base native)0 chars)8=0). rewrite put_many_meta_other by lia. rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror. }
 assert(Hsize:meta_value after 6<>0).
 { unfold after. change(meta_value(put_many(pending_base native)0 chars)6<>0). rewrite put_many_count.
   - change(Z.of_nat(length chars)<>0). intro Hzero. change(Z.of_nat(length chars)=Z.of_nat 0) in Hzero. apply Nat2Z.inj in Hzero. lia.
   - rewrite pending_base_length. lia.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Hbyte:exec(funcdef_0__tokenByte(fun _=>false)(byte_arguments ch))(reset native)=Some(tt,reset native)).
 { rewrite (generated_tokenByte (reset native) (fun _=>false) (byte_arguments ch) 0).
   - unfold tick. rewrite bool_decide_true by exact Hsep. rewrite bool_decide_true by reflexivity. reflexivity.
   - now rewrite reset_length.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - lia.
   - now rewrite reset_token.
   - exact Hch. }
 rewrite(read_pending_eof_composition (tapeEnd byte_body) funcdef_0__tokenByte f ch after Hmeta Hpending Hch Hsep Herror Hbyte Htape Hafter Hdone Herr Hsize).
 reflexivity.
Qed.
End NativePendingSeparatorEOF.
