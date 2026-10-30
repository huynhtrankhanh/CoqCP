From CoqCP Require Import Options Imperative Execution TapeEnd InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadNat ReadTokenLeading ReadTokenPendingLeading NativeMissingNumberEOF.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NativePendingWhitespaceEOF.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadTokenPendingLeading.
Lemma read_pending_empty_composition tape_proc byte_proc (f : Frame) ch after :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 15 = ch + 1 -> 0 <= ch < 256 -> separator ch ->
  meta_value (machine f) 8 = 0 ->
  exec (byte_proc (fun _ => false) (byte_arguments ch)) (reset (machine f)) = Some (tt,reset (machine f)) ->
  execLocal tape_proc (setMachine f (store_meta (reset (machine f)) 15 0)) = Some (tt,setMachine f after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  meta_value after 17 = 0 -> meta_value after 8 = 0 -> meta_value after 6 = 0 ->
  execLocal (read_with tape_proc byte_proc) f = Some (tt,setMachine f (store_meta after 7 1)).
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

Definition token_result native := store_meta(withInput(pending_base native)[])7 1.
Theorem generated_token native bs ns ch prefix :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> separator ch -> Forall separator prefix -> stdin native=prefix ->
 exec(funcdef_0__readToken bs ns)native=Some(tt,token_result native).
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hsep Hprefix Hinput.
 unfold funcdef_0__readToken. rewrite exec_eliminate,actual_read_body.
 set(f:={|machine:=native;bools:=bs;nums:=ns|}:ReadTokenExecution.Frame).
 set(after:=withInput(pending_base native)[]).
 assert(Htape:execLocal(tapeEnd byte_body)(setMachine f(pending_base native))=Some(tt,setMachine f after)).
 { apply tapeEnd_execution. unfold after.
   eapply(ReadTokenLeading.skip_tape prefix (setMachine f(pending_base native)) []);cbn [machine setMachine].
   - exact Hprefix.
   - change(stdin native=prefix++[]). now rewrite app_nil_r.
   - now rewrite pending_base_length.
   - now rewrite pending_base_token.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   - rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
   - apply tape_eof. reflexivity. }
 assert(Hafter:(17<length(memory after arraydef_0__meta))%nat).
 { unfold after. change(17<length(memory(pending_base native)arraydef_0__meta))%nat. now rewrite pending_base_length. }
 assert(Hdone:meta_value after 17=0) by (unfold after;change(meta_value(pending_base native)17=0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity).
 assert(Herr:meta_value after 8=0) by (unfold after;change(meta_value(pending_base native)8=0);rewrite pending_base_meta by (try exact Hmeta;lia);exact Herror).
 assert(Hsize:meta_value after 6=0) by (unfold after;change(meta_value(pending_base native)6=0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity).
 assert(Hbyte:exec(funcdef_0__tokenByte(fun _=>false)(byte_arguments ch))(reset native)=Some(tt,reset native)).
 { rewrite (generated_tokenByte (reset native) (fun _=>false) (byte_arguments ch) 0).
   - unfold tick. rewrite bool_decide_true by exact Hsep. rewrite bool_decide_true by reflexivity. reflexivity.
   - now rewrite reset_length.
   - rewrite reset_meta by exact Hmeta. reflexivity.
   - lia.
   - now rewrite reset_token.
   - exact Hch. }
 rewrite(read_pending_empty_composition (tapeEnd byte_body) funcdef_0__tokenByte f ch after Hmeta Hpending Hch Hsep Herror Hbyte Htape Hafter Hdone Herr Hsize).
 reflexivity.
Qed.
Definition number_result native := store_meta(token_result native)11 0.
Theorem generated_number native bs ns ch prefix observations :
 (17<length(memory native arraydef_0__meta))%nat -> (1024<=length(memory native arraydef_0__token))%nat ->
 meta_value native 15=ch+1 -> meta_value native 8=0 -> 0<=ch<256 -> separator ch -> Forall separator prefix -> stdin native=prefix ->
 execObserved(funcdef_0__readNat bs ns)(native,observations)=Some(tt,(number_result native,observations)) /\
 meta_value(number_result native)14=0 /\ meta_value(number_result native)11=0 /\ meta_value(number_result native)7=1 /\
 meta_value(number_result native)6=0 /\ meta_value(number_result native)8=0 /\ stdin(number_result native)=[] /\
 stdout(number_result native)=stdout native /\ (17<length(memory(number_result native)arraydef_0__meta))%nat.
Proof.
 intros Hmeta Htoken Hpending Herror Hch Hsep Hprefix Hinput.
 assert(Hreader:exec(funcdef_0__readToken(fun _=>false)(fun _=>0))native=Some(tt,token_result native)).
 { now apply(generated_token native (fun _=>false)(fun _=>0)ch prefix). }
 assert(Hlength:(17<length(memory(token_result native)arraydef_0__meta))%nat).
 { unfold token_result. rewrite store_meta_length. change(17<length(memory(pending_base native)arraydef_0__meta))%nat. now rewrite pending_base_length. }
 assert(Hvalid:meta_value(token_result native)14=0).
 { unfold token_result. rewrite meta_store_other by lia. change(meta_value(pending_base native)14=0).
   rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity. }
 assert(Hrun:exec(funcdef_0__readNat bs ns)native=Some(tt,number_result native)).
 { unfold funcdef_0__readNat. rewrite exec_eliminate,ReadNatExecution.actual_body.
   rewrite(NativeMissingNumberEOF.invalid_composition funcdef_0__readToken ReadNatExecution.digit_loop
     {|machine:=native;bools:=bs;nums:=ns|} (token_result native) Hreader ltac:(lia) Hvalid). reflexivity. }
 split;[now apply ReadNatExecution.generated_readNat_observed|].
 unfold number_result. repeat rewrite meta_store_other by lia. split;[exact Hvalid|].
 split;[apply meta_store_same;lia|].
 unfold token_result. repeat rewrite meta_store_other by lia. split.
 - apply meta_store_same. change(7<length(memory(pending_base native)arraydef_0__meta))%nat. rewrite pending_base_length. lia.
 - split.
   + repeat rewrite meta_store_other by lia. change(meta_value(pending_base native)6=0). rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
   + split.
     * repeat rewrite meta_store_other by lia. change(meta_value(pending_base native)8=0). rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
     * split;[reflexivity|]. split;[reflexivity|].
       rewrite !store_meta_length. change(17<length(memory(pending_base native)arraydef_0__meta))%nat. now rewrite pending_base_length.
Qed.
End NativePendingWhitespaceEOF.
