From CoqCP Require Import Options Imperative Execution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken ReadTokenLeading SeedSeparator.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ReadTokenPendingLeading.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution ReadTokenLeading.
Lemma read_pending_separator_composition tape_proc byte_proc (f : Frame) ch after :
  (17 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 15 = ch + 1 -> 0 <= ch < 256 -> separator ch ->
  meta_value (machine f) 8 = 0 ->
  exec (byte_proc (fun _ => false) (byte_arguments ch)) (reset (machine f)) = Some (tt,reset (machine f)) ->
  execLocal tape_proc (setMachine f (store_meta (reset (machine f)) 15 0)) = Some (tt,setMachine f after) ->
  (17 < length (memory after arraydef_0__meta))%nat ->
  meta_value after 17 = 1 -> meta_value after 8 = 0 -> meta_value after 6 <> 0 ->
  execLocal (read_with tape_proc byte_proc) f = Some (tt,setMachine f (store_meta after 14 1)).
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
    |rewrite Hpending |rewrite Herror |rewrite Hdone |rewrite Herr
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

Definition pending_base s := store_meta (reset s) 15 0.
Lemma pending_base_length s : length(memory(pending_base s) arraydef_0__meta)=length(memory s arraydef_0__meta).
Proof. unfold pending_base. now rewrite store_meta_length,reset_length. Qed.
Lemma pending_base_token s : memory(pending_base s) arraydef_0__token=memory s arraydef_0__token.
Proof. unfold pending_base. rewrite store_meta_other by discriminate. apply reset_token. Qed.
Lemma pending_base_meta s i : (17<length(memory s arraydef_0__meta))%nat -> i<>15%nat ->
 meta_value(pending_base s) i=if bool_decide(i=6%nat \/ i=14%nat \/ i=17%nat) then 0 else meta_value s i.
Proof. intros Hmeta Hne. unfold pending_base. rewrite meta_store_other by exact Hne. now apply reset_meta. Qed.
Definition pending_separator_result s chars tail :=
 store_meta (withInput (store_meta (put_many (pending_base s) 0 chars) 17 1) tail) 14 1.
Theorem generated_pending_leading s bs ns ch prefix chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 -> 0<=ch<256 -> separator ch ->
  (0 < length chars <= 1024)%nat ->
  Forall (fun ch => 0 <= ch < 256 /\ ~ separator ch) chars -> separator sep ->
  Forall separator prefix -> stdin s = prefix ++ chars ++ sep :: tail ->
  exec (funcdef_0__readToken bs ns) s = Some (tt,pending_separator_result s chars tail).
Proof.
  intros Hmeta Htoken Hpending Herror Hch Hchsep Hchars Hbytes Hsep Hprefix Hin.
  unfold funcdef_0__readToken. rewrite exec_eliminate, actual_read_body.
  set (f := {|machine := s; bools := bs; nums := ns|} : Frame).
  set (after := withInput (store_meta (put_many (pending_base s) 0 chars) 17 1) tail).
  assert (Hafterm : (17 < length (memory after arraydef_0__meta))%nat).
  { unfold after. change (17 < length (memory (store_meta (put_many (pending_base s) 0 chars) 17 1%Z) arraydef_0__meta))%nat.
    now rewrite store_meta_length, put_many_meta_length, pending_base_length. }
  assert (Htape : execLocal (tapeEnd byte_body) (setMachine f (pending_base s)) = Some (tt,setMachine f after)).
  { apply tapeEnd_execution. unfold after. change
      (tape_execution byte_body (setMachine f (pending_base s))
        (setMachine (setMachine f (pending_base s))
          (withInput (store_meta (put_many (pending_base s) 0 chars) 17 1) tail))).
    eapply (skip_tape prefix (setMachine f (pending_base s)) (chars ++ sep :: tail)); cbn [machine setMachine].
    - exact Hprefix.
    - change (stdin s = prefix ++ chars ++ sep :: tail). exact Hin.
    - now rewrite pending_base_length.
    - rewrite pending_base_token. exact Htoken.
    - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
    - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity.
    - rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror.
    - pose proof (payload_tape_execution chars (setMachine f (withInput (pending_base s) (chars++sep::tail))) 0 sep tail
        ltac:(change (17<length(memory(pending_base s) arraydef_0__meta))%nat;now rewrite pending_base_length)
        ltac:(change (meta_value(pending_base s) 6=Z.of_nat 0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity)
        (proj2 Hchars) (proj1 Hchars)
        ltac:(change (1024<=length(memory(pending_base s) arraydef_0__token))%nat;rewrite pending_base_token;exact Htoken)
        ltac:(change (meta_value(pending_base s) 17=0);rewrite pending_base_meta by (try exact Hmeta;lia);reflexivity)
        ltac:(change (meta_value(pending_base s) 8=0);rewrite pending_base_meta by (try exact Hmeta;lia);exact Herror)
        Hbytes Hsep eq_refl) as Hpayload.
      cbn [machine setMachine] in Hpayload.
      rewrite put_many_input,SeedSeparator.store_input in Hpayload.
      cbn [withInput] in Hpayload. exact Hpayload. }


  assert (Hdone : meta_value after 17 = 1).
  { unfold after. change (meta_value (store_meta (put_many (pending_base s) 0 chars) 17 1) 17 = 1).
    apply meta_store_same. rewrite put_many_meta_length, pending_base_length. exact Hmeta. }
  assert (Herr : meta_value after 8 = 0).
  { unfold after. change (meta_value (store_meta (put_many (pending_base s) 0 chars) 17 1) 8 = 0).
    rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite pending_base_meta by (try exact Hmeta;lia). exact Herror. }
  assert (Hsize : meta_value after 6 <> 0).
  { unfold after. change (meta_value (store_meta (put_many (pending_base s) 0 chars) 17 1) 6 <> 0).
    rewrite meta_store_other by lia. rewrite put_many_count.
    - change (Z.of_nat (length chars) <> 0). intro Hz. change (Z.of_nat (length chars) = Z.of_nat 0) in Hz. apply Nat2Z.inj in Hz. lia.
    - rewrite pending_base_length. lia.
    - rewrite pending_base_meta by (try exact Hmeta;lia). reflexivity. }
  assert (Hbyte:exec (funcdef_0__tokenByte (fun _=>false) (byte_arguments ch)) (reset s)=Some(tt,reset s)).
  { rewrite (generated_tokenByte (reset s) (fun _=>false) (byte_arguments ch) 0).
    - unfold tick. rewrite bool_decide_true by exact Hchsep. rewrite bool_decide_true by reflexivity. reflexivity.
    - now rewrite reset_length.
    - rewrite reset_meta by exact Hmeta. reflexivity.
    - lia.
    - now rewrite reset_token.
    - exact Hch. }
  rewrite (read_pending_separator_composition (tapeEnd byte_body) funcdef_0__tokenByte f ch after Hmeta Hpending Hch Hchsep Herror Hbyte Htape Hafterm Hdone Herr Hsize).
  reflexivity.
Qed.

Lemma result_meta_length s chars tail :
 length(memory(pending_separator_result s chars tail)arraydef_0__meta)=length(memory s arraydef_0__meta).
Proof. unfold pending_separator_result. rewrite store_meta_length. change (length(memory(store_meta(put_many(pending_base s)0 chars)17 1%Z)arraydef_0__meta)=length(memory s arraydef_0__meta)). now rewrite store_meta_length,put_many_meta_length,pending_base_length. Qed.
Lemma result_valid s chars tail : (17<length(memory s arraydef_0__meta))%nat -> meta_value(pending_separator_result s chars tail)14=1.
Proof. intro H. unfold pending_separator_result. apply meta_store_same. change (14<length(memory(store_meta(put_many(pending_base s)0 chars)17 1%Z)arraydef_0__meta))%nat. rewrite store_meta_length,put_many_meta_length,pending_base_length. lia. Qed.
Lemma result_count s chars tail : (17<length(memory s arraydef_0__meta))%nat -> meta_value(pending_separator_result s chars tail)6=Z.of_nat(length chars).
Proof. intro H. unfold pending_separator_result. rewrite meta_store_other by lia. change(meta_value(store_meta(put_many(pending_base s)0 chars)17 1%Z)6=Z.of_nat(length chars)). rewrite meta_store_other by lia. rewrite put_many_count;[reflexivity|rewrite pending_base_length;lia|rewrite pending_base_meta by (try exact H;lia);reflexivity]. Qed.
Lemma result_token_length s chars tail : length(memory(pending_separator_result s chars tail)arraydef_0__token)=length(memory s arraydef_0__token).
Proof. unfold pending_separator_result. rewrite store_meta_other by discriminate. change(length(memory(store_meta(put_many(pending_base s)0 chars)17 1%Z)arraydef_0__token)=length(memory s arraydef_0__token)). rewrite store_meta_other by discriminate. now rewrite put_many_token_length,pending_base_token. Qed.
Lemma result_token_entry s chars tail i : (i<length chars)%nat -> (length chars<=length(memory s arraydef_0__token))%nat ->
 List.nth i (memory(pending_separator_result s chars tail)arraydef_0__token) 0=List.nth i chars 0.
Proof. intros Hi Hlen. unfold pending_separator_result. rewrite store_meta_other by discriminate. change(List.nth i (memory(store_meta(put_many(pending_base s)0 chars)17 1%Z)arraydef_0__token)0=List.nth i chars 0). rewrite store_meta_other by discriminate. change(List.nth (0+i) (memory(put_many(pending_base s)0 chars)arraydef_0__token)0=List.nth i chars 0). apply put_many_entry;[exact Hi|]. now rewrite pending_base_token. Qed.
End ReadTokenPendingLeading.
