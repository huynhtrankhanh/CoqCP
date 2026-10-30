From CoqCP Require Import Options Imperative Execution TapeEnd.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash TokenByte ReadToken SeedSeparator.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module ReadTokenLeading.
Import IndexExecution SipHashExecution TokenByteExecution ReadTokenExecution.
Lemma leading_byte (f:Frame) ch :
 (17<length(memory(machine f) arraydef_0__meta))%nat ->
 (1024<=length(memory(machine f) arraydef_0__token))%nat ->
 meta_value(machine f) 6=0 -> meta_value(machine f) 17=0 -> meta_value(machine f) 8=0 -> separator ch ->
 execLocal (byte_body ch) f=Some(KeepGoing,f).
Proof.
 intros Hmeta Htoken Hsize Hdone Herror Hsep.
 rewrite (generated_byte_body f 0 ch Hmeta Hsize ltac:(lia) Htoken ltac:(unfold separator in Hsep;lia)).
 unfold tick. rewrite bool_decide_true by exact Hsep. rewrite bool_decide_true by reflexivity.
 unfold byte_outcome. rewrite Hdone,Herror. rewrite !bool_decide_false by congruence.
 destruct f;reflexivity.
Qed.
Theorem skip_tape prefix (f:Frame) rest final :
 Forall separator prefix -> stdin(machine f)=prefix++rest ->
 (17<length(memory(machine f) arraydef_0__meta))%nat ->
 (1024<=length(memory(machine f) arraydef_0__token))%nat ->
 meta_value(machine f) 6=0 -> meta_value(machine f) 17=0 -> meta_value(machine f) 8=0 ->
 tape_execution byte_body (setMachine f (withInput (machine f) rest)) final ->
 tape_execution byte_body f final.
Proof.
 induction prefix as [|ch prefix IH] in f|-*;intros Hprefix Hin Hmeta Htoken Hsize Hdone Herror Hrun.
 - cbn [app] in Hin. replace (setMachine f (withInput (machine f) rest)) with f in Hrun;[exact Hrun|].
   destruct f as [s bs ns]. cbn [machine setMachine]. destruct s;cbn in *. now subst.
 - inversion Hprefix as [|ch' prefix' Hch Htail];subst ch' prefix'.
   set (next:=setMachine f (withInput (machine f) (prefix++rest))).
   eapply (tape_next byte_body f ch (prefix++rest) next);[exact Hin|unfold separator in Hch;lia| |].
   + unfold next. rewrite (leading_byte (setMachine f (withInput (machine f) (prefix++rest))) ch Hmeta Htoken Hsize Hdone Herror Hch). reflexivity.
   + apply (IH next Htail eq_refl Hmeta Htoken Hsize Hdone Herror).
     unfold next in *. cbn [machine setMachine] in *. exact Hrun.
Qed.
Theorem generated_readToken_leading s bs ns prefix chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  (0 < length chars <= 1024)%nat ->
  Forall (fun ch => 0 <= ch < 256 /\ ~ separator ch) chars -> separator sep ->
  Forall separator prefix -> stdin s = prefix ++ chars ++ sep :: tail ->
  exec (funcdef_0__readToken bs ns) s = Some (tt,read_result s chars tail).
Proof.
  intros Hmeta Htoken Hpending Herror Hchars Hbytes Hsep Hprefix Hin.
  unfold funcdef_0__readToken. rewrite exec_eliminate, actual_read_body.
  set (f := {|machine := s; bools := bs; nums := ns|} : Frame).
  set (after := withInput (store_meta (put_many (reset s) 0 chars) 17 1) tail).
  assert (Hafterm : (17 < length (memory after arraydef_0__meta))%nat).
  { unfold after. change (17 < length (memory (store_meta (put_many (reset s) 0 chars) 17 1%Z) arraydef_0__meta))%nat.
    now rewrite store_meta_length, put_many_meta_length, reset_length. }
  assert (Htape : execLocal (tapeEnd byte_body) (setMachine f (reset s)) = Some (tt,setMachine f after)).
  { apply tapeEnd_execution. unfold after. change
      (tape_execution byte_body (setMachine f (reset s))
        (setMachine (setMachine f (reset s))
          (withInput (store_meta (put_many (reset s) 0 chars) 17 1) tail))).
    eapply (skip_tape prefix (setMachine f (reset s)) (chars ++ sep :: tail)); cbn [machine setMachine].
    - exact Hprefix.
    - change (stdin s = prefix ++ chars ++ sep :: tail). exact Hin.
    - now rewrite reset_length.
    - rewrite reset_token. exact Htoken.
    - rewrite reset_meta by exact Hmeta. reflexivity.
    - rewrite reset_meta by exact Hmeta. reflexivity.
    - rewrite reset_meta by exact Hmeta. exact Herror.
    - pose proof (payload_tape_execution chars (setMachine f (withInput (reset s) (chars++sep::tail))) 0 sep tail
        ltac:(change (17<length(memory(reset s) arraydef_0__meta))%nat;now rewrite reset_length)
        ltac:(change (meta_value(reset s) 6=Z.of_nat 0);rewrite reset_meta by exact Hmeta;reflexivity)
        (proj2 Hchars) (proj1 Hchars)
        ltac:(change (1024<=length(memory(reset s) arraydef_0__token))%nat;rewrite reset_token;exact Htoken)
        ltac:(change (meta_value(reset s) 17=0);rewrite reset_meta by exact Hmeta;reflexivity)
        ltac:(change (meta_value(reset s) 8=0);rewrite reset_meta by exact Hmeta;exact Herror)
        Hbytes Hsep eq_refl) as Hpayload.
      cbn [machine setMachine] in Hpayload.
      rewrite put_many_input,SeedSeparator.store_input in Hpayload.
      cbn [withInput] in Hpayload. exact Hpayload. }


  assert (Hdone : meta_value after 17 = 1).
  { unfold after. change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 17 = 1).
    apply meta_store_same. rewrite put_many_meta_length, reset_length. exact Hmeta. }
  assert (Herr : meta_value after 8 = 0).
  { unfold after. change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 8 = 0).
    rewrite meta_store_other by lia. rewrite put_many_meta_other by lia. rewrite reset_meta by exact Hmeta. exact Herror. }
  assert (Hsize : meta_value after 6 <> 0).
  { unfold after. change (meta_value (store_meta (put_many (reset s) 0 chars) 17 1) 6 <> 0).
    rewrite meta_store_other by lia. rewrite put_many_count.
    - change (Z.of_nat (length chars) <> 0). intro Hz. change (Z.of_nat (length chars) = Z.of_nat 0) in Hz. apply Nat2Z.inj in Hz. lia.
    - rewrite reset_length. lia.
    - rewrite reset_meta by exact Hmeta. reflexivity. }
  rewrite (read_none_composition (tapeEnd byte_body) funcdef_0__tokenByte f after Hmeta Hpending Herror Htape Hafterm Hdone Herr Hsize).
  reflexivity.
Qed.
End ReadTokenLeading.
