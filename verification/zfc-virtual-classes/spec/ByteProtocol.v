From CoqCP Require Import Options.
From Stdlib Require Import Lists.List ZArith.ZArith Bool.Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** A standalone lexical specification for the byte stream. A token ends at
    the first separator after it starts. That separator is consumed. When the
    1025th nonseparator byte arrives, it is consumed and tokenization fails.
    EOF can terminate the final nonempty token without a separator. *)
Module ByteProtocol.
Definition maximum := 18446744073709551615.
Definition separator (byte:Z) : bool :=
 Z.eqb byte 32 || Z.eqb byte 9 || Z.eqb byte 10 || Z.eqb byte 13.
Definition byte_stream (bytes:list Z) := Forall (fun byte=>0<=byte<256) bytes.
Inductive token_result :=
 | end_of_input
 | token (bytes remaining:list Z) (ended_at_eof:bool)
 | token_too_long (remaining:list Z).
Fixpoint scan_token (reversed:list Z) (input:list Z) : token_result :=
 match input with
 | []=>match reversed with []=>end_of_input | _=>token (rev reversed) [] true end
 | byte::remaining=>
   if separator byte then
     match reversed with []=>scan_token [] remaining | _=>token (rev reversed) remaining false end
   else if Nat.eqb (length reversed) 1024 then token_too_long remaining
        else scan_token (byte::reversed) remaining
 end.
Definition read_token input := scan_token [] input.

(** Decimal conversion checks each byte and then checked multiplication and
    addition, in order. Leading zeroes are valid. *)
Inductive number_error := bad_digit | overflow.
Inductive number_result := number (value:Z) | number_error_result (error:number_error).
Fixpoint digits (acc:Z) (bytes:list Z) : number_result :=
 match bytes with
 | []=>number acc
 | byte::tail=>
    if (48<=?byte) && (byte<=?57) then
      let digit:=byte-48 in
      if acc <=? (maximum-digit)/10 then digits (10*acc+digit) tail
      else number_error_result overflow
    else number_error_result bad_digit
 end.
Definition decode_number bytes := match bytes with
 | []=>number_error_result bad_digit | _=>digits 0 bytes end.
Inductive read_number_result :=
 | number_missing
 | number_too_long (remaining:list Z)
 | number_invalid (error:number_error) (remaining:list Z) (ended_at_eof:bool)
 | number_token (value:Z) (remaining:list Z) (ended_at_eof:bool).
Definition read_number input := match read_token input with
 | end_of_input=>number_missing
 | token_too_long tail=>number_too_long tail
 | token bytes tail ended=>match decode_number bytes with
    | number value=>number_token value tail ended
    | number_error_result error=>number_invalid error tail ended end
 end.
Lemma digits_bounded acc bytes value : 0<=acc<=maximum -> digits acc bytes=number value -> 0<=value<=maximum.
Proof.
 induction bytes as [|byte tail IH] in acc|-*;intros Hacc Hrun;cbn [digits] in Hrun.
 - inversion Hrun;subst;exact Hacc.
 - destruct ((48<=?byte)&&(byte<=?57)) eqn:Hdigit;[|discriminate].
   apply Bool.andb_true_iff in Hdigit as [Hlow Hhigh]. apply Z.leb_le in Hlow,Hhigh.
   destruct (acc <=? (maximum-(byte-48))/10) eqn:Hroom;[|discriminate].
   apply Z.leb_le in Hroom. apply IH with (acc:=10*acc+(byte-48));[|exact Hrun].
   unfold maximum in *. split;[lia|].
   assert (Hdiv:10*((18446744073709551615-(byte-48))/10)<=18446744073709551615-(byte-48)).
   { apply Z.mul_div_le;lia. }
   nia.
Qed.
Theorem decode_number_bounded bytes value : decode_number bytes=number value -> 0<=value<=maximum.
Proof.
 destruct bytes as [|byte tail];[discriminate|]. cbn [decode_number]. intro H.
 exact(digits_bounded 0 (byte::tail) value ltac:(unfold maximum;lia) H).
Qed.
Theorem read_number_bounded input value remaining ended :
 read_number input=number_token value remaining ended -> 0<=value<=maximum.
Proof.
 unfold read_number. destruct (read_token input) as [|bytes tail eof|tail];try discriminate.
 destruct (decode_number bytes) as [numberValue|error] eqn:Hdecode;try discriminate.
 intro Hrun. inversion Hrun;subst. exact(decode_number_bounded bytes value Hdecode).
Qed.
Lemma scan_token_valid reversed input bytes remaining ended :
 (length reversed<=1024)%nat -> scan_token reversed input=token bytes remaining ended ->
 bytes<>[] /\ (length bytes<=1024)%nat.
Proof.
 induction input as [|byte tail IH] in reversed|-*;intros Hlength Hrun;cbn [scan_token] in Hrun.
 - destruct reversed as [|head rest];[discriminate|]. inversion Hrun;subst.
   split;[intro Hnil;apply (f_equal (@length Z)) in Hnil;cbn [rev] in Hnil;rewrite length_app in Hnil;cbn in Hnil;lia|].
   cbn [rev];rewrite length_app,length_rev;cbn in *;lia.
 - destruct(separator byte) eqn:Hseparator.
   + destruct reversed as [|head rest].
     * eapply (IH []);[cbn;lia|exact Hrun].
     * inversion Hrun;subst. split;[intro Hnil;apply (f_equal (@length Z)) in Hnil;cbn [rev] in Hnil;rewrite length_app in Hnil;cbn in Hnil;lia|].
       cbn [rev];rewrite length_app,length_rev;cbn in *;lia.
   + destruct(Nat.eqb (length reversed) 1024) eqn:Hfull;[discriminate|].
     apply Nat.eqb_neq in Hfull. eapply (IH (byte::reversed));[cbn;lia|exact Hrun].
Qed.
Theorem read_token_valid input bytes remaining ended :
 read_token input=token bytes remaining ended -> bytes<>[] /\ (length bytes<=1024)%nat.
Proof. unfold read_token. apply scan_token_valid. cbn;lia. Qed.
Definition token_remaining result := match result with
 | end_of_input=>[] | token _ remaining _=>remaining | token_too_long remaining=>remaining end.
Lemma scan_token_remaining reversed input :
 exists consumed,input=consumed++token_remaining(scan_token reversed input).
Proof.
 induction input as [|byte tail IH] in reversed|-*;cbn [scan_token].
 - destruct reversed;exists [];reflexivity.
 - destruct(separator byte);[destruct reversed as [|head rest]|destruct(Nat.eqb (length reversed) 1024)].
   + destruct(IH []) as [consumed Hconsumed]. exists(byte::consumed). change(byte::tail=byte::(consumed++token_remaining(scan_token [] tail))). now f_equal.
   + exists [byte]. reflexivity.
   + exists [byte]. reflexivity.
   + destruct(IH (byte::reversed)) as [consumed Hconsumed]. exists(byte::consumed). change(byte::tail=byte::(consumed++token_remaining(scan_token (byte::reversed) tail))). now f_equal.
Qed.
Theorem read_token_remaining input :
 exists consumed,input=consumed++token_remaining(read_token input).
Proof. unfold read_token. apply scan_token_remaining. Qed.
Definition decimal_value bytes := fold_left (fun acc byte=>10*acc+(byte-48)) bytes 0.
Lemma digits_value acc bytes value : digits acc bytes=number value ->
 value=fold_left (fun running byte=>10*running+(byte-48)) bytes acc.
Proof.
 induction bytes as [|byte tail IH] in acc|-*;cbn [digits fold_left];intro H.
 - now inversion H.
 - destruct ((48<=?byte)&&(byte<=?57));[|discriminate].
   destruct (acc <=? (maximum-(byte-48))/10);[|discriminate].
   now apply IH.
Qed.
Theorem decode_number_value bytes value : decode_number bytes=number value ->
 bytes<>[] /\ value=decimal_value bytes.
Proof.
 destruct bytes as [|byte tail];[discriminate|]. cbn [decode_number]. intro H.
 split;[discriminate|]. unfold decimal_value. exact(digits_value 0 (byte::tail) value H).
Qed.
Lemma separator_spec byte : separator byte=true <-> byte=32 \/ byte=9 \/ byte=10 \/ byte=13.
Proof. unfold separator. rewrite !Bool.orb_true_iff,!Z.eqb_eq. tauto. Qed.
Lemma final_token_eof byte : separator byte=false -> read_token [byte]=token [byte] [] true.
Proof. intro H. unfold read_token. cbn [scan_token]. rewrite H. reflexivity. Qed.
Lemma zero_is_zero : decode_number [48]=number 0.
Proof. reflexivity. Qed.
Lemma max_is_valid : decode_number [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;53]=number maximum.
Proof. vm_compute. reflexivity. Qed.
Lemma max_plus_one_overflows : decode_number [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;54]=number_error_result overflow.
Proof. vm_compute. reflexivity. Qed.
End ByteProtocol.
