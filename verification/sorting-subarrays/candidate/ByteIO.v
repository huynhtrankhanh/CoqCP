From CoqCP Require Import Options Imperative DecimalEncoding DecimalDigits.
From Stdlib Require Import Lists.List Bool.Bool Lia ZArith.ZArith Arith.PeanoNat.
From stdpp Require Import numbers list.
Require Trusted.Spec.
Import ListNotations.
Local Open Scope Z_scope.

Definition IO (A : Type) := Action BasicEffect basicEffectReturnValue A.
Definition ret {A} (x : A) : IO A := Done _ _ _ x.
Definition trap {A} : IO A := Dispatch _ _ _ Trap (fun impossible => False_rect _ impossible).
Definition get : IO Z := Dispatch _ _ _ ReadChar (fun ch => ret ch).
Definition put (ch : Z) : IO unit := Dispatch _ _ _ (WriteChar ch) (fun _ => ret tt).
Definition digitb (ch : Z) := (48 <=? ch) && (ch <? 58).
Definition spaceb (ch : Z) := (ch =? 32) || (ch =? 10) || (ch =? 13) || (ch =? 9).
Definition eof := (2^64-1)%Z.

(* Every append is checked before recursion, so even malformed streams cannot
   make the extracted reader accumulate an unbounded integer. *)
Fixpoint read_rest (fuel : nat) (value : Z) : IO Z :=
  match fuel with
  | O => trap
  | S fuel => get >>= fun ch =>
      if digitb ch then
        let next := 10 * value + ch - 48 in
        if next <=? 1000000000 then read_rest fuel next else trap
      else if spaceb ch || (ch =? eof) then ret value else trap
  end.
Definition read_first (ch : Z) : IO Z :=
  if digitb ch then read_rest 20 (ch-48) else trap.
Fixpoint read_start (fuel : nat) : IO Z :=
  match fuel with
  | O => trap
  | S fuel => get >>= fun ch =>
      if spaceb ch then read_start fuel else
      if ch =? 45 then get >>= fun first => read_first first >>= fun n => ret (-n)
      else read_first ch
  end.
Definition read_integer := read_start 16.

Fixpoint write_bytes (bytes : list Z) : IO unit :=
  match bytes with [] => ret tt | ch :: rest => put ch >>= fun _ => write_bytes rest end.

Lemma run_bind {A B} (code : IO A) (next : A -> IO B) input output :
  runIO (code >>= next) input output =
  match runIO code input output with
  | None => None
  | Some (value, remaining, written) => runIO (next value) remaining written
  end.
Proof.
  induction code as [value|e cont IH] in input, output |- *; [reflexivity|].
  destruct e; cbn [bind runIO]; try reflexivity.
  - apply IH.
  - destruct input; apply IH.
  - apply IH.
Qed.

Lemma run_write bytes input output :
  runIO (write_bytes bytes) input output = Some (tt, input, output ++ bytes).
Proof.
  induction bytes as [|ch bytes IH] in output |- *.
  - simpl. now rewrite app_nil_r.
  - cbn [write_bytes put bind runIO ret]. rewrite IH, <- app_assoc. reflexivity.
Qed.

Lemma digitb_valid ch : decimalDigit ch -> digitb ch = true.
Proof. unfold decimalDigit, digitb. intros H. apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.
Lemma digit_not_space ch : decimalDigit ch -> spaceb ch = false.
Proof.
  unfold decimalDigit, spaceb. intro H. repeat rewrite orb_false_iff.
  repeat split; apply Z.eqb_neq; lia.
Qed.
Lemma digit_not_minus ch : decimalDigit ch -> (ch =? 45) = false.
Proof. unfold decimalDigit. intro H. apply Z.eqb_neq. lia. Qed.
Lemma delimiter_digit sep : spaceb sep = true -> digitb sep = false.
Proof.
  unfold spaceb, digitb. rewrite !orb_true_iff. intros [[[H|H]|H]|H];
    apply Z.eqb_eq in H; subst sep; reflexivity.
Qed.

Lemma read_rest_correct fuel digits value sep rest out :
  (length digits < fuel)%nat -> Forall decimalDigit digits ->
  0 <= value -> decodeDigits digits value <= 1000000000 -> spaceb sep = true ->
  runIO (read_rest fuel value) (digits ++ sep :: rest) out =
    Some (decodeDigits digits value, rest, out).
Proof.
  revert fuel value. induction digits as [|ch digits IH]; intros fuel value Hlen Hd Hv Hbound Hsep.
  - destruct fuel; [simpl in Hlen; lia|]. cbn [read_rest get bind runIO ret List.app decodeDigits fold_left].
    rewrite delimiter_digit by exact Hsep. rewrite Hsep. reflexivity.
  - inversion Hd as [|? ? Hch Hds]. destruct fuel; [simpl in Hlen; lia|].
    cbn [read_rest get bind runIO ret List.app]. rewrite digitb_valid by exact Hch.
    set (next := 10 * value + ch - 48).
    assert (Hnext : 0 <= next) by (unfold next, decimalDigit in *; lia).
    assert (Hupper : next <= 1000000000).
    { pose proof (decodeDigits_ge digits next Hds Hnext) as Hge. unfold next in *. exact (Z.le_trans _ _ _ Hge Hbound). }
    rewrite (proj2 (Z.leb_le _ _) Hupper). apply IH; try assumption; simpl in Hlen; lia.
Qed.

Lemma read_first_correct digits n sep rest out :
  digits <> [] -> (length digits <= 20)%nat -> Forall decimalDigit digits ->
  decodeDigits digits 0 = n -> 0 <= n <= 1000000000 -> spaceb sep = true ->
  runIO (get >>= read_first) (digits ++ sep :: rest) out = Some (n, rest, out).
Proof.
  intros Hne Hlen Hd Hdecode Hn Hsep. destruct digits as [|ch digits]; [contradiction|].
  inversion Hd as [|? ? Hch Hds]. cbn [get bind runIO read_first ret List.app].
  unfold read_first. rewrite digitb_valid by exact Hch.
  rewrite read_rest_correct.
  - change (decodeDigits digits (ch-48) = n) in Hdecode. now rewrite Hdecode.
  - simpl in Hlen. lia.
  - exact Hds.
  - unfold decimalDigit in Hch. lia.
  - change (decodeDigits digits (ch-48) = n) in Hdecode. rewrite Hdecode. lia.
  - exact Hsep.
Qed.

Lemma magnitude_bound x : -1000000000 <= x <= 1000000000 ->
  (Z.to_nat (Z.abs x) < 2^64)%nat.
Proof.
  intro H. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_pow, Z2Nat.id by apply Z.abs_nonneg.
  change (Z.abs x < 18446744073709551616). pose proof (Z.abs_spec x). lia.
Qed.

Lemma read_integer_correct x sep rest out :
  -1000000000 <= x <= 1000000000 -> spaceb sep = true ->
  runIO read_integer (Trusted.Spec.word x sep ++ rest) out = Some (x, rest, out).
Proof.
  intros Hx Hsep. unfold Trusted.Spec.word, Trusted.Spec.signed_bytes. rewrite <- app_assoc.
  destruct (x <? 0) eqn:E.
  - apply Z.ltb_lt in E.
    set (n := Z.to_nat (-x)).
    assert (Nbound : (n < 2^64)%nat).
    { unfold n. replace (-x) with (Z.abs x) by (rewrite Z.abs_neq; lia). now apply magnitude_bound. }
    assert (Dn := decimalBytes_valid n).
    assert (Decode := decimalBytes_decode n Nbound).
    assert (Len := decimalBytes_length n).
    assert (Nonempty := decimalBytes_nonempty n Nbound).
    assert (Nz : Z.of_nat n = -x) by (unfold n; rewrite Z2Nat.id; lia).
    cbn [read_integer read_start get bind runIO spaceb ret List.app].
    change (runIO ((get >>= read_first) >>= fun value => ret (-value))
      (decimalBytes n ++ sep :: rest) out = Some (x, rest, out)).
    rewrite run_bind, read_first_correct with (n := -x); try assumption; try lia.
    change (Some (- -x, rest, out) = Some (x, rest, out)). now rewrite Z.opp_involutive.
  - apply Z.ltb_ge in E. set (n := Z.to_nat x).
    assert (Nbound : (n < 2^64)%nat).
    { unfold n. replace x with (Z.abs x) at 1 by (rewrite Z.abs_eq; lia). now apply magnitude_bound. }
    assert (Dn := decimalBytes_valid n).
    assert (Decode := decimalBytes_decode n Nbound).
    assert (Len := decimalBytes_length n).
    assert (Nonempty := decimalBytes_nonempty n Nbound).
    assert (Nz : Z.of_nat n = x) by (unfold n; rewrite Z2Nat.id; lia).
    destruct (decimalBytes n) as [|ch digits] eqn:B; [contradiction|].
    inversion Dn as [|? ? Hch Hds].
    cbn [read_integer read_start get bind runIO ret List.app].
    rewrite digit_not_space, digit_not_minus by exact Hch.
    change (runIO (get >>= read_first) ((ch :: digits) ++ sep :: rest) out = Some (x, rest, out)).
    apply read_first_correct; try assumption; try discriminate; lia.
Qed.
