From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow ArrayFacts SipHash InternTail TokenByte Observation ReadToken.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module ReadNatExecution.
Import IndexExecution SipHashExecution.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__readNat) withLocalVariablesReturnValue R.
Ltac nat_callback code use :=
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind _ ?next =>
      let code := eval cbn beta in (next tt) in
      lazymatch code with bind (bind _ ?branch) _ =>
        let code := eval cbn beta iota in (branch true) in
        lazymatch code with bind (bind _ ?run) _ => use run end
      end
    end
  end.
Definition digit_loop (total : Z) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__readNat_body in funcdef_0__readNat_body in
  nat_callback code ltac:(fun run => exact (run total))).
Definition digit_body (total : Z) (remaining : nat) : LocalAction LoopOutcome := ltac:(
  let code := eval unfold digit_loop in (digit_loop total) in
  let code := eval cbn beta in code in
  lazymatch code with loop _ ?body => exact (body remaining) end).
Lemma actual_digit_loop total : digit_loop total = loop (Z.to_nat total) (digit_body total).
Proof. reflexivity. Qed.
Lemma local_read_token (f : Frame) slot :
  (Z.to_nat slot < length (memory (machine f) arraydef_0__token))%nat ->
  execLocal (R := arrayType _ environment1 arraydef_0__token) (retrieve _ _ _ arraydef_0__token slot) f =
    Some (List.nth (Z.to_nat slot) (memory (machine f) arraydef_0__token) 0,f).
Proof. destruct f. intro H. cbn [retrieve execLocal localStep step]. case_decide; [|lia].
  rewrite nth_lt_default with (default := 0%Z). reflexivity. Qed.
Lemma local_get (f : Frame) name :
  execLocal (R := Z) (numberLocalGet _ _ _ name) f = Some (nums f name,f).
Proof. reflexivity. Qed.
Lemma local_set (f : Frame) name value :
  execLocal (R := unit) (numberLocalSet _ _ _ name value) f = Some (tt,setNum f name value).
Proof. reflexivity. Qed.
Lemma local_done {R} (value : R) (f : Frame) : execLocal (Done _ _ _ value) f = Some (value,f).
Proof. reflexivity. Qed.
Definition digit_frame (f : Frame) ch value :=
  setNum (setNum (setNum f vardef_0__readNat_digit ch) vardef_0__readNat_digit (ch-48)) vardef_0__readNat_value value.
Theorem generated_digit f total remaining index ch value :
  total - Z.of_nat remaining - 1 = Z.of_nat index ->
  (index < length (memory (machine f) arraydef_0__token))%nat ->
  List.nth index (memory (machine f) arraydef_0__token) 0 = ch ->
  nums f vardef_0__readNat_value = value ->
  48 <= ch <= 57 -> 0 <= value -> 10 * value + (ch - 48) <= maximum ->
  execLocal (digit_body total remaining) f = Some (KeepGoing,digit_frame f ch (10 * value + (ch-48))).
Proof.
  intros Hindex Hcapacity Hch Hvalue Hdigit Hnonnegative Hlimit.
  assert (Hraw : coerceInt ch 64 = ch) by (apply coerce_word; unfold word, maximum; lia).
  assert (Hd : coerceInt (ch-48) 64 = ch-48) by (apply coerce_word; unfold word, maximum; lia).
  assert (Hv : coerceInt (value*10) 64 = value*10) by (apply coerce_word; unfold word, maximum in *; lia).
  assert (Hsum : coerceInt (value*10+(ch-48)) 64 = 10*value+(ch-48)) by
    (replace (value*10) with (10*value) by lia; apply coerce_word; unfold word, maximum in *; lia).
  assert (Hsub : coerceInt (maximum-(ch-48)) 64 = maximum-(ch-48)) by
    (apply coerce_word; unfold word, maximum; lia).
  assert (Hdivide : value <= (maximum-(ch-48))/10).
  { apply Z.div_le_lower_bound; lia. }
  destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold digit_body. unfold maximum in Hsub, Hdivide.
  repeat first [rewrite execLocal_bind |rewrite ReadTokenExecution.exec_drop_assoc |rewrite exec_drop_lift |rewrite local_done |rewrite Hindex |progress cbn [bind optionBind fst snd]].
  rewrite (local_read_token {| machine := s; bools := bs; nums := ns |} (Z.of_nat index)).
  2: { now rewrite Nat2Z.id. }
  repeat first [rewrite execLocal_bind |rewrite ReadTokenExecution.exec_drop_assoc |rewrite exec_drop_lift
    |rewrite local_done |rewrite local_read_token by (rewrite ?Hindex, ?Nat2Z.id; exact Hcapacity)
    |rewrite local_get |rewrite local_set |rewrite Hindex |rewrite Nat2Z.id |rewrite Hch |rewrite Hraw |rewrite Hd
    |rewrite Hv |rewrite Hsum |rewrite Hsub |rewrite Hvalue
    |rewrite dropWithinLoop_1
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by lia |rewrite (bool_decide_false P) by lia] end
    |progress cbv beta iota zeta delta [bind subInt addInt multInt divIntUnsigned shortCircuitOr optionBind fst snd machine setMachine setNum nums bools Imperative.update]
    |match goal with |- context [decide ?P] => first
       [rewrite (decide_True (P := P)) by congruence |rewrite (decide_False (P := P)) by congruence] end
  ]. reflexivity.
Qed.

Fixpoint number_from value chars := match chars with
| [] => value | ch :: chars => number_from (10*value+(ch-48)) chars end.
Lemma number_from_ge value chars : 0 <= value -> Forall (fun ch => 48 <= ch <= 57) chars ->
  value <= number_from value chars.
Proof.
  induction chars as [|ch chars IH] in value |- *; [cbn; lia|].
  intros Hvalue Hchars. inversion Hchars as [|ch' chars' Hch Hrest]; subst ch' chars'.
  cbn [number_from]. pose proof (IH (10*value+(ch-48)) ltac:(lia) Hrest). lia.
Qed.
Fixpoint run_digits (f : Frame) value chars := match chars with
| [] => f | ch :: chars => run_digits (digit_frame f ch (10*value+(ch-48))) (10*value+(ch-48)) chars end.
Lemma digit_value f ch value : nums (digit_frame f ch value) vardef_0__readNat_value = value.
Proof. reflexivity. Qed.
Lemma run_machine f value chars : machine (run_digits f value chars) = machine f.
Proof. induction chars as [|ch chars IH] in f, value |- *; [reflexivity|]. cbn [run_digits]. rewrite IH. reflexivity. Qed.
Lemma run_value f value chars : nums f vardef_0__readNat_value = value ->
  nums (run_digits f value chars) vardef_0__readNat_value = number_from value chars.
Proof.
  induction chars as [|ch chars IH] in f, value |- *; [exact (fun H => H)|].
  intro H. cbn [run_digits number_from]. apply IH. apply digit_value.
Qed.
Theorem generated_digits chars f total offset value :
  (offset + length chars = total)%nat ->
  (total <= length (memory (machine f) arraydef_0__token))%nat ->
  (forall i, (i < length chars)%nat ->
    List.nth (offset+i) (memory (machine f) arraydef_0__token) 0 = List.nth i chars 0) ->
  nums f vardef_0__readNat_value = value ->
  0 <= value -> number_from value chars <= maximum -> Forall (fun ch => 48 <= ch <= 57) chars ->
  execLocal (loop (length chars) (digit_body (Z.of_nat total))) f = Some (tt,run_digits f value chars).
Proof.
  induction chars as [|ch chars IH] in f, offset, value |- *.
  - intros Htotal Hcapacity Hentries Hvalue Hpositive Hlimit Hchars. reflexivity.
  - intros Htotal Hcapacity Hentries Hvalue Hpositive Hlimit Hchars.
    inversion Hchars as [|ch' chars' Hch Hrest]; subst ch' chars'.
    assert (Hnext : 0 <= 10*value+(ch-48)) by lia.
    assert (Hbound : 10*value+(ch-48) <= maximum).
    { pose proof (number_from_ge (10*value+(ch-48)) chars Hnext Hrest). cbn [number_from] in Hlimit. lia. }
    assert (Hindex : Z.of_nat total - Z.of_nat (length chars) - 1 = Z.of_nat offset).
    { cbn [length] in Htotal. lia. }
    assert (Hcapacity' : (offset < length (memory (machine f) arraydef_0__token))%nat).
    { cbn [length] in Htotal. lia. }
    assert (Hentry : List.nth offset (memory (machine f) arraydef_0__token) 0 = ch).
    { specialize (Hentries 0%nat ltac:(cbn [length]; lia)). rewrite Nat.add_0_r in Hentries. exact Hentries. }
    cbn [length]. rewrite loop_S, execLocal_bind.
    rewrite (generated_digit f (Z.of_nat total) (length chars) offset ch value Hindex Hcapacity' Hentry Hvalue Hch Hpositive Hbound).
    cbn [optionBind fst snd run_digits]. apply (IH (digit_frame f ch (10*value+(ch-48))) (S offset) (10*value+(ch-48))).
    + cbn [length] in Htotal. lia.
    + exact Hcapacity.
    + intros i Hi. change (List.nth (S offset+i) (memory (machine f) arraydef_0__token) 0 = List.nth i chars 0).
      replace (S offset+i)%nat with (offset+S i)%nat by lia. apply (Hentries (S i)). cbn [length]. lia.
    + apply digit_value.
    + exact Hnext.
    + exact Hlimit.
    + exact Hrest.
Qed.

Definition reader_function := (varsfuncdef_0__readToken -> bool) -> (varsfuncdef_0__readToken -> Z) ->
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition body_with (reader : reader_function) (digits : Z -> LocalAction unit) : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__readNat_body in funcdef_0__readNat_body in
  nat_callback code ltac:(fun run =>
    let generalized := eval pattern funcdef_0__readToken,run in code in
    lazymatch generalized with ?family _ _ => exact (family reader digits) end)).
Lemma actual_body : funcdef_0__readNat_body = body_with funcdef_0__readToken digit_loop.
Proof. reflexivity. Qed.
Lemma read_composition reader digits (f : Frame) tokenstate after :
  exec (reader (fun _ => false) (fun _ => 0)) (machine f) = Some (tt,tokenstate) ->
  (14 < length (memory tokenstate arraydef_0__meta))%nat -> meta_value tokenstate 14 <> 0 ->
  execLocal (digits (meta_value tokenstate 6)) (setNum (setMachine f tokenstate) vardef_0__readNat_value 0) = Some (tt,after) ->
  (11 < length (memory (machine after) arraydef_0__meta))%nat ->
  execLocal (body_with reader digits) f =
    Some (tt,setMachine after (store_meta (machine after) 11 (nums after vardef_0__readNat_value))).
Proof.
  intros Hreader Hmeta Hvalid Hdigits Hafter.
  destruct f as [s bs ns]. cbn [machine] in *.
  cbv beta iota zeta delta [machine setMachine setNum nums bools] in Hdigits.
  unfold body_with.
  repeat first [rewrite execLocal_bind |rewrite execLocal_lift |rewrite local_done
    |rewrite local_get |rewrite local_set |rewrite Hreader |rewrite Hdigits
    |rewrite local_read_meta by (cbn [machine setMachine]; lia)
    |rewrite local_put_meta by (cbn [machine setMachine]; lia)
    |progress replace (Z.to_nat 14) with 14%nat by reflexivity
    |progress replace (Z.to_nat 11) with 11%nat by reflexivity
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [rewrite (bool_decide_true P) by congruence |rewrite (bool_decide_false P) by congruence] end
    |progress cbn [bind optionBind fst snd]
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools]
  ]. reflexivity.
Qed.
Definition token_number (s : Machine) chars := store_meta s 11 (number_from 0 chars).

Theorem generated_readNat_from_token s bs ns tokenstate chars :
  exec (funcdef_0__readToken (fun _ => false) (fun _ => 0)) s = Some (tt,tokenstate) ->
  (17 < length (memory tokenstate arraydef_0__meta))%nat -> meta_value tokenstate 14 <> 0 ->
  meta_value tokenstate 6 = Z.of_nat (length chars) ->
  (length chars <= length (memory tokenstate arraydef_0__token))%nat ->
  (forall i, (i < length chars)%nat -> List.nth i (memory tokenstate arraydef_0__token) 0 = List.nth i chars 0) ->
  Forall (fun ch => 48 <= ch <= 57) chars -> number_from 0 chars <= maximum ->
  exec (funcdef_0__readNat bs ns) s = Some (tt,token_number tokenstate chars).
Proof.
  intros Hreader Htmeta Htvalid Htcount Hcapacity Hentries Hdigits Hlimit.
  set (f := {| machine := s; bools := bs; nums := ns |} : Frame).
  set (start := setNum (setMachine f tokenstate) vardef_0__readNat_value 0).
  set (after := run_digits start 0 chars).
  assert (Hrun : execLocal (digit_loop (meta_value tokenstate 6)) start = Some (tt,after)).
  { rewrite Htcount, actual_digit_loop, Nat2Z.id. apply (generated_digits chars start (length chars) 0 0).
    - reflexivity.
    - exact Hcapacity.
    - exact Hentries.
    - reflexivity.
    - lia.
    - exact Hlimit.
    - exact Hdigits. }
  assert (Hmachine : machine after = tokenstate).
  { unfold after. rewrite run_machine. reflexivity. }
  assert (Hvalue : nums after vardef_0__readNat_value = number_from 0 chars).
  { unfold after. apply run_value. reflexivity. }
  unfold funcdef_0__readNat. rewrite exec_eliminate, actual_body. fold f.
  rewrite (read_composition funcdef_0__readToken digit_loop f tokenstate after Hreader ltac:(lia) Htvalid Hrun ltac:(rewrite Hmachine; lia)).
  cbn [optionBind fst snd machine setMachine]. rewrite Hvalue, Hmachine. reflexivity.
Qed.
Theorem generated_readNat_none s bs ns chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = 0 -> meta_value s 8 = 0 ->
  (0 < length chars <= 1024)%nat ->
  Forall (fun ch => 48 <= ch <= 57) chars -> number_from 0 chars <= maximum ->
  TokenByteExecution.separator sep -> stdin s = chars ++ sep :: tail ->
  exec (funcdef_0__readNat bs ns) s = Some (tt,token_number (ReadTokenExecution.read_result s chars tail) chars).
Proof.
  intros Hmeta Htoken Hpending Herror Hlength Hdigits Hlimit Hsep Hin.
  assert (Hbytes : Forall (fun ch => 0 <= ch < 256 /\ ~ TokenByteExecution.separator ch) chars).
  { apply Forall_impl with (P := fun ch => 48 <= ch <= 57); [|exact Hdigits].
    intros ch Hch. split; [lia|unfold TokenByteExecution.separator; lia]. }
  apply generated_readNat_from_token.
  - now apply (ReadTokenExecution.generated_readToken_none s (fun _ => false) (fun _ => 0) chars sep tail).
  - now rewrite ReadTokenExecution.result_meta_length.
  - rewrite ReadTokenExecution.result_valid by exact Hmeta. discriminate.
  - now apply ReadTokenExecution.result_count.
  - unfold ReadTokenExecution.read_result. rewrite store_meta_other by discriminate.
    change (length chars <= length (memory (store_meta (ReadTokenExecution.put_many (ReadTokenExecution.reset s) 0 chars) 17 1%Z) arraydef_0__token))%nat.
    rewrite store_meta_other by discriminate. rewrite ReadTokenExecution.put_many_token_length, ReadTokenExecution.reset_token. lia.
  - intros i Hi. apply (ReadTokenExecution.result_token_entry s chars tail i); [exact Hi|exact (Nat.le_trans _ _ _ (proj2 Hlength) Htoken)].
  - exact Hdigits.
  - exact Hlimit.
Qed.

Theorem generated_readNat_pending s bs ns ch chars sep tail :
  (17 < length (memory s arraydef_0__meta))%nat ->
  (1024 <= length (memory s arraydef_0__token))%nat ->
  meta_value s 15 = ch+1 -> meta_value s 8 = 0 ->
  (S (length chars) <= 1024)%nat ->
  Forall (fun c => 48 <= c <= 57) (ch :: chars) -> number_from 0 (ch :: chars) <= maximum ->
  TokenByteExecution.separator sep -> stdin s = chars ++ sep :: tail ->
  exec (funcdef_0__readNat bs ns) s = Some (tt,token_number (ReadTokenExecution.pending_result s ch chars tail) (ch :: chars)).
Proof.
  intros Hmeta Htoken Hpending Herror Hlength Hdigits Hlimit Hsep Hin.
  inversion Hdigits as [|ch' chars' Hch Hrest]; subst ch' chars'.
  assert (Hbytes : Forall (fun c => 0 <= c < 256 /\ ~ TokenByteExecution.separator c) chars).
  { apply Forall_impl with (P := fun c => 48 <= c <= 57); [|exact Hrest].
    intros c Hc. split; [lia|unfold TokenByteExecution.separator; lia]. }
  apply generated_readNat_from_token.
  - apply (ReadTokenExecution.generated_readToken_pending s (fun _ => false) (fun _ => 0) ch chars sep tail);
      try assumption; unfold TokenByteExecution.separator; lia.
  - now rewrite ReadTokenExecution.pending_meta_length.
  - rewrite ReadTokenExecution.pending_valid by exact Hmeta. discriminate.
  - now apply ReadTokenExecution.pending_count.
  - rewrite ReadTokenExecution.pending_token_length. cbn [length]. lia.
  - intros i Hi. apply (ReadTokenExecution.pending_token_entry s ch chars tail i); [exact Hi|exact (Nat.le_trans _ _ _ Hlength Htoken)].
  - exact Hdigits.
  - exact Hlimit.
Qed.
Lemma number_result_value s chars : (11 < length (memory s arraydef_0__meta))%nat ->
  meta_value (token_number s chars) 11 = number_from 0 chars.
Proof. intro H. apply meta_store_same. exact H. Qed.
Lemma number_result_input s chars : stdin (token_number s chars) = stdin s.
Proof. reflexivity. Qed.
Lemma number_result_other s chars name : name <> arraydef_0__meta -> memory (token_number s chars) name = memory s name.
Proof. apply store_meta_other. Qed.
Theorem generated_readNat_observed s bs ns after observations :
  exec (funcdef_0__readNat bs ns) s = Some (tt,after) ->
  execObserved (funcdef_0__readNat bs ns) (s,observations) = Some (tt,(after,observations)).
Proof. intro Hrun. apply observed_plain; [apply InternalObservation.readNat_nf|exact Hrun]. Qed.
End ReadNatExecution.



