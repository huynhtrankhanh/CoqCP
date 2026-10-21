From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index Overflow SipHash InternTail ArrayFacts ObservedLocal NativePrimitives NameLookup.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module NameCopyExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__bindName) withLocalVariablesReturnValue R.
Definition copy_body (total : Z) : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__bindName_body in funcdef_0__bindName_body in
  match code with context [bind (bind (Done _ _ _ 6%Z) _) ?next] =>
    let candidate := eval cbn beta in (next total) in
    lazymatch candidate with loop _ ?body => exact body end
  end).
Definition written (s : Machine) index byte := withMemory s (modifyArray (memory s) arraydef_0__names index byte).
Lemma written_other s index byte name : name <> arraydef_0__names -> memory (written s index byte) name = memory s name.
Proof. intro H. unfold written. cbn [withMemory memory]. now rewrite InternTailExecution.modify_other. Qed.
Lemma written_names s index byte : memory (written s index byte) arraydef_0__names = <[index := byte]> (memory s arraydef_0__names).
Proof. unfold written. cbn [withMemory memory]. apply InternTailExecution.modify_same. Qed.
Lemma written_meta s index byte i : meta_value (written s index byte) i = meta_value s i.
Proof. unfold meta_value. now rewrite written_other by discriminate. Qed.
Lemma written_length s index byte : length (memory (written s index byte) arraydef_0__names) = length (memory s arraydef_0__names).
Proof. rewrite written_names. apply length_insert. Qed.
Theorem generated_copy_byte (f : Frame) total remaining offset index byte observations :
  (5 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 5 = Z.of_nat offset ->
  NameLookupExecution.byte_index total remaining = Z.of_nat index -> word (Z.of_nat (offset + index)) ->
  (index < length (memory (machine f) arraydef_0__token))%nat ->
  (offset + index < length (memory (machine f) arraydef_0__names))%nat ->
  List.nth index (memory (machine f) arraydef_0__token) 0 = byte ->
  execLocalObserved (copy_body total remaining) (f,observations) = Some (KeepGoing,(setMachine f (written (machine f) (offset + index) byte),observations)).
Proof.
  intros Hmeta Hoffset Hindex Hword Htoken Hnames Hbyte. destruct f as [s bs ns]. cbn [machine] in *.
  assert (Hadd : coerceInt (Z.of_nat offset + Z.of_nat index) 64 = Z.of_nat (offset + index)).
  { rewrite <-Nat2Z.inj_add. now apply coerce_word. }
  unfold copy_body. cbn beta zeta.
  repeat first [progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |progress cbn [optionBind fst snd]
    |progress fold (NameLookupExecution.byte_index total remaining)
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       lazymatch name with
       |arraydef_0__meta => eapply Nat.le_lt_trans with (m := 5%nat); [cbn; lia|exact Hmeta]
       |arraydef_0__token => exact Htoken
       |arraydef_0__names => exact Hnames
       end)
    |progress replace (Z.to_nat 5) with 5%nat by reflexivity
    |progress rewrite Hoffset |progress rewrite Hindex |progress rewrite Hbyte
    |progress unfold addInt at 1 |progress rewrite Hadd |progress rewrite Nat2Z.id
    |progress cbn [dropWithinLoop break bind]
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.
Fixpoint copy_remaining (s : Machine) offset total remaining := match remaining with
| O => s
| S rest => let index := (total - S rest)%nat in
    copy_remaining (written s (offset + index) (List.nth index (memory s arraydef_0__token) 0)) offset total rest
end.
Lemma copy_other s offset total remaining name : name <> arraydef_0__names ->
  memory (copy_remaining s offset total remaining) name = memory s name.
Proof.
  intro Hname. induction remaining as [|remaining IH] in s |- *; [reflexivity|].
  cbn [copy_remaining]. now rewrite IH,written_other.
Qed.
Lemma copy_length s offset total remaining : length (memory (copy_remaining s offset total remaining) arraydef_0__names) = length (memory s arraydef_0__names).
Proof.
  induction remaining as [|remaining IH] in s |- *; [reflexivity|]. cbn [copy_remaining]. now rewrite IH,written_length.
Qed.
Lemma copy_meta s offset total remaining i : meta_value (copy_remaining s offset total remaining) i = meta_value s i.
Proof. unfold meta_value. now rewrite copy_other by discriminate. Qed.
Lemma copy_input s offset total remaining : stdin (copy_remaining s offset total remaining) = stdin s.
Proof. induction remaining as [|remaining IH] in s |- *; [reflexivity|]. cbn [copy_remaining]. rewrite IH. reflexivity. Qed.
Lemma copy_output s offset total remaining : stdout (copy_remaining s offset total remaining) = stdout s.
Proof. induction remaining as [|remaining IH] in s |- *; [reflexivity|]. cbn [copy_remaining]. rewrite IH. reflexivity. Qed.
Theorem generated_copy (f : Frame) offset total remaining observations :
  (remaining <= total)%nat -> (5 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 5 = Z.of_nat offset -> word (Z.of_nat (offset + total)) ->
  (total <= length (memory (machine f) arraydef_0__token))%nat ->
  (offset + total <= length (memory (machine f) arraydef_0__names))%nat ->
  execLocalObserved (loop remaining (copy_body (Z.of_nat total))) (f,observations) =
    Some (tt,(setMachine f (copy_remaining (machine f) offset total remaining),observations)).
Proof.
  induction remaining as [|remaining IH] in f |- *.
  - intros. destruct f. reflexivity.
  - intros Hremaining Hmeta Hoffset Hword Htoken Hnames.
    set (index := (total - S remaining)%nat).
    assert (Hindex : (index < total)%nat) by (unfold index; lia).
    assert (Hbinder : NameLookupExecution.byte_index (Z.of_nat total) remaining = Z.of_nat index) by
      (unfold NameLookupExecution.byte_index,index; lia).
    assert (Hindexword : word (Z.of_nat (offset + index))) by (unfold word in *; lia).
    pose proof (generated_copy_byte f (Z.of_nat total) remaining offset index
      (List.nth index (memory (machine f) arraydef_0__token) 0) observations Hmeta Hoffset Hbinder Hindexword ltac:(lia) ltac:(lia) eq_refl) as Hbyte.
    rewrite loop_S,ObservedLocal.local_bind,Hbyte. cbn [optionBind fst snd].
    set (next := setMachine f (written (machine f) (offset + index) (List.nth index (memory (machine f) arraydef_0__token) 0))).
    assert (Hnextmeta : (5 < length (memory (machine next) arraydef_0__meta))%nat).
    { unfold next. cbn [machine setMachine]. now rewrite written_other by discriminate. }
    assert (Hnextoffset : meta_value (machine next) 5 = Z.of_nat offset) by (unfold next; cbn [machine setMachine]; now rewrite written_meta).
    assert (Hnexttoken : (total <= length (memory (machine next) arraydef_0__token))%nat).
    { unfold next. cbn [machine setMachine]. now rewrite written_other by discriminate. }
    assert (Hnextnames : (offset + total <= length (memory (machine next) arraydef_0__names))%nat).
    { unfold next. cbn [machine setMachine]. now rewrite written_length. }
    pose proof (IH next ltac:(lia) Hnextmeta Hnextoffset Hword Hnexttoken Hnextnames) as Hrest.
    match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
      let expression := constr:(@execLocalObserved I T EI V EV R code state) in
      let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(setMachine next (copy_remaining (machine next) offset total remaining),observations))) by exact Hrest;
      rewrite Hrun
    end. unfold next,index. destruct f. reflexivity.
Qed.
Theorem copy_before s offset total remaining i : (remaining <= total)%nat -> (i < offset + (total - remaining))%nat ->
  List.nth i (memory (copy_remaining s offset total remaining) arraydef_0__names) 0 = List.nth i (memory s arraydef_0__names) 0.
Proof.
  induction remaining as [|remaining IH] in s |- *; [intros; reflexivity|].
  intros Hremaining Hi. cbn [copy_remaining]. rewrite IH by lia. rewrite written_names. apply ArrayFacts.nth_insert_other. lia.
Qed.
Theorem copy_filled s offset total remaining i : (remaining <= total)%nat ->
  (offset + total <= length (memory s arraydef_0__names))%nat -> (total - remaining <= i < total)%nat ->
  List.nth (offset + i) (memory (copy_remaining s offset total remaining) arraydef_0__names) 0 =
    List.nth i (memory s arraydef_0__token) 0.
Proof.
  induction remaining as [|remaining IH] in s |- *; [intros; lia|]. intros Hremaining Hcapacity Hi.
  cbn [copy_remaining]. destruct (Nat.eq_dec i (total - S remaining)%nat) as [Heq|Hne].
  - subst i. rewrite copy_before by lia. rewrite written_names. apply OverflowExecution.nth_insert_same. lia.
  - rewrite IH by (try rewrite written_length; lia). now rewrite written_other by discriminate.
Qed.
End NameCopyExecution.
