From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ArrayFacts ObservedLocal Observation LocalObservation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module NameLookupExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup.
Definition LocalAction R := Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__lookup) withLocalVariablesReturnValue R.
Definition outer_body (total : Z) : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__lookup_body in funcdef_0__lookup_body in
  lazymatch code with bind _ ?next =>
    let code := eval cbn beta in (next tt) in
    lazymatch code with bind (bind _ ?next) _ =>
      let code := eval cbn beta in (next total) in
      lazymatch code with loop _ ?body => exact body end
    end
  end).
Definition inner_body (total : Z) (outer_remaining : nat) (count : Z) : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold outer_body in (outer_body total outer_remaining) in
  let code := eval cbn beta zeta in code in
  match code with context [bind (bind (Done _ _ _ 6%Z) _) ?next] =>
    let code := eval cbn beta in (next count) in
    lazymatch code with loop _ ?body => exact body end
  end).
Definition entry_index total remaining := total - Z.of_nat remaining - 1.
Definition byte_index count remaining := count - Z.of_nat remaining - 1.
Theorem generated_byte (f : Frame) total outer_remaining count remaining offset size value flag kind byte tokenbyte :
  (Z.to_nat (entry_index total outer_remaining) < length (memory (machine f) arraydef_0__bindings))%nat ->
  (Z.to_nat (offset + byte_index count remaining) < length (memory (machine f) arraydef_0__names))%nat ->
  (Z.to_nat (byte_index count remaining) < length (memory (machine f) arraydef_0__token))%nat ->
  word (offset + byte_index count remaining) ->
  List.nth (Z.to_nat (entry_index total outer_remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) = (offset,size,value,flag,kind) ->
  List.nth (Z.to_nat (offset + byte_index count remaining)) (memory (machine f) arraydef_0__names) 0 = byte ->
  List.nth (Z.to_nat (byte_index count remaining)) (memory (machine f) arraydef_0__token) 0 = tokenbyte ->
  execLocal (inner_body total outer_remaining count remaining) f =
    if bool_decide (byte = tokenbyte) then Some (KeepGoing,f)
    else Some (Stop,setNum f vardef_0__lookup_equal 0).
Proof.
  intros Hbinding Hnames Htoken Hword Hentry Hname Htok.
  destruct f as [s bs ns]. cbn [machine] in *.
  unfold entry_index, byte_index in *.
  let reduce_step := ltac:(
  unfold inner_body, outer_body; cbn zeta;
  cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    retrieve numberLocalGet numberLocalSet break addInt execLocal localStep step optionBind fst snd
    nums bools machine setNum setMachine Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__lookup varsfuncdef_0__lookup_rec];
  repeat first [progress rewrite (coerce_word _ Hword)
    |progress rewrite nth_lt_default with (default := (0,0,0,0,0))
    |progress rewrite nth_lt_default with (default := 0)
    |match goal with |- context [@List.nth ?A ?slot (memory s arraydef_0__bindings) ?zero] =>
        let Hraw := fresh "Hraw" in assert (Hraw : @List.nth A slot (memory s arraydef_0__bindings) zero = (offset,size,value,flag,kind)) by exact Hentry;
        rewrite Hraw; clear Hraw end
    |match goal with |- context [@List.nth ?A ?slot (memory s arraydef_0__names) ?zero] =>
        let Hraw := fresh "Hraw" in assert (Hraw : @List.nth A slot (memory s arraydef_0__names) zero = byte) by exact Hname;
        rewrite Hraw; clear Hraw end
    |match goal with |- context [@List.nth ?A ?slot (memory s arraydef_0__token) ?zero] =>
        let Hraw := fresh "Hraw" in assert (Hraw : @List.nth A slot (memory s arraydef_0__token) zero = tokenbyte) by exact Htok;
        rewrite Hraw; clear Hraw end
    |progress rewrite Hentry |progress rewrite Hname |progress rewrite Htok
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence
       |progress rewrite (bool_decide_false P) by congruence] end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
      retrieve numberLocalGet numberLocalSet break addInt execLocal localStep step optionBind fst snd
      nums bools machine setNum setMachine Imperative.update decide decide_rel
      variableIndexEqualityDecidablevarsfuncdef_0__lookup varsfuncdef_0__lookup_rec]
    |match goal with |- context [Nat.lt_dec ?i ?len] => destruct (Nat.lt_dec i len); [|lia] end
    |case_decide; [|lia]
  ];
  reflexivity) in
  destruct (Z.eq_dec byte tokenbyte) as [Hequal|Hdifferent]; reduce_step.
Qed.
Fixpoint equal_suffix (s : Machine) offset size remaining : bool := match remaining with
| O => true
| S rest => bool_decide (List.nth (offset + (size - S rest)) (memory s arraydef_0__names) 0 =
    List.nth (size - S rest) (memory s arraydef_0__token) 0) && equal_suffix s offset size rest
end.
Theorem generated_compare (f : Frame) total outer_remaining size remaining offset value flag kind :
  (remaining <= size)%nat -> 0 <= offset -> word (offset + Z.of_nat size) ->
  (Z.to_nat offset + size <= length (memory (machine f) arraydef_0__names))%nat ->
  (size <= length (memory (machine f) arraydef_0__token))%nat ->
  (Z.to_nat (entry_index total outer_remaining) < length (memory (machine f) arraydef_0__bindings))%nat ->
  List.nth (Z.to_nat (entry_index total outer_remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) =
    (offset,Z.of_nat size,value,flag,kind) ->
  execLocal (loop remaining (inner_body total outer_remaining (Z.of_nat size))) f =
    Some (tt,if equal_suffix (machine f) (Z.to_nat offset) size remaining then f else setNum f vardef_0__lookup_equal 0).
Proof.
  induction remaining as [|remaining IH] in f |- *.
  - intros. reflexivity.
  - intros Hremaining Hoffset Hword Hnames Htoken Hbinding Hentry.
    set (j := (size - S remaining)%nat).
    assert (Hj : (j < size)%nat) by (unfold j; lia).
    assert (Hindex : byte_index (Z.of_nat size) remaining = Z.of_nat j) by (unfold byte_index,j; lia).
    assert (Hjword : word (offset + Z.of_nat j)) by (unfold word in *; lia).
    assert (Hjconvert : Z.to_nat (offset + Z.of_nat j) = (Z.to_nat offset + j)%nat).
    { rewrite Z2Nat.inj_add by lia. now rewrite Nat2Z.id. }
    pose proof (generated_byte f total outer_remaining (Z.of_nat size) remaining offset (Z.of_nat size) value flag kind
      (List.nth (Z.to_nat offset + j) (memory (machine f) arraydef_0__names) 0)
      (List.nth j (memory (machine f) arraydef_0__token) 0) Hbinding
      ltac:(rewrite Hindex,Hjconvert; lia) ltac:(rewrite Hindex,Nat2Z.id; lia)
      ltac:(now rewrite Hindex) Hentry ltac:(now rewrite Hindex,Hjconvert) ltac:(now rewrite Hindex,Nat2Z.id)) as Hbyte.
    rewrite loop_S,execLocal_bind,Hbyte. cbn [equal_suffix]. fold j.
    destruct (bool_decide (List.nth (Z.to_nat offset + j) (memory (machine f) arraydef_0__names) 0 =
      List.nth j (memory (machine f) arraydef_0__token) 0)) eqn:Hsame.
    + cbn [optionBind fst snd andb]. apply IH; try assumption; lia.
    + reflexivity.
Qed.
Lemma equal_suffix_spec s offset size remaining : (remaining <= size)%nat ->
  (equal_suffix s offset size remaining = true <-> forall j, (size - remaining <= j < size)%nat ->
    List.nth (offset + j) (memory s arraydef_0__names) 0 = List.nth j (memory s arraydef_0__token) 0).
Proof.
  induction remaining as [|remaining IH].
  - intro Hrange. cbn [equal_suffix]. split; [intros _ j Hj; lia|reflexivity].
  - intro Hrange. cbn [equal_suffix]. rewrite andb_true_iff, bool_decide_eq_true, IH by lia.
    split.
    + intros [Hfirst Htail] j Hj. destruct (Nat.eq_dec j (size - S remaining)) as [->|Hother]; [exact Hfirst|apply Htail; lia].
    + intro Hall. split; [apply Hall; lia|intros j Hj; apply Hall; lia].
Qed.
Lemma compare_no_flush total outer_remaining count remaining :
  InternalObservation.local_nf (loop remaining (inner_body total outer_remaining count)).
Proof.
  apply InternalObservation.loop_nf. intro index. unfold inner_body,outer_body. InternalObservation.nf.
Qed.
Theorem generated_compare_observed (f : Frame) total outer_remaining size remaining offset value flag kind observations :
  (remaining <= size)%nat -> 0 <= offset -> word (offset + Z.of_nat size) ->
  (Z.to_nat offset + size <= length (memory (machine f) arraydef_0__names))%nat ->
  (size <= length (memory (machine f) arraydef_0__token))%nat ->
  (Z.to_nat (entry_index total outer_remaining) < length (memory (machine f) arraydef_0__bindings))%nat ->
  List.nth (Z.to_nat (entry_index total outer_remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) =
    (offset,Z.of_nat size,value,flag,kind) ->
  execLocalObserved (loop remaining (inner_body total outer_remaining (Z.of_nat size))) (f,observations) =
    Some (tt,((if equal_suffix (machine f) (Z.to_nat offset) size remaining then f else setNum f vardef_0__lookup_equal 0),observations)).
Proof.
  intros Hremaining Hoffset Hword Hnames Htoken Hbinding Hentry. apply LocalObservation.plain_observed.
  - apply compare_no_flush.
  - exact (generated_compare f total outer_remaining size remaining offset value flag kind Hremaining Hoffset Hword Hnames Htoken Hbinding Hentry).
Qed.
Definition outer_with total remaining (compare : Z -> LocalAction unit) : LocalAction LoopOutcome := ltac:(
  let code := eval unfold outer_body in (outer_body total remaining) in
  let code := eval cbn beta zeta in code in
  match code with context [bind (bind (Done _ _ _ 6%Z) _) ?next] =>
    let candidate := eval cbn beta in (next 0%Z) in
    lazymatch candidate with loop _ _ =>
      let abstracted := eval pattern next in code in
      lazymatch abstracted with ?family _ => exact (family compare) end
    end
  end).
Lemma outer_actual total remaining : outer_body total remaining = outer_with total remaining
  (fun count => loop (Z.to_nat count) (inner_body total remaining count)).
Proof. reflexivity. Qed.
Theorem generated_entry_composition compare (f compared : Frame) total outer_remaining size offset value flag kind observations :
  (6 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size ->
  (Z.to_nat (entry_index total outer_remaining) < length (memory (machine f) arraydef_0__bindings))%nat ->
  List.nth (Z.to_nat (entry_index total outer_remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) =
    (offset,Z.of_nat size,value,flag,kind) ->
  execLocalObserved (compare (Z.of_nat size)) (setNum f vardef_0__lookup_equal 1,observations) = Some (tt,(compared,observations)) ->
  machine compared = machine f ->
  execLocalObserved (outer_with total outer_remaining compare) (f,observations) =
    Some ((if bool_decide (nums compared vardef_0__lookup_equal <> 0) then Stop else KeepGoing),
      ((if bool_decide (nums compared vardef_0__lookup_equal <> 0)
        then setMachine compared (store_meta (machine compared) 0 (entry_index total outer_remaining)) else compared),observations)).
Proof.
  intros Hmeta Hsize Hbinding Hentry Hcompare Hmachine. destruct f as [s bs ns], compared as [cs cbs cns]. cbn [machine] in *. subst cs.
  unfold outer_with.
  let solve_entry := ltac:(repeat first [progress rewrite ObservedLocal.drop_assoc
    |progress rewrite ObservedLocal.drop_lift
    |progress cbn [optionBind fst snd]
    |progress fold (entry_index total outer_remaining)
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       lazymatch name with
       | arraydef_0__bindings => exact Hbinding
       | arraydef_0__meta => eapply Nat.le_lt_trans with (m := 6%nat); [cbn; lia|exact Hmeta]
       end)
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hsize |progress rewrite Hentry
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (compare ?count) ?state] =>
        let expression := constr:(@execLocalObserved I T EI V EV R (compare count) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,({|machine := s; bools := cbs; nums := cns|},observations))) by exact Hcompare;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence
       |progress rewrite (bool_decide_false P) by congruence] end
    |progress cbn [dropWithinLoop break bind]
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]) in
  destruct (Z.eq_dec (cns vardef_0__lookup_equal) 0) as [Hmatched|Hmatched]; solve_entry; reflexivity.
Qed.
Definition entry_result (f : Frame) total remaining offset size :=
  if equal_suffix (machine f) (Z.to_nat offset) size size
  then (Stop,setMachine (setNum f vardef_0__lookup_equal 1) (store_meta (machine f) 0 (entry_index total remaining)))
  else (KeepGoing,setNum (setNum f vardef_0__lookup_equal 1) vardef_0__lookup_equal 0).
Theorem generated_entry (f : Frame) total outer_remaining size offset value flag kind observations :
  (6 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size ->
  0 <= offset -> word (offset + Z.of_nat size) ->
  (Z.to_nat offset + size <= length (memory (machine f) arraydef_0__names))%nat ->
  (size <= length (memory (machine f) arraydef_0__token))%nat ->
  (Z.to_nat (entry_index total outer_remaining) < length (memory (machine f) arraydef_0__bindings))%nat ->
  List.nth (Z.to_nat (entry_index total outer_remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) =
    (offset,Z.of_nat size,value,flag,kind) ->
  execLocalObserved (outer_body total outer_remaining) (f,observations) =
    Some (fst (entry_result f total outer_remaining offset size),(snd (entry_result f total outer_remaining offset size),observations)).
Proof.
  intros Hmeta Hsize Hoffset Hword Hnames Htoken Hbinding Hentry.
  set (entered := setNum f vardef_0__lookup_equal 1).
  set (compared := if equal_suffix (machine f) (Z.to_nat offset) size size then entered else setNum entered vardef_0__lookup_equal 0).
  assert (Hcompare : execLocalObserved (loop (Z.to_nat (Z.of_nat size)) (inner_body total outer_remaining (Z.of_nat size)))
    (entered,observations) = Some (tt,(compared,observations))).
  { rewrite Nat2Z.id. exact (generated_compare_observed entered total outer_remaining size size offset value flag kind observations
      ltac:(lia) Hoffset Hword Hnames Htoken Hbinding Hentry). }
  assert (Hmachine : machine compared = machine f).
  { unfold compared,entered. destruct (equal_suffix (machine f) (Z.to_nat offset) size size); reflexivity. }
  rewrite outer_actual.
  pose proof (generated_entry_composition (fun count => loop (Z.to_nat count) (inner_body total outer_remaining count))
    f compared total outer_remaining size offset value flag kind observations Hmeta Hsize Hbinding Hentry Hcompare Hmachine) as Hrun.
  rewrite Hrun. unfold compared,entered,entry_result.
  destruct (equal_suffix (machine f) (Z.to_nat offset) size size);
    cbn [nums setNum setMachine machine fst snd];
    cbn; reflexivity.
Qed.
Theorem generated_entry_length_mismatch (f : Frame) total outer_remaining size descriptor_size offset value flag kind observations :
  (6 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 6 = Z.of_nat size -> descriptor_size <> size ->
  (Z.to_nat (entry_index total outer_remaining) < length (memory (machine f) arraydef_0__bindings))%nat ->
  List.nth (Z.to_nat (entry_index total outer_remaining)) (memory (machine f) arraydef_0__bindings) (0,0,0,0,0) =
    (offset,Z.of_nat descriptor_size,value,flag,kind) ->
  execLocalObserved (outer_body total outer_remaining) (f,observations) = Some (KeepGoing,(f,observations)).
Proof.
  intros Hmeta Hsize Hdifferent Hbinding Hentry. destruct f as [s bs ns]. cbn [machine] in *.
  unfold outer_body. cbn beta zeta.
  repeat first [progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |progress cbn [optionBind fst snd] |progress fold (entry_index total outer_remaining)
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       lazymatch name with
       |arraydef_0__bindings => exact Hbinding
       |arraydef_0__meta => eapply Nat.le_lt_trans with (m := 6%nat); [cbn; lia|exact Hmeta]
       end)
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |progress rewrite Hsize |progress rewrite Hentry
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |progress cbn [dropWithinLoop break bind]
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ]. reflexivity.
Qed.
End NameLookupExecution.
