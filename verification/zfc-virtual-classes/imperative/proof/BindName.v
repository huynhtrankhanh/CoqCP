From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash InternTail NameCopy NameSearch NameRepresentation BindingStorage ObservedLocal NativePrimitives ReplyOK ReplyNO.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module BindNameExecution.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := NameCopyExecution.Frame.
Definition lookup_function := (varsfuncdef_0__lookup -> bool) -> (varsfuncdef_0__lookup -> Z) ->
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.
Definition body_with (lookup : lookup_function) (copy : Z -> NameCopyExecution.LocalAction unit) : NameCopyExecution.LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__bindName_body in funcdef_0__bindName_body in
  let abstracted := eval pattern funcdef_0__lookup in code in
  lazymatch abstracted with ?family _ =>
    let code := constr:(family lookup) in let code := eval cbv beta in code in
    match code with context [bind (bind (Done _ _ _ 6%Z) _) ?next] =>
      let candidate := eval cbn beta in (next 0%Z) in
      lazymatch candidate with loop _ _ =>
        let abstracted := eval pattern next in code in
        lazymatch abstracted with ?family _ => exact (family copy) end
      end
    end
  end).
Lemma body_actual : funcdef_0__bindName_body = body_with funcdef_0__lookup
  (fun total => loop (Z.to_nat total) (NameCopyExecution.copy_body total)).
Proof. reflexivity. Qed.
Definition copy_start (f : Frame) looked offset size := setMachine f (BindingStorage.grown_names looked offset size).
Lemma updated_meta_other s count offset size value kind i : i <> 5%nat ->
  meta_value (BindingStorage.updated_bytes s count offset size value kind) i = meta_value s i.
Proof. intro H. unfold BindingStorage.updated_bytes. rewrite meta_store_other by exact H. apply BindingStorage.written_meta. Qed.
Lemma updated_length s count offset size value kind : length (memory (BindingStorage.updated_bytes s count offset size value kind) arraydef_0__meta) = length (memory s arraydef_0__meta).
Proof. unfold BindingStorage.updated_bytes. rewrite store_meta_length. apply BindingStorage.written_meta_length. Qed.
Lemma reply_meta s value i : meta_value (ReplyOKExecution.reply_state s value) i = meta_value s i.
Proof. unfold meta_value. now rewrite ReplyOKExecution.reply_other by discriminate. Qed.
Local Opaque funcdef_0__ok funcdef_0__no.
Theorem generated_body_composition lookup copy (f : Frame) looked count offset size value kind observations :
  execObserved (lookup (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(looked,observations)) ->
  (8 < length (memory looked arraydef_0__meta))%nat -> (20 <= length (memory looked arraydef_0__printBuffer))%nat ->
  meta_value looked 0 = maximum -> meta_value looked 4 = Z.of_nat count ->
  meta_value looked 5 = Z.of_nat offset -> meta_value looked 6 = Z.of_nat size ->
  Z.of_nat count < maximum -> Z.of_nat (offset + size) <= maximum -> Z.of_nat value <= maximum ->
  nums f vardef_0__bindName_value = Z.of_nat value -> nums f vardef_0__bindName_kind = kind ->
  execLocalObserved (copy (Z.of_nat size)) (copy_start f looked offset size,observations) =
    Some (tt,(setMachine f (BindingStorage.copied looked offset size),observations)) ->
  execLocalObserved (body_with lookup copy) (f,observations) = Some (tt,(setMachine f (BindingStorage.result looked count offset size value kind),
    observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin looked|}])).
Proof.
  intros Hlookup Hmeta Hbuffer Hmissing Hcount Hoffset Hsize Hcountword Hbytesword Hvalueword Hvalue Hkind Hcopy.
  destruct f as [s bs ns]. cbn [machine nums] in *.
  assert (Hsum : coerceInt (Z.of_nat offset + Z.of_nat size) 64 = Z.of_nat (offset + size)).
  { rewrite <-Nat2Z.inj_add. apply coerce_word. unfold word. lia. }
  assert (Hnext : coerceInt (Z.of_nat count + 1) 64 = Z.of_nat (S count)).
  { rewrite coerce_word by (unfold word; lia). lia. }
  assert (Hdifference : coerceInt (maximum - Z.of_nat offset) 64 = maximum - Z.of_nat offset).
  { apply coerce_word. unfold word. lia. }
  unfold maximum in *. unfold body_with.
  repeat first [progress cbn [optionBind fst snd]
    |progress unfold addInt at 1 |progress unfold subInt at 1
    |progress fold (BindingStorage.grown_names looked offset size)
    |progress fold (BindingStorage.grown_bindings looked count offset size)
    |progress fold (BindingStorage.raw offset size value kind)
    |progress change (withMemory (BindingStorage.grown_bindings looked count offset size)
       (modifyArray (memory (BindingStorage.grown_bindings looked count offset size)) arraydef_0__bindings count
         (BindingStorage.raw offset size value kind))) with (BindingStorage.written looked count offset size value kind)
    |progress fold (BindingStorage.updated_bytes looked count offset size value kind)
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code (?frame, ?trace)] =>
        let current := eval cbn [machine] in (machine frame) in
        lazymatch current with withMemory _ _ =>
          let Hstate := fresh "Hstate" in
          assert (Hstate : current = BindingStorage.written looked count offset size value kind) by reflexivity;
          rewrite Hstate; clear Hstate
        end
      end
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       lazymatch name with
       | arraydef_0__meta =>
           repeat first [rewrite ReplyOKExecution.reply_other by discriminate
             |rewrite store_meta_length |rewrite updated_length |rewrite BindingStorage.written_meta_length
             |rewrite BindingStorage.grown_bindings_other by discriminate
             |rewrite BindingStorage.copied_other by discriminate
             |rewrite BindingStorage.grown_names_other by discriminate];
           eapply Nat.le_lt_trans with (m := 8%nat); [cbn; lia|exact Hmeta]
       | arraydef_0__bindings => unfold BindingStorage.grown_bindings; cbn [withMemory memory];
           rewrite growArrays_same,growList_length; rewrite ?Nat2Z.id; lia
       end)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (lookup ?bl ?nl) ?state] =>
        let expression := constr:(@execObserved I T EI R (lookup bl nl) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(looked,observations))) by exact Hlookup;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R (copy ?n) ?state] =>
        let expression := constr:(@execLocalObserved I T EI V EV R (copy n) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(setMachine {|machine := s; bools := bs; nums := ns|}
          (BindingStorage.copied looked offset size),observations))) by exact Hcopy;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__ok ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__ok bo no) (current,trace)) in
        let Hok := fresh "Hok" in assert (Hok : expression = Some (tt,(ReplyOKExecution.reply_state current value,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin current|}]))) by
          (apply (ReplyOKExecution.generated_ok current bo no value trace); [reflexivity|exact Hvalueword|
            unfold BindingStorage.updated_bytes; rewrite store_meta_other,BindingStorage.written_other,BindingStorage.copied_other by discriminate; exact Hbuffer]);
        rewrite Hok; clear Hok end
    |progress rewrite reply_meta |progress rewrite updated_meta_other by lia
    |progress rewrite BindingStorage.written_meta |progress rewrite BindingStorage.grown_bindings_meta
    |progress rewrite BindingStorage.copied_meta |progress rewrite BindingStorage.grown_names_meta
    |progress rewrite Hmissing |progress rewrite Hcount |progress rewrite Hoffset |progress rewrite Hsize
    |progress rewrite Hvalue |progress rewrite Hkind |progress rewrite Hsum |progress rewrite Hnext |progress rewrite Hdifference
    |progress rewrite Nat2Z.id
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress replace (Z.to_nat 4) with 4%nat by reflexivity
    |progress replace (Z.to_nat 5) with 5%nat by reflexivity
    |progress replace (Z.to_nat 6) with 6%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ].
  unfold BindingStorage.result,BindingStorage.updated_bytes.
  cbn [store_meta withMemory stdin stdout]. rewrite ?BindingStorage.written_input,?BindingStorage.written_output. reflexivity.
Qed.
Theorem generated_copy (f : Frame) looked offset size observations :
  (8 < length (memory looked arraydef_0__meta))%nat ->
  meta_value looked 5 = Z.of_nat offset -> Z.of_nat (offset + size) <= maximum ->
  (size <= length (memory looked arraydef_0__token))%nat ->
  execLocalObserved (loop (Z.to_nat (Z.of_nat size)) (NameCopyExecution.copy_body (Z.of_nat size)))
    (copy_start f looked offset size,observations) =
    Some (tt,(setMachine f (BindingStorage.copied looked offset size),observations)).
Proof.
  intros Hmeta Hoffset Hword Htoken. rewrite Nat2Z.id.
  assert (Hmeta' : (5 < length (memory (BindingStorage.grown_names looked offset size) arraydef_0__meta))%nat)
    by (rewrite BindingStorage.grown_names_other by discriminate; lia).
  assert (Hoffset' : meta_value (BindingStorage.grown_names looked offset size) 5 = Z.of_nat offset)
    by (now rewrite BindingStorage.grown_names_meta).
  assert (Htoken' : (size <= length (memory (BindingStorage.grown_names looked offset size) arraydef_0__token))%nat)
    by (now rewrite BindingStorage.grown_names_other by discriminate).
  assert (Hnames : (offset + size <= length (memory (BindingStorage.grown_names looked offset size) arraydef_0__names))%nat)
    by (rewrite BindingStorage.grown_names_length; lia).
  pose proof (NameCopyExecution.generated_copy (copy_start f looked offset size) offset size size observations
    ltac:(lia) Hmeta' Hoffset' ltac:(unfold word; lia) Htoken' Hnames) as Hrun.
  unfold copy_start in *. destruct f. exact Hrun.
Qed.
Theorem generated_body (f : Frame) looked count offset size value kind observations :
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(looked,observations)) ->
  (8 < length (memory looked arraydef_0__meta))%nat -> (20 <= length (memory looked arraydef_0__printBuffer))%nat ->
  meta_value looked 0 = maximum -> meta_value looked 4 = Z.of_nat count ->
  meta_value looked 5 = Z.of_nat offset -> meta_value looked 6 = Z.of_nat size ->
  Z.of_nat count < maximum -> Z.of_nat (offset + size) <= maximum -> Z.of_nat value <= maximum ->
  nums f vardef_0__bindName_value = Z.of_nat value -> nums f vardef_0__bindName_kind = kind ->
  (size <= length (memory looked arraydef_0__token))%nat ->
  execLocalObserved funcdef_0__bindName_body (f,observations) = Some (tt,(setMachine f (BindingStorage.result looked count offset size value kind),
    observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin looked|}])).
Proof.
  intros Hlookup Hmeta Hbuffer Hmissing Hcount Hoffset Hsize Hcountword Hbytesword Hvalueword Hvalue Hkind Htoken.
  rewrite body_actual. eapply generated_body_composition; try eassumption.
  exact (generated_copy f looked offset size observations Hmeta Hoffset Hbytesword Htoken).
Qed.
Theorem generated_bind s bs ns looked count offset size value kind observations :
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(looked,observations)) ->
  (8 < length (memory looked arraydef_0__meta))%nat -> (20 <= length (memory looked arraydef_0__printBuffer))%nat ->
  meta_value looked 0 = maximum -> meta_value looked 4 = Z.of_nat count ->
  meta_value looked 5 = Z.of_nat offset -> meta_value looked 6 = Z.of_nat size ->
  Z.of_nat count < maximum -> Z.of_nat (offset + size) <= maximum -> Z.of_nat value <= maximum ->
  ns vardef_0__bindName_value = Z.of_nat value -> ns vardef_0__bindName_kind = kind ->
  (size <= length (memory looked arraydef_0__token))%nat ->
  execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(BindingStorage.result looked count offset size value kind,
    observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin looked|}])).
Proof.
  intros Hlookup Hmeta Hbuffer Hmissing Hcount Hoffset Hsize Hcountword Hbytesword Hvalueword Hvalue Hkind Htoken.
  pose proof (generated_body {|machine := s; bools := bs; nums := ns|} looked count offset size value kind observations
    Hlookup Hmeta Hbuffer Hmissing Hcount Hoffset Hsize Hcountword Hbytesword Hvalueword Hvalue Hkind Htoken) as Hbody.
  unfold funcdef_0__bindName. rewrite ObservedLocal.eliminate_correct.
  match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
    let expression := constr:(@execLocalObserved I T EI V EV R code state) in
    assert (Hrun : expression = Some (tt,(setMachine {|machine := s; bools := bs; nums := ns|}
      (BindingStorage.result looked count offset size value kind), observations ++
        [{|flushedOutput := stdout looked ++ Protocol.reply_bytes (Protocol.OK value); unreadInput := stdin looked|}]))) by exact Hbody;
    rewrite Hrun; reflexivity
  end.
Qed.
Theorem generated_duplicate_body (f : Frame) looked observations :
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (machine f,observations) = Some (tt,(looked,observations)) ->
  (0 < length (memory looked arraydef_0__meta))%nat -> meta_value looked 0 <> maximum ->
  execLocalObserved funcdef_0__bindName_body (f,observations) = Some (tt,(setMachine f (ReplyNOExecution.reply_state looked),
    observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin looked|}])).
Proof.
  intros Hlookup Hmeta Hfound. destruct f as [s bs ns]. cbn [machine] in *. unfold maximum in *.
  rewrite body_actual. unfold body_with.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hmeta)
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__lookup ?bl ?nl) ?state] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__lookup bl nl) state) in
        let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(looked,observations))) by exact Hlookup;
        rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__no ?bo ?no) (?current,?trace)] =>
        let expression := constr:(@execObserved I T EI R (funcdef_0__no bo no) (current,trace)) in
        let Hno := fresh "Hno" in assert (Hno : expression = Some (tt,(ReplyNOExecution.reply_state current,
          trace ++ [{|flushedOutput := stdout current ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin current|}]))) by
          exact (ReplyNOExecution.generated_no current bo no trace);
        rewrite Hno; clear Hno end
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by congruence
       |progress rewrite (bool_decide_false P) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine nums bools]
  ]. reflexivity.
Qed.
Theorem generated_duplicate s bs ns looked observations :
  execObserved (funcdef_0__lookup (fun _ => false) (fun _ => 0)) (s,observations) = Some (tt,(looked,observations)) ->
  (0 < length (memory looked arraydef_0__meta))%nat -> meta_value looked 0 <> maximum ->
  execObserved (funcdef_0__bindName bs ns) (s,observations) = Some (tt,(ReplyNOExecution.reply_state looked,
    observations ++ [{|flushedOutput := stdout looked ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin looked|}])).
Proof.
  intros Hlookup Hmeta Hfound.
  pose proof (generated_duplicate_body {|machine := s; bools := bs; nums := ns|} looked observations Hlookup Hmeta Hfound) as Hbody.
  unfold funcdef_0__bindName. rewrite ObservedLocal.eliminate_correct.
  match goal with |- context [@execLocalObserved ?I ?T ?EI ?V ?EV ?R ?code ?state] =>
    let expression := constr:(@execLocalObserved I T EI V EV R code state) in
    assert (Hrun : expression = Some (tt,(setMachine {|machine := s; bools := bs; nums := ns|}
      (ReplyNOExecution.reply_state looked), observations ++
        [{|flushedOutput := stdout looked ++ Protocol.reply_bytes Protocol.NO; unreadInput := stdin looked|}]))) by exact Hbody;
    rewrite Hrun; reflexivity
  end.
Qed.
End BindNameExecution.
