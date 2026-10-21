From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash Stack RenameMemoBounds RenameMemoInit ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoControl.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit.
Lemma updated_same {V A} `{EqDecision V} (values : V->A) key value : update values key value key=value.
Proof. unfold update. case_decide; congruence. Qed.
Lemma updated_other {V A} `{EqDecision V} (values : V->A) key value other : other<>key ->
  update values key value other=values other.
Proof. intro Hother. unfold update. case_decide; congruence. Qed.
Local Opaque Imperative.update.
Local Opaque loop funcdef_0__push Z.div.
Definition iteration_at remaining : LocalAction LoopOutcome := ltac:(
  let code:=eval unfold continuation in continuation in
  match code with context [loop _ ?body]=>exact (body remaining) end).
Definition iteration : LocalAction LoopOutcome := iteration_at 0%nat.
Lemma iteration_uniform remaining : iteration_at remaining=iteration.
Proof. reflexivity. Qed.
Definition body_with (scan : Z->LocalAction unit) : LocalAction unit := ltac:(
  let code:=eval unfold continuation in continuation in
  match code with context [bind (numberLocalGet _ _ _ vardef_0__rename_budget) ?next]=>
    let candidate:=eval cbn beta in (next 0%Z) in
    lazymatch candidate with loop _ _=>let family:=eval pattern next in code in
      lazymatch family with ?family _=>exact (family scan) end end end).
Lemma actual_body : continuation=body_with (fun count=>loop (Z.to_nat count) iteration_at).
Proof. reflexivity. Qed.
Definition finish : LocalAction unit := ltac:(
  let code:=eval unfold continuation in continuation in
  lazymatch code with bind _ ?next=>exact (next tt) end).
Definition prepared (f : Frame) root :=
  setMachine (setNum (setNum (setNum f vardef_0__rename_width (Z.of_nat (S root)))
    vardef_0__rename_pairs (Z.of_nat (S root*S root))) vardef_0__rename_budget (Z.of_nat (RenameMemoBounds.fuel root)))
    (StackExecution.push_state (machine f) 0 (Z.of_nat root) (nums f vardef_0__rename_initialDepth)).
Local Opaque finish.
Theorem generated_preparation scan (f : Frame) root observations :
  (31<length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 10=0 ->
  nums f vardef_0__rename_node=Z.of_nat root -> Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  execLocalObserved (body_with scan) (f,observations)=
  optionBind (execLocalObserved (scan (Z.of_nat (RenameMemoBounds.fuel root))) (prepared f root,observations))
    (fun response=>execLocalObserved finish (snd response)).
Proof.
  intros Hmeta Hstack Hroot Hfuel.
  destruct (RenameMemoBounds.checked_arithmetic root Hfuel)
    as [Hnotmax [Hwidthpos [Hsquareguard [Hpairsguard [Hpairs Hbudget]]]]].
  unfold RenameMemoBounds.maximum in Hnotmax,Hsquareguard,Hpairsguard,Hpairs,Hbudget.
  change (Z.of_nat (S root*S root)<=18446744073709551614/5) in Hpairsguard.
  assert (Hwidth : Z.of_nat root+1=Z.of_nat (S root)) by lia.
  assert (Hsquare : Z.of_nat (S root)*Z.of_nat (S root)=Z.of_nat (S root*S root)) by now rewrite Nat2Z.inj_mul.
  assert (Hbudgetvalue : Z.of_nat (S root*S root)*5+1=Z.of_nat (RenameMemoBounds.fuel root)).
  { unfold RenameMemoBounds.fuel. rewrite Nat2Z.inj_add,Nat2Z.inj_mul. cbn. lia. }
  assert (Hwidthword : word (Z.of_nat (S root))).
  { unfold word,maximum. nia. }
  assert (Hpairsword : word (Z.of_nat (S root*S root))) by exact Hpairs.
  assert (Hproductword : word (Z.of_nat (S root*S root)*5)).
  { unfold word,maximum. lia. }
  assert (Hfuelword : word (Z.of_nat (RenameMemoBounds.fuel root))) by exact Hbudget.
  set (args:=update (update (fun _=>0) vardef_0__push_node (Z.of_nat root))
    vardef_0__push_depth (nums f vardef_0__rename_initialDepth)).
  assert (Hpush : execObserved (funcdef_0__push (fun _=>false) args) (machine f,observations)=
    Some (tt,(StackExecution.push_state (machine f) 0 (Z.of_nat root) (nums f vardef_0__rename_initialDepth),observations))).
  { apply observed_plain; [apply InternalObservation.push_nf|]. apply StackExecution.generated_push.
    - lia.
    - exact Hstack.
    - unfold maximum. lia. }
  destruct f as [s bs ns]. cbn [machine nums] in *. unfold body_with.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine setNum];
      eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta])
    |progress rewrite Hroot |progress rewrite Hwidth |progress rewrite Hsquare |progress rewrite Hbudgetvalue
    |match goal with |- context [coerceInt ?value 64]=>progress rewrite (coerce_word value) by
       first [exact Hwidthword|exact Hpairsword|exact Hproductword|exact Hfuelword
        |rewrite Hwidth; exact Hwidthword|rewrite Hsquare; exact Hpairsword|rewrite Hbudgetvalue; exact Hfuelword] end
    |match goal with |- context [bool_decide ?P]=>progress rewrite (bool_decide_false P) by lia end
    |match goal with |- context [numbers.Z.eq_dec ?a ?b]=>destruct (numbers.Z.eq_dec a b); [exfalso; lia|] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools addInt multInt divIntUnsigned
      decide decide_rel]
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__push ?bp ?np) ?state]=>
      let expression:=constr:(@execObserved I T EI R (funcdef_0__push bp np) state) in
      assert (Hrun : expression=Some (tt,(StackExecution.push_state s 0 (Z.of_nat root) (ns vardef_0__rename_initialDepth),observations))) by exact Hpush;
      rewrite Hrun; clear Hrun end
  ].
  destruct (execLocalObserved (scan (Z.of_nat (RenameMemoBounds.fuel root)))
    (prepared {|machine:=s;bools:=bs;nums:=ns|} root,observations)) as [[[] after]|] eqn:Hrun;
    cbv beta iota zeta delta [prepared setMachine setNum machine nums bools] in Hrun; rewrite Hrun; reflexivity.
Qed.
Local Transparent finish.
Theorem generated_finish_empty (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 10 = 0 ->
  execLocalObserved finish (f,observations) = Some (tt,(f,observations)).
Proof.
  intros Hmeta Hempty. unfold finish.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hmeta)
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress rewrite Hempty |progress rewrite bool_decide_true by reflexivity
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
Theorem generated_finish_exhausted (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 10 <> 0 ->
  execLocalObserved finish (f,observations) = Some (tt,(setMachine f (store_meta (machine f) 8 1),observations)).
Proof.
  intros Hmeta Hnonempty. unfold finish.
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; first [exact Hmeta | eapply Nat.le_lt_trans with (m := 10%nat); [cbn; lia|exact Hmeta]])
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress rewrite bool_decide_true by exact Hnonempty
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
Theorem generated_iteration_empty (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 10 = 0 ->
  execLocalObserved iteration (f,observations) = Some (Stop,(f,observations)).
Proof.
  intros Hmeta Hempty. unfold iteration,iteration_at.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; exact Hmeta)
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress rewrite Hempty |progress rewrite bool_decide_true by reflexivity
    |progress cbn [dropWithinLoop Action_rect]
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
Theorem generated_iteration_failed (f : Frame) observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10 <> 0 -> meta_value (machine f) 8 <> 0 ->
  execLocalObserved iteration (f,observations) = Some (Stop,(f,observations)).
Proof.
  intros Hmeta Hnonempty Herror. unfold iteration,iteration_at.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine];
       first [exact Hmeta|eapply Nat.le_lt_trans with (m := 10%nat); [cbn; lia|exact Hmeta]])
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress rewrite bool_decide_false by exact Hnonempty
    |progress rewrite bool_decide_true by exact Herror
    |progress cbn [dropWithinLoop Action_rect]
    |progress cbv beta iota zeta delta [machine nums bools setMachine]
  ]. reflexivity.
Qed.
Theorem generated_initialized_preparation (f : Frame) root observations :
  (31<length (memory (machine f) arraydef_0__meta))%nat -> nums f vardef_0__rename_node=Z.of_nat root ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  execLocalObserved funcdef_0__rename_body (f,observations)=
  optionBind (execLocalObserved (loop (RenameMemoBounds.fuel root) iteration_at)
    (prepared (setMachine f (initialized (machine f))) root,observations))
    (fun response=>execLocalObserved finish (snd response)).
Proof.
  intros Hmeta Hroot Hfuel. rewrite RenameMemoInit.body_actual,RenameMemoInit.generated_prefix by exact Hmeta.
  rewrite actual_body.
  rewrite generated_preparation with (root:=root).
  - now rewrite Nat2Z.id.
  - cbn [machine setMachine]. now rewrite initialized_meta_length.
  - cbn [machine setMachine]. now apply initialized_stack.
  - destruct f. exact Hroot.
  - exact Hfuel.
Qed.
Theorem generated_start s bs ns root observations :
  (31<length (memory s arraydef_0__meta))%nat -> ns vardef_0__rename_node=Z.of_nat root ->
  Z.of_nat (RenameMemoBounds.fuel root)<=maximum ->
  let initial : Frame:={|machine:=s;bools:=bs;nums:=ns|} in
  execObserved (funcdef_0__rename bs ns) (s,observations)=
  optionBind (execLocalObserved (loop (RenameMemoBounds.fuel root) iteration_at)
    (prepared (setMachine initial (initialized s)) root,observations))
    (fun response=>optionBind (execLocalObserved finish (snd response))
      (fun final=>Some (fst final,(machine (fst (snd final)),snd (snd final))))).
Proof.
  intros Hmeta Hroot Hfuel initial. unfold funcdef_0__rename. rewrite ObservedLocal.eliminate_correct.
  rewrite generated_initialized_preparation with (root:=root) by assumption.
  subst initial. cbn [machine].
  destruct (execLocalObserved (loop (RenameMemoBounds.fuel root) iteration_at)
    (prepared (setMachine {|machine:=s;bools:=bs;nums:=ns|} (initialized s)) root,observations)) as [[[] after]|]; reflexivity.
Qed.
Lemma prepared_budget (f : Frame) root : nums (prepared f root) vardef_0__rename_budget=Z.of_nat (RenameMemoBounds.fuel root).
Proof. unfold prepared. destruct f. cbn [setMachine setNum nums machine]. apply updated_same. Qed.
End RenameMemoControl.
