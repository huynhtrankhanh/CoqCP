From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import Protocol.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives SchemaMetadata ArenaFrame.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module SchemaCheck.
Import IndexExecution SipHashExecution ObservedLocal.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__schemaCheck.
Definition rejected s := store_meta s 18 0.
Definition typed s (kind expected : Z) := if bool_decide (kind <> expected) then rejected s else s.
Definition checked s (kind width expected : Z) :=
  let t := typed s kind expected in
  if bool_decide (meta_value s 19 < width) then store_meta t 19 width else t.
Ltac primitives Hmeta Hbound :=
  repeat first [progress cbn [optionBind fst snd negb]
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; rewrite ?Nat2Z.id;
       first [exact Hbound|rewrite ?store_meta_length; eapply Nat.le_lt_trans with (m:=19%nat); [cbn; lia|exact Hmeta]])
    |progress replace (Z.to_nat 16) with 16%nat by reflexivity
    |progress replace (Z.to_nat 18) with 18%nat by reflexivity
    |progress replace (Z.to_nat 19) with 19%nat by reflexivity
    |progress rewrite Nat2Z.id
    |progress rewrite meta_store_other by lia
    |progress rewrite store_meta_other by discriminate
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update]
  ].
Theorem generated_missing_body (f : Frame) observations :
  (19 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 16 <= nums f vardef_0__schemaCheck_node ->
  execLocalObserved funcdef_0__schemaCheck_body (f,observations)=
    Some (tt,(setMachine f (rejected (machine f)),observations)).
Proof.
  intros Hmeta Hmissing. destruct f as [s bs ns]. cbn [machine nums] in *.
  unfold funcdef_0__schemaCheck_body.
  repeat first [progress primitives Hmeta Hmeta
    |progress rewrite bool_decide_false by lia]. reflexivity.
Qed.
Theorem generated_missing s bs ns observations :
  (19 < length (memory s arraydef_0__meta))%nat -> meta_value s 16 <= ns vardef_0__schemaCheck_node ->
  execObserved (funcdef_0__schemaCheck bs ns) (s,observations)=Some (tt,(rejected s,observations)).
Proof.
  intros Hmeta Hmissing. unfold funcdef_0__schemaCheck. rewrite eliminate_correct.
  pose proof (generated_missing_body {|machine:=s;bools:=bs;nums:=ns|} observations Hmeta Hmissing) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
Theorem generated_present_body (f : Frame) index raw expected observations :
  (19 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__schemaCheck_node=Z.of_nat index -> nums f vardef_0__schemaCheck_type=expected ->
  Z.of_nat index < meta_value (machine f) 16 ->
  nth_error (memory (machine f) arraydef_0__schemaNodes) index=Some raw ->
  execLocalObserved funcdef_0__schemaCheck_body (f,observations)=
    Some (tt,(setMachine f (checked (machine f) (snd (fst raw)) (snd raw) expected),observations)).
Proof.
  intros Hmeta Hindex Hexpected Hreference Hraw.
  assert (Hbound : (index < length (memory (machine f) arraydef_0__schemaNodes))%nat)
    by (apply nth_error_Some; congruence).
  pose proof (List.nth_error_nth _ _ (0,0,0,0,0,0,0) Hraw) as Hnth.
  destruct f as [s bs ns]. cbn [machine nums] in *.
  destruct (bool_decide (snd (fst raw) <> expected)) eqn:Hkind;
    destruct (bool_decide (meta_value s 19 < snd raw)) eqn:Hwidth;
    unfold funcdef_0__schemaCheck_body, checked, typed; rewrite Hkind,Hwidth;
    repeat first [progress primitives Hmeta Hbound
      |progress rewrite Hindex |progress rewrite Hexpected
      |match goal with |- context [List.nth ?i (memory ?source arraydef_0__schemaNodes) ?zero] =>
         let expression:=constr:(List.nth i (memory source arraydef_0__schemaNodes) zero) in
         let Hsame:=fresh in assert (Hsame : expression=raw) by exact Hnth; rewrite Hsame; clear Hsame end
      |progress rewrite Hkind |progress rewrite Hwidth
      |progress rewrite bool_decide_true by exact Hreference].
  all: reflexivity.
Qed.
Theorem generated_present s bs ns index raw expected observations :
  (19 < length (memory s arraydef_0__meta))%nat ->
  ns vardef_0__schemaCheck_node=Z.of_nat index -> ns vardef_0__schemaCheck_type=expected ->
  Z.of_nat index < meta_value s 16 -> nth_error (memory s arraydef_0__schemaNodes) index=Some raw ->
  execObserved (funcdef_0__schemaCheck bs ns) (s,observations)=
    Some (tt,(checked s (snd (fst raw)) (snd raw) expected,observations)).
Proof.
  intros Hmeta Hindex Hexpected Hreference Hraw. unfold funcdef_0__schemaCheck. rewrite eliminate_correct.
  pose proof (generated_present_body {|machine:=s;bools:=bs;nums:=ns|} index raw expected observations Hmeta Hindex Hexpected Hreference Hraw) as Hrun.
  unfold Frame in Hrun. rewrite Hrun. reflexivity.
Qed.
Lemma checked_flag s kind width expected : (19 < length (memory s arraydef_0__meta))%nat ->
  meta_value (checked s kind width expected) 18 =
    if bool_decide (kind <> expected) then 0 else meta_value s 18.
Proof.
  intro Hmeta. unfold checked,typed,rejected.
  destruct (bool_decide (kind<>expected)); destruct (bool_decide (meta_value s 19<width));
    rewrite ?meta_store_other by lia; try reflexivity; apply meta_store_same; lia.
Qed.
Lemma checked_width s kind width expected : (19 < length (memory s arraydef_0__meta))%nat ->
  meta_value (checked s kind width expected) 19=Z.max (meta_value s 19) width.
Proof.
  intro Hmeta. unfold checked,typed,rejected.
  destruct (bool_decide (meta_value s 19<width)) eqn:Hwidth;
    destruct (bool_decide (kind<>expected)); rewrite ?meta_store_same,?meta_store_other by (rewrite ?store_meta_length; lia).
  all: first [apply bool_decide_eq_true in Hwidth; rewrite Z.max_r by lia; reflexivity
    |apply bool_decide_eq_false in Hwidth; rewrite Z.max_l by lia; reflexivity].
Qed.
Lemma checked_storage s kind width expected : ArenaFrame.storage s (checked s kind width expected).
Proof.
  unfold checked,typed,rejected. destruct (bool_decide (meta_value s 19<width));
    destruct (bool_decide (kind<>expected)); ArenaFrame.storage_steps.
Qed.
(* The semantic contract is total over represented schema nodes: missing IDs
   clear the accumulated validation flag; existing nodes check their type and
   accumulate precisely the maximum dependency arity. *)
Definition semantic_result s expressions index expected :=
  match nth_error expressions index with
  | None => rejected s
  | Some expression => checked s (SchemaMetadata.kind expression)
      (Z.of_nat (SchemaMetadata.arity expression)) expected
  end.
Theorem generated_total s bs ns expressions index expected observations :
  (19 < length (memory s arraydef_0__meta))%nat -> SchemaMetadata.represents s expressions ->
  ns vardef_0__schemaCheck_node=Z.of_nat index -> ns vardef_0__schemaCheck_type=expected ->
  execObserved (funcdef_0__schemaCheck bs ns) (s,observations)=
    Some (tt,(semantic_result s expressions index expected,observations)).
Proof.
  intros Hmeta Hrep Hindex Hexpected. unfold semantic_result.
  destruct (nth_error expressions index) as [expression|] eqn:Hentry.
  - destruct (SchemaMetadata.represented_lookup s expressions index expression Hrep Hentry)
      as [raw [Hraw Hfields]].
    assert (Hreference : Z.of_nat index < meta_value s 16).
    { rewrite (proj1 Hrep). apply Nat2Z.inj_lt. apply nth_error_Some. congruence. }
    pose proof (generated_present s bs ns index raw expected observations Hmeta Hindex Hexpected Hreference Hraw) as Hrun.
    destruct raw as [[[[[[k a] b] c] d] kind] width].
    destruct Hfields as [Hkind [Hwidth Hword]]. cbn [fst snd] in Hrun.
    now rewrite Hkind,Hwidth in Hrun.
  - apply generated_missing; [exact Hmeta|]. rewrite Hindex,(proj1 Hrep).
    apply Nat2Z.inj_le. now apply nth_error_None in Hentry.
Qed.
Theorem semantic_flag s expressions index expected : (19 < length (memory s arraydef_0__meta))%nat ->
  meta_value (semantic_result s expressions index expected) 18=
    match nth_error expressions index with
    | None => 0
    | Some expression => if bool_decide (SchemaMetadata.kind expression <> expected) then 0 else meta_value s 18
    end.
Proof.
  intro Hmeta. unfold semantic_result. destruct (nth_error expressions index) as [expression|].
  - now apply checked_flag.
  - unfold rejected. apply meta_store_same. lia.
Qed.
Theorem semantic_width s expressions index expected : (19 < length (memory s arraydef_0__meta))%nat ->
  meta_value (semantic_result s expressions index expected) 19=
    match nth_error expressions index with
    | None => meta_value s 19
    | Some expression => Z.max (meta_value s 19) (Z.of_nat (SchemaMetadata.arity expression))
    end.
Proof.
  intro Hmeta. unfold semantic_result. destruct (nth_error expressions index) as [expression|].
  - now apply checked_width.
  - unfold rejected. apply meta_store_other. lia.
Qed.
Theorem semantic_storage s expressions index expected :
  ArenaFrame.storage s (semantic_result s expressions index expected).
Proof.
  unfold semantic_result. destruct (nth_error expressions index) as [expression|].
  - apply checked_storage.
  - unfold rejected. apply ArenaFrame.storage_meta; lia.
Qed.
Theorem preserves_schema s expressions index expected : SchemaMetadata.represents s expressions ->
  SchemaMetadata.represents (semantic_result s expressions index expected) expressions.
Proof.
  intro Hrep. apply (SchemaMetadata.transport s); [| |exact Hrep].
  - unfold semantic_result,checked,typed,rejected.
    destruct (nth_error expressions index) as [expression|];
      try destruct (bool_decide (meta_value s 19 < Z.of_nat (SchemaMetadata.arity expression)));
      try destruct (bool_decide (SchemaMetadata.kind expression <> expected));
      repeat rewrite meta_store_other by lia; reflexivity.
  - apply (proj1 (proj2 (semantic_storage s expressions index expected))); discriminate.
Qed.
End SchemaCheck.
