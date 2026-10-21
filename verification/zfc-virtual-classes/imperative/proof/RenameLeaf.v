From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash InternTail ObservedLocal NativePrimitives RenameStructure RenameStack RenameFrames FormulaEncoding Representation HashTable ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameLeaf.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Definition loaded (f : Frame) top root depth phase left_id tag a b :=
  setNum (setNum (setNum (setNum (setNum (setNum (setNum (setNum f
    vardef_0__rename_top (Z.of_nat top)) vardef_0__rename_current root)
    vardef_0__rename_depth depth) vardef_0__rename_phase phase) vardef_0__rename_left left_id)
    vardef_0__rename_tag tag) vardef_0__rename_a a) vardef_0__rename_b b.
Definition false_state (f : Frame) top root depth left_id := setMachine (loaded f top root depth 0 left_id 0 0 0)
  (store_meta (store_meta (machine f) 0 0) 10 (Z.of_nat top)).
Local Opaque funcdef_0__intern funcdef_0__push funcdef_0__renameIndex.
Theorem generated_falsity (f : Frame) top root depth left_id observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10 = Z.of_nat (S top) -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (S top) <= maximum ->
  (top < length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,depth,0,left_id) ->
  (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0) = (0,0,0) ->
  execLocalObserved iteration (f,observations) = Some (KeepGoing,(false_state f top root depth left_id,observations)).
Proof.
  intros Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula.
  assert (Htop : coerceInt (Z.of_nat (S top) - 1) 64 = Z.of_nat top).
  { replace (Z.of_nat (S top) - 1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. split; lia. }
  destruct f as [s bs ns]. cbn [machine] in *. unfold iteration.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       lazymatch name with
       |arraydef_0__meta => first [exact Hmeta|eapply Nat.le_lt_trans with (m := 10%nat); [cbn; lia|exact Hmeta]]
       |arraydef_0__frames => first [exact Hframes|rewrite Nat2Z.id; exact Hframes]
       |arraydef_0__formulas => exact Hformulas end)
    |match goal with |- context [List.nth ?index (memory s arraydef_0__frames) ?zero] =>
       let expression := constr:(List.nth index (memory s arraydef_0__frames) zero) in
       let Hsame := fresh "Hsame" in assert (Hsame : expression = (root,depth,0,left_id)) by exact Hframe;
       rewrite Hsame; clear Hsame end
    |match goal with |- context [List.nth ?index (memory s arraydef_0__formulas) ?zero] =>
       let expression := constr:(List.nth index (memory s arraydef_0__formulas) zero) in
       let Hsame := fresh "Hsame" in assert (Hsame : expression = (0,0,0)) by exact Hformula;
       rewrite Hsame; clear Hsame end
    |match goal with |- context [dropWithinLoop (bind (Done _ _ _ ?value) ?next)] =>
       let expression := constr:(dropWithinLoop (bind (Done _ _ _ value) next)) in
       change expression with (dropWithinLoop (next value)) end
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror |progress rewrite Htop |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update subInt]
  ]. unfold false_state,loaded. reflexivity.
Qed.
Lemma falsity_record s fs index : NativeRepresentation.canonical_arena s fs -> nth_error fs index = Some SetTheory.falsity ->
  (index < length (memory s arraydef_0__formulas))%nat /\
  List.nth index (memory s arraydef_0__formulas) (0,0,0) = (0,0,0).
Proof.
  intros [Htable [Hrep [Hunique Hnormal]]] Hlookup.
  assert (Hbound : (index < length fs)%nat) by (apply nth_error_Some; congruence).
  pose proof (NativeRepresentation.represented_lookup s fs index SetTheory.falsity Hrep Hlookup) as Hdecode.
  split.
  - pose proof (proj1 Htable) as [_ [_ [_ [_ [Hlength _]]]]]. lia.
  - exact (FormulaEncoding.decode_injective fs (HashTableInvariant.tuple_at s index) (0,0,0) SetTheory.falsity
      Hunique (Hnormal index Hbound) ltac:(left; auto) Hdecode eq_refl).
Qed.
Theorem generated_falsity_refines (f : Frame) fs depth stack observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.visit SetTheory.falsity depth :: stack) ->
  exists final, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) fs /\ RenameFrames.represents (machine final) fs stack /\
    meta_value (machine final) 0 = 0.
Proof.
  intros Hmeta Herror Harena Hstack.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct raw as [[[root raw_depth] phase] left_id]. cbn [RenameFrames.entry] in Hentry.
  destruct Hentry as [Hroot [Hdepth [Hdepth_eq [Hphase Hlookup]]]]; subst raw_depth phase.
  destruct (falsity_record (machine f) fs (Z.to_nat root) Harena Hlookup) as [Hbound Hnode].
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,Z.of_nat depth,0,left_id))
    by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  exists (false_state f (length stack) root (Z.of_nat depth) left_id).
  split; [now apply generated_falsity|]. split.
  - apply (ArenaFrame.storage_arena (machine f) _ fs); [|exact Harena].
    eapply ArenaFrame.storage_trans; apply ArenaFrame.storage_meta; lia.
  - split.
    + apply RenameFrames.pop with (task := RenameStack.visit SetTheory.falsity depth).
      * now rewrite store_meta_length.
      * eapply RenameFrames.transport; [apply meta_store_other; lia|apply store_meta_other; discriminate|exact Hstack].
    + change (meta_value (store_meta (store_meta (machine f) 0 0) 10 (Z.of_nat (length stack))) 0 = 0).
      rewrite meta_store_other by lia. apply meta_store_same. lia.
Qed.
End RenameLeaf.
