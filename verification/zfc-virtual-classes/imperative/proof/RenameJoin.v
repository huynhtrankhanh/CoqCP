From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash InternTail ObservedLocal NativePrimitives RenameLeaf RenameStructure RenameStack RenameFrames FormulaEncoding Representation HashTable ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameJoin.
Import RenameLeaf.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Definition arguments phase left_id right_id : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _ => 0) vardef_0__intern_tag (if Z.eq_dec phase 2 then 3 else 4))
    vardef_0__intern_a (if Z.eq_dec phase 2 then left_id else right_id))
    vardef_0__intern_b (if Z.eq_dec phase 2 then right_id else 0).
Definition result (f : Frame) internstate top root depth phase left_id tag a b :=
  setMachine (RenameLeaf.loaded f top root depth phase left_id tag a b) (store_meta internstate 10 (Z.of_nat top)).
Local Opaque funcdef_0__intern funcdef_0__push funcdef_0__renameIndex.
Theorem generated_join (f : Frame) internstate top root depth phase left_id right_id tag a b observations :
  (phase = 2 \/ phase = 3) ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10 = Z.of_nat (S top) -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (S top) <= maximum ->
  (top < length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,depth,phase,left_id) ->
  (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0) = (tag,a,b) ->
  meta_value (machine f) 0 = right_id ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments phase left_id right_id))
    (machine f,observations) = Some (tt,(internstate,observations)) ->
  (10 < length (memory internstate arraydef_0__meta))%nat ->
  execLocalObserved iteration (f,observations) = Some (KeepGoing,(result f internstate top root depth phase left_id tag a b,observations)).
Proof.
  intros Hphase Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hright Hintern Hpostmeta.
  assert (Htop : coerceInt (Z.of_nat (S top) - 1) 64 = Z.of_nat top).
  { replace (Z.of_nat (S top) - 1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. split; lia. }
  destruct Hphase as [Hphase|Hphase]; subst phase; destruct f as [s bs ns]; cbn [machine] in *; unfold iteration.
  all:
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       lazymatch name with
       |arraydef_0__meta => first [exact Hpostmeta|exact Hmeta|eapply Nat.le_lt_trans with (m := 10%nat); [cbn; lia|exact Hmeta]]
       |arraydef_0__frames => first [exact Hframes|rewrite Nat2Z.id; exact Hframes]
       |arraydef_0__formulas => exact Hformulas end)
    |match goal with |- context [List.nth ?index (memory ?source arraydef_0__frames) ?zero] =>
       let expression := constr:(List.nth index (memory source arraydef_0__frames) zero) in
       let Hsame := fresh "Hsame" in first
         [assert (Hsame : expression = (root,depth,2,left_id)) by exact Hframe
         |assert (Hsame : expression = (root,depth,3,left_id)) by exact Hframe];
       rewrite Hsame; clear Hsame end
    |match goal with |- context [List.nth ?index (memory ?source arraydef_0__formulas) ?zero] =>
       let expression := constr:(List.nth index (memory source arraydef_0__formulas) zero) in
       let Hsame := fresh "Hsame" in assert (Hsame : expression = (tag,a,b)) by exact Hformula;
       rewrite Hsame; clear Hsame end
    |match goal with |- context [dropWithinLoop (bind (Done _ _ _ ?value) ?next)] =>
       let expression := constr:(dropWithinLoop (bind (Done _ _ _ value) next)) in
       change expression with (dropWithinLoop (next value)) end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(internstate,observations))) by exact Hintern;
       rewrite Hrun; clear Hrun end
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror |progress rewrite Htop |progress rewrite Hright |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update subInt]
   ]. all: unfold result,RenameLeaf.loaded; reflexivity.
Qed.
End RenameJoin.
