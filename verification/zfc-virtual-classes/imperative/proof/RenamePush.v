From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash InternTail ObservedLocal NativePrimitives RenameStructure RenameLeaf FrameReplace Stack RenameStack RenameFrames FormulaEncoding Representation HashTable ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenamePush.
Import RenameLeaf.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Definition arguments node depth : varsfuncdef_0__push -> Z :=
  update (update (fun _ => 0) vardef_0__push_node node) vardef_0__push_depth depth.
Definition parent_phase tag := if Z.eq_dec tag 3 then 1 else 3.
Definition child_depth tag depth := if Z.eq_dec tag 3 then depth else coerceInt (depth + 1) 64.
Definition result (f : Frame) pushedstate top root depth left_id tag a b :=
  setMachine (RenameLeaf.loaded f top root depth 0 left_id tag a b) pushedstate.
Local Opaque funcdef_0__intern funcdef_0__push funcdef_0__renameIndex.
Theorem generated_fresh (f : Frame) pushedstate top root depth left_id tag a b observations :
  (tag = 3 \/ tag = 4) -> (tag = 4 -> depth < maximum) ->
  (10 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10 = Z.of_nat (S top) -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (S top) <= maximum ->
  (top < length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,depth,0,left_id) ->
  (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0) = (tag,a,b) ->
  execObserved (funcdef_0__push (fun _ => false) (arguments a (child_depth tag depth)))
    (FrameReplace.write (machine f) top (root,depth,parent_phase tag,0),observations) = Some (tt,(pushedstate,observations)) ->
  execLocalObserved iteration (f,observations) = Some (KeepGoing,(result f pushedstate top root depth left_id tag a b,observations)).
Proof.
  intros Htag Hdepth Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hpush.
  assert (Htop : coerceInt (Z.of_nat (S top) - 1) 64 = Z.of_nat top).
  { replace (Z.of_nat (S top) - 1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. split; lia. }
  destruct Htag as [Htag|Htag]; subst tag; destruct f as [s bs ns]; cbn [machine] in *; unfold iteration.
  all:
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       lazymatch name with
       |arraydef_0__meta => first [exact Hmeta|eapply Nat.le_lt_trans with (m := 10%nat); [cbn; lia|exact Hmeta]]
       |arraydef_0__frames => first [exact Hframes|rewrite Nat2Z.id; exact Hframes]
       |arraydef_0__formulas => exact Hformulas end)
    |match goal with |- context [List.nth ?index (memory ?source arraydef_0__frames) ?zero] =>
       let expression := constr:(List.nth index (memory source arraydef_0__frames) zero) in
       let Hsame := fresh "Hsame" in assert (Hsame : expression = (root,depth,0,left_id)) by exact Hframe;
       rewrite Hsame; clear Hsame end
    |match goal with |- context [List.nth ?index (memory ?source arraydef_0__formulas) ?zero] =>
       let expression := constr:(List.nth index (memory source arraydef_0__formulas) zero) in
       let Hsame := fresh "Hsame" in first
         [assert (Hsame : expression = (3,a,b)) by exact Hformula
         |assert (Hsame : expression = (4,a,b)) by exact Hformula];
       rewrite Hsame; clear Hsame end
    |match goal with |- context [dropWithinLoop (bind (Done _ _ _ ?value) ?next)] =>
       let expression := constr:(dropWithinLoop (bind (Done _ _ _ value) next)) in
       change expression with (dropWithinLoop (next value)) end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__push ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__push bi ni) state) in
       let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(pushedstate,observations))) by exact Hpush;
       rewrite Hrun; clear Hrun end
    |progress rewrite Nat2Z.id
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror |progress rewrite Htop |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; unfold maximum in *; first [lia|pose proof (Hdepth eq_refl); lia])
       |progress rewrite (bool_decide_false P) by (try congruence; unfold maximum in *; first [lia|pose proof (Hdepth eq_refl); lia])] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools Imperative.update subInt addInt]
   ]. all: unfold result,RenameLeaf.loaded; reflexivity.
Qed.
End RenamePush.
