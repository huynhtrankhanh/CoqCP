From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash InternTail ObservedLocal NativePrimitives RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoFalsity RenameMemoJoin RenameMemoInvariant IndexFrame RenameStack RenameFrames FormulaEncoding Representation HashTable ArenaFrame.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoAtom.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Definition intern_arguments tag a b : varsfuncdef_0__intern -> Z :=
  update (update (update (fun _ => 0) vardef_0__intern_tag tag) vardef_0__intern_a a) vardef_0__intern_b b.
Definition result (f : Frame) stored top root depth left_id tag a b mapped_a mapped_b :=
  setMachine (setNum (setNum (RenameMemoHit.loaded f top root depth 0 left_id tag a b)
    vardef_0__rename_a mapped_a) vardef_0__rename_b mapped_b) stored.
Local Opaque funcdef_0__intern funcdef_0__push funcdef_0__renameIndex funcdef_0__renameCacheGet funcdef_0__renameCachePut Imperative.update.
Theorem generated_atom_composition (f : Frame) looked first second internstate stored top root depth left_id tag a b mapped_a mapped_b mode shift arg observations :
  (tag = 1 \/ tag = 2) ->
  nums f vardef_0__rename_mode = mode -> nums f vardef_0__rename_shift = shift -> nums f vardef_0__rename_arg = arg ->
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10 = Z.of_nat (S top) -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (S top) <= maximum ->
  (top < length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,depth,0,left_id) ->
  (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0) = (tag,a,b) ->
  execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root depth))
    (machine f,observations)=Some (tt,(looked,observations)) ->
  (31<length (memory looked arraydef_0__meta))%nat -> meta_value looked 31=maximum -> meta_value looked 8=0 ->
  execObserved (funcdef_0__renameIndex (fun _ => false) (IndexFrame.native_arguments a depth mode shift arg))
    (looked,observations) = Some (tt,(first,observations)) ->
  (31 < length (memory first arraydef_0__meta))%nat -> meta_value first 0 = mapped_a ->
  execObserved (funcdef_0__renameIndex (fun _ => false) (IndexFrame.native_arguments b depth mode shift arg))
    (first,observations) = Some (tt,(second,observations)) ->
  (31 < length (memory second arraydef_0__meta))%nat -> meta_value second 0 = mapped_b ->
  execObserved (funcdef_0__intern (fun _ => false) (intern_arguments tag mapped_a mapped_b))
    (second,observations) = Some (tt,(internstate,observations)) ->
  (31 < length (memory internstate arraydef_0__meta))%nat ->
  meta_value internstate 8=0 ->
  execObserved (funcdef_0__renameCachePut (fun _=>false)
    (RenameMemoFalsity.arguments root depth (meta_value internstate 0)))
    (RenameMemoJoin.popped internstate top,observations)=Some (tt,(stored,observations)) ->
  execLocalObserved iteration (f,observations) = Some (KeepGoing,(result f stored top root depth left_id tag a b mapped_a mapped_b,observations)).
Proof.
  intros Htag Hmode Hshift Harg Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hlookup Hlookmeta Hmiss Hlookerror Hfirst Hfirstmeta Hmapped_a Hsecond Hsecondmeta Hmapped_b Hintern Hpostmeta Hposterror Hput.
  assert (Htop : coerceInt (Z.of_nat (S top) - 1) 64 = Z.of_nat top).
  { replace (Z.of_nat (S top) - 1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. split; lia. }
  destruct Htag as [Htag|Htag]; subst tag; destruct f as [s bs ns]; cbn [machine nums] in *; unfold iteration,iteration_at.
  all:
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       lazymatch name with
       |arraydef_0__meta => eapply Nat.le_lt_trans with (m := 31%nat); [cbn; lia|first [exact Hpostmeta|exact Hsecondmeta|exact Hfirstmeta|exact Hlookmeta|exact Hmeta]]
       |arraydef_0__frames => first [exact Hframes|rewrite Nat2Z.id; exact Hframes]
       |arraydef_0__formulas => exact Hformulas end)
    |match goal with |- context [List.nth ?index (memory ?source arraydef_0__frames) ?zero] =>
       let expression := constr:(List.nth index (memory source arraydef_0__frames) zero) in
       let Hsame := fresh "Hsame" in assert (Hsame : expression = (root,depth,0,left_id)) by exact Hframe;
       rewrite Hsame; clear Hsame end
    |match goal with |- context [List.nth ?index (memory ?source arraydef_0__formulas) ?zero] =>
       let expression := constr:(List.nth index (memory source arraydef_0__formulas) zero) in
       let Hsame := fresh "Hsame" in first
         [assert (Hsame : expression = (1,a,b)) by exact Hformula
         |assert (Hsame : expression = (2,a,b)) by exact Hformula];
       rewrite Hsame; clear Hsame end
    |match goal with |- context [dropWithinLoop (bind (Done _ _ _ ?value) ?next)] =>
       let expression := constr:(dropWithinLoop (bind (Done _ _ _ value) next)) in
       change expression with (dropWithinLoop (next value)) end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameCacheGet ?bp ?np) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__renameCacheGet bp np) state) in
       assert (Hrun : expression=Some (tt,(looked,observations))) by exact Hlookup; rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameCachePut ?bp ?np) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__renameCachePut bp np) state) in
       assert (Hrun : expression=Some (tt,(stored,observations))) by exact Hput; rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameIndex ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__renameIndex bi ni) state) in
       let Hrun := fresh "Hrun" in first
         [assert (Hrun : expression = Some (tt,(first,observations))) by exact Hfirst
         |assert (Hrun : expression = Some (tt,(second,observations))) by exact Hsecond];
       rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__intern ?bi ?ni) ?state] =>
       let expression := constr:(@execObserved I T EI R (funcdef_0__intern bi ni) state) in
       let Hrun := fresh "Hrun" in assert (Hrun : expression = Some (tt,(internstate,observations))) by exact Hintern;
       rewrite Hrun; clear Hrun end
    |progress rewrite meta_store_other by lia
    |progress rewrite Hmiss |progress rewrite Hlookerror |progress rewrite Hposterror
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |progress replace (Z.to_nat 31) with 31%nat by reflexivity
    |progress rewrite Hmode |progress rewrite Hshift |progress rewrite Harg
    |progress rewrite Hmapped_a |progress rewrite Hmapped_b
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror |progress rewrite Htop |progress rewrite Nat2Z.id
    |match goal with |- context [bool_decide ?P] => first
       [progress rewrite (bool_decide_true P) by (try congruence; unfold maximum in *; lia)
       |progress rewrite (bool_decide_false P) by (try congruence; unfold maximum in *; lia)] end
    |match goal with |- context [decide ?P] => first
       [progress rewrite (decide_True (P := P)) by congruence
       |progress rewrite (decide_False (P := P)) by congruence] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools subInt]
   ]. all: unfold result,RenameMemoHit.loaded; reflexivity.
Qed.
Theorem parameters (f : Frame) stored top root depth left_id tag a b mapped_a mapped_b :
  RenameMemoHit.parameters f (result f stored top root depth left_id tag a b mapped_a mapped_b).
Proof.
  intros variable Hin. repeat destruct Hin as [<-|Hin]; try contradiction;
    unfold result,RenameMemoHit.loaded; destruct f; cbv beta iota zeta delta [setMachine setNum nums bools machine];
    now repeat rewrite updated_other by discriminate.
Qed.
End RenameMemoAtom.
