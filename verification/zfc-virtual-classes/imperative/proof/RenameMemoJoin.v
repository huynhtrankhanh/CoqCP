From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoFalsity RenameMemoInvariant RenameMemoPut
  ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoJoin.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Definition arguments phase left_id right_id : varsfuncdef_0__intern->Z :=
  update (update (update (fun _=>0) vardef_0__intern_tag (if Z.eq_dec phase 2 then 3 else 4))
    vardef_0__intern_a (if Z.eq_dec phase 2 then left_id else right_id))
    vardef_0__intern_b (if Z.eq_dec phase 2 then right_id else 0).
Definition popped s top:=store_meta s 10 (Z.of_nat top).
Definition result (f : Frame) stored top root depth phase left_id tag a b:=
  setMachine (RenameMemoHit.loaded f top root depth phase left_id tag a b) stored.
Local Opaque funcdef_0__intern funcdef_0__push funcdef_0__renameIndex funcdef_0__renameCacheGet funcdef_0__renameCachePut Imperative.update.
Theorem generated_join_composition (f : Frame) internstate stored top root depth phase left_id right_id tag a b observations :
  (phase = 2 \/ phase = 3) ->
  (31 < length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10 = Z.of_nat (S top) -> meta_value (machine f) 8 = 0 ->
  Z.of_nat (S top) <= maximum ->
  (top < length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,depth,phase,left_id) ->
  (Z.to_nat root < length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0) = (tag,a,b) ->
  meta_value (machine f) 0 = right_id ->
  execObserved (funcdef_0__intern (fun _ => false) (arguments phase left_id right_id))
    (machine f,observations) = Some (tt,(internstate,observations)) ->
  (31 < length (memory internstate arraydef_0__meta))%nat -> meta_value internstate 8=0 ->
  execObserved (funcdef_0__renameCachePut (fun _=>false) (RenameMemoFalsity.arguments root depth (meta_value internstate 0)))
    (popped internstate top,observations)=Some (tt,(stored,observations)) ->
  execLocalObserved iteration (f,observations) = Some (KeepGoing,(result f stored top root depth phase left_id tag a b,observations)).
Proof.
  intros Hphase Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hright Hintern Hpostmeta Hposterror Hput.
  assert (Htop : coerceInt (Z.of_nat (S top) - 1) 64 = Z.of_nat top).
  { replace (Z.of_nat (S top) - 1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. split; lia. }
  destruct Hphase as [Hphase|Hphase]; subst phase; destruct f as [s bs ns]; cbn [machine] in *; unfold iteration,iteration_at.
  all:
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite ObservedLocal.drop_assoc |progress rewrite ObservedLocal.drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot => cbn [machine setMachine]; repeat rewrite store_meta_length;
       lazymatch name with
       |arraydef_0__meta => first [eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta]
         |eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hpostmeta]]
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
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameCachePut ?bp ?np) ?state] =>
       let expression:=constr:(@execObserved I T EI R (funcdef_0__renameCachePut bp np) state) in
       assert (Hrun : expression=Some (tt,(stored,observations))) by exact Hput; rewrite Hrun; clear Hrun end
    |progress rewrite meta_store_other by lia
    |progress rewrite Hposterror
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
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
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools subInt]
   ]. all: unfold result,RenameMemoHit.loaded; reflexivity.
Qed.
Lemma popped_frame s top : RenameMemoHit.storage_frame s (popped s top).
Proof.
  unfold popped. split; [intros; now apply store_meta_other|]. split; [intros; now apply meta_store_other|].
  split; [apply store_meta_length|]. split; reflexivity.
Qed.
Lemma popped_valid s top count meaning : RenameMemoInvariant.valid s count meaning -> RenameMemoInvariant.valid (popped s top) count meaning.
Proof.
  intro Hvalid. apply RenameMemoInvariant.transport with (s:=s); [exact Hvalid|apply popped_frame|].
  unfold popped. now rewrite store_meta_other by discriminate.
Qed.
Lemma popped_storage s top : RenameMemoInvariant.storage_frame s (popped s top).
Proof.
  unfold popped. split; [intros; now apply store_meta_other|]. split; [intros; now apply meta_store_other|].
  split; [apply store_meta_length|]. split; [now rewrite store_meta_other by discriminate|]. split; reflexivity.
Qed.
Theorem parameters (f : Frame) stored top root depth phase left_id tag a b :
  RenameMemoHit.parameters f (result f stored top root depth phase left_id tag a b).
Proof.
  intros variable Hin. repeat destruct Hin as [<-|Hin]; try contradiction;
    unfold result,RenameMemoHit.loaded; destruct f; cbv beta iota zeta delta [setMachine setNum nums bools machine];
    now repeat rewrite updated_other by discriminate.
Qed.
Theorem generated_completion s root depth top count meaning observations : RenameMemoInvariant.valid s count meaning ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  meaning (root,depth) (meta_value s 0) ->
  exists stored size,
    execObserved (funcdef_0__renameCachePut (fun _=>false) (RenameMemoFalsity.arguments root depth (meta_value s 0)))
      (popped s top,observations)=Some (tt,(stored,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ RenameMemoInvariant.valid stored size meaning /\
    meta_value stored 0=meta_value s 0 /\ meta_value stored 10=Z.of_nat top /\
    RenameMemoPut.storage_frame (popped s top) stored /\ RenameMemoInvariant.storage_frame s stored.
Proof.
  intros Hvalid Hfits Hmeaning.
  assert (Hpopvalid : RenameMemoInvariant.valid (popped s top) count meaning) by now apply popped_valid.
  assert (Hpopfits : Z.of_nat count/2<=meta_value (popped s top) 30 -> Z.of_nat count<=9223372036854775807).
  { unfold popped. rewrite meta_store_other by lia. exact Hfits. }
  assert (Hresult : meaning
    (RenameMemoFalsity.arguments root depth (meta_value s 0) vardef_0__renameCachePut_node,
     RenameMemoFalsity.arguments root depth (meta_value s 0) vardef_0__renameCachePut_depth)
    (RenameMemoFalsity.arguments root depth (meta_value s 0) vardef_0__renameCachePut_value)).
  { destruct (RenameMemoFalsity.arguments_values root depth (meta_value s 0)) as [Hnode [Hdepth Hvalue]]. now rewrite Hnode,Hdepth,Hvalue. }
  destruct (RenameMemoInvariant.generated_put (popped s top) (fun _=>false) (RenameMemoFalsity.arguments root depth (meta_value s 0))
    count observations meaning Hpopvalid Hpopfits Hresult) as [stored [size [Hrun [Hchoice [Hstored Hframe]]]]].
  exists stored,size. split; [exact Hrun|]. split; [exact Hchoice|]. split; [exact Hstored|].
  pose proof Hframe as [Ha [Hm _]]. split.
  - rewrite Hm by lia. unfold popped. now rewrite meta_store_other by lia.
  - split.
    + rewrite Hm by lia. unfold popped. apply meta_store_same. pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hvalid). lia.
    + split; [exact Hframe|]. apply RenameMemoInvariant.storage_trans with (t:=popped s top); [apply popped_storage|].
      now apply RenameMemoInvariant.inserted_storage.
Qed.
End RenameMemoJoin.
