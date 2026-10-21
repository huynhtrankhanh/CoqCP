From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash RenameMemoTable RenameMemoLookup RenameMemoCapacity RenameMemoInit RenameMemoControl
  RenameMemoHit RenameMemoPut RenameMemoInvariant ObservedLocal Observation NativePrimitives.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoFalsity.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Definition arguments root depth value:=update (update (update (fun _=>0) vardef_0__renameCachePut_node root)
  vardef_0__renameCachePut_depth depth) vardef_0__renameCachePut_value value.
Definition result_frame (f : Frame) final top root depth left_id:=
  setMachine (RenameMemoHit.loaded f top root depth 0 left_id 0 0 0) final.
Local Opaque funcdef_0__renameCacheGet funcdef_0__renameCachePut funcdef_0__intern funcdef_0__push funcdef_0__renameIndex Imperative.update.
Theorem generated_falsity_composition (f : Frame) looked final top root depth left_id observations :
  (31<length (memory (machine f) arraydef_0__meta))%nat ->
  meta_value (machine f) 10=Z.of_nat (S top) -> meta_value (machine f) 8=0 -> Z.of_nat (S top)<=maximum ->
  (top<length (memory (machine f) arraydef_0__frames))%nat ->
  List.nth top (memory (machine f) arraydef_0__frames) (0,0,0,0)=(root,depth,0,left_id) ->
  (Z.to_nat root<length (memory (machine f) arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)= (0,0,0) ->
  execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root depth)) (machine f,observations)=Some (tt,(looked,observations)) ->
  (31<length (memory looked arraydef_0__meta))%nat -> meta_value looked 31=maximum -> meta_value looked 8=0 ->
  execObserved (funcdef_0__renameCachePut (fun _=>false) (arguments root depth 0))
    (RenameMemoInvariant.completed looked top 0,observations)=Some (tt,(final,observations)) ->
  execLocalObserved iteration (f,observations)=Some (KeepGoing,(result_frame f final top root depth left_id,observations)).
Proof.
  intros Hmeta Hcount Herror Hword Hframes Hframe Hformulas Hformula Hlookup Hlookmeta Hmiss Hlookerror Hput.
  assert (Htop : coerceInt (Z.of_nat (S top)-1) 64=Z.of_nat top).
  { replace (Z.of_nat (S top)-1) with (Z.of_nat top) by lia. apply coerce_word. unfold word. lia. }
  destruct f as [s bs ns]. cbn [machine] in *. unfold iteration,iteration_at.
  repeat first [progress cbn [optionBind fst snd negb]
    |progress rewrite drop_assoc |progress rewrite drop_lift
    |NativePrimitives.primitive ltac:(fun frame name slot=>cbn [machine setMachine]; repeat rewrite store_meta_length;
      lazymatch name with
      |arraydef_0__meta=>first
        [eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hmeta]
        |eapply Nat.le_lt_trans with (m:=31%nat); [cbn; lia|exact Hlookmeta]]
      |arraydef_0__frames=>first [exact Hframes|rewrite Nat2Z.id; exact Hframes]
      |arraydef_0__formulas=>exact Hformulas end)
    |match goal with |- context [List.nth ?index (memory s arraydef_0__frames) ?zero]=>
      let expression:=constr:(List.nth index (memory s arraydef_0__frames) zero) in
      assert (Hsame : expression=(root,depth,0,left_id)) by exact Hframe; rewrite Hsame; clear Hsame end
    |match goal with |- context [List.nth ?index (memory s arraydef_0__formulas) ?zero]=>
      let expression:=constr:(List.nth index (memory s arraydef_0__formulas) zero) in
      assert (Hsame : expression= (0,0,0)) by exact Hformula; rewrite Hsame; clear Hsame end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameCacheGet ?bp ?np) ?state]=>
      let expression:=constr:(@execObserved I T EI R (funcdef_0__renameCacheGet bp np) state) in
      assert (Hrun : expression=Some (tt,(looked,observations))) by exact Hlookup; rewrite Hrun; clear Hrun end
    |match goal with |- context [@execObserved ?I ?T ?EI ?R (funcdef_0__renameCachePut ?bp ?np) ?state]=>
      let expression:=constr:(@execObserved I T EI R (funcdef_0__renameCachePut bp np) state) in
      assert (Hrun : expression=Some (tt,(final,observations))) by exact Hput; rewrite Hrun; clear Hrun end
    |progress rewrite meta_store_other by lia
    |progress rewrite meta_store_same by (repeat rewrite store_meta_length; lia)
    |progress rewrite Hmiss |progress rewrite Hlookerror
    |match goal with |- context [dropWithinLoop (bind (Done _ _ _ ?value) ?next)]=>
      let expression:=constr:(dropWithinLoop (bind (Done _ _ _ value) next)) in change expression with (dropWithinLoop (next value)) end
    |progress replace (Z.to_nat 31) with 31%nat by reflexivity
    |progress replace (Z.to_nat 10) with 10%nat by reflexivity
    |progress replace (Z.to_nat 8) with 8%nat by reflexivity
    |progress replace (Z.to_nat 0) with 0%nat by reflexivity
    |progress rewrite Hcount |progress rewrite Herror |progress rewrite Htop |progress rewrite Nat2Z.id
    |progress rewrite updated_same |progress rewrite updated_other by discriminate
    |match goal with |- context [bool_decide ?P]=>first
      [progress rewrite (bool_decide_true P) by (try congruence; unfold maximum in *; lia)
      |progress rewrite (bool_decide_false P) by (try congruence; unfold maximum in *; lia)] end
    |progress cbv beta iota zeta delta [machine setMachine setNum nums bools subInt]
  ]. unfold result_frame,RenameMemoHit.loaded. reflexivity.
Qed.
Lemma arguments_values root depth value :
  arguments root depth value vardef_0__renameCachePut_node=root /\
  arguments root depth value vardef_0__renameCachePut_depth=depth /\
  arguments root depth value vardef_0__renameCachePut_value=value.
Proof.
  unfold arguments. repeat split; repeat first [rewrite updated_same|rewrite updated_other by discriminate]; reflexivity.
Qed.
Theorem generated_falsity s bs ns top root depth left_id count observations meaning :
  RenameMemoInvariant.valid s count meaning ->
  meta_value s 10=Z.of_nat (S top) -> Z.of_nat (S top)<=maximum ->
  (top<length (memory s arraydef_0__frames))%nat ->
  List.nth top (memory s arraydef_0__frames) (0,0,0,0)=(root,depth,0,left_id) ->
  (Z.to_nat root<length (memory s arraydef_0__formulas))%nat ->
  List.nth (Z.to_nat root) (memory s arraydef_0__formulas) (0,0,0)=(0,0,0) ->
  RenameMemoLookup.lookup s (root,depth) count=None ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  meaning (root,depth) 0 ->
  exists final size, execLocalObserved iteration ({|machine:=s;bools:=bs;nums:=ns|},observations)=Some (KeepGoing,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ RenameMemoInvariant.valid (machine final) size meaning /\
    meta_value (machine final) 0=0 /\ meta_value (machine final) 10=Z.of_nat top /\
    RenameMemoInvariant.storage_frame s (machine final) /\ RenameMemoHit.parameters {|machine:=s;bools:=bs;nums:=ns|} final.
Proof.
  intros Hvalid Hcount Hword Hframes Hframe Hformulas Hformula Hnone Hfits Hmeaning.
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity Hmin HcapWord Hmemo Hlive Hload Hentries Hindexed].
  set (looked:=RenameMemoLookup.result_state s (root,depth) count).
  set (popped:=RenameMemoInvariant.completed looked top 0).
  assert (Hlookup : execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root depth)) (s,observations)=Some (tt,(looked,observations))).
  { pose proof (RenameMemoLookup.generated_lookup_exact s (fun _=>false) (RenameMemoHit.arguments root depth) count observations
      Hmeta Hsip Hpositive Hcapacity ltac:(lia) HcapWord Hmemo) as Hrun.
    cbv beta iota zeta delta [RenameMemoHit.arguments] in Hrun.
    rewrite updated_same,updated_other,updated_same in Hrun by discriminate. exact Hrun. }
  assert (Hlookvalid : RenameMemoInvariant.valid looked count meaning) by (now apply RenameMemoInvariant.lookup_valid).
  assert (Hpopvalid : RenameMemoInvariant.valid popped count meaning) by (now apply RenameMemoInvariant.completed_valid).
  assert (Hmiss : meta_value looked 31=maximum).
  { unfold looked. rewrite RenameMemoLookup.result_value,Hnone by exact Hmeta. reflexivity. }
  assert (Hcounter : meta_value popped 30=meta_value s 30).
  { unfold popped,RenameMemoInvariant.completed. rewrite !meta_store_other by lia.
    destruct (RenameMemoLookup.result_frame s (root,depth) count) as [_ [Hm _]]. now apply Hm. }
  assert (Hpopfits : Z.of_nat count/2<=meta_value popped 30 -> Z.of_nat count<=9223372036854775807).
  { now rewrite Hcounter. }
  assert (Hresult : meaning (arguments root depth 0 vardef_0__renameCachePut_node,arguments root depth 0 vardef_0__renameCachePut_depth)
    (arguments root depth 0 vardef_0__renameCachePut_value)).
  { destruct (arguments_values root depth 0) as [Hnode [Hdepth Hvalue]]. now rewrite Hnode,Hdepth,Hvalue. }
  destruct (RenameMemoInvariant.generated_put popped (fun _=>false) (arguments root depth 0) count observations meaning
    Hpopvalid Hpopfits Hresult) as [stored [size [Hput [Hchoice [Hstored Hputframe]]]]].
  exists (result_frame {|machine:=s;bools:=bs;nums:=ns|} stored top root depth left_id),size. split.
  - apply generated_falsity_composition with (looked:=looked); try assumption.
    + exact (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid).
    + exact (RenameMemoInvariant.error_clear _ _ _ Hlookvalid).
  - split; [exact Hchoice|]. split; [exact Hstored|].
    destruct Hputframe as [Ha [Hm [Hl [Hs [Hi Ho]]]]]. split.
    + change (meta_value stored 0=0). rewrite Hm by lia. unfold popped,RenameMemoInvariant.completed.
      rewrite meta_store_other by lia. apply meta_store_same. exact (Nat.lt_trans 0 31 _ ltac:(lia)
        (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid)).
    + split.
      * change (meta_value stored 10=Z.of_nat top). rewrite Hm by lia. unfold popped,RenameMemoInvariant.completed.
        apply meta_store_same. rewrite store_meta_length. pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid). lia.
      * split.
        -- apply RenameMemoInvariant.storage_trans with (t:=looked); [apply RenameMemoInvariant.lookup_storage|].
           apply RenameMemoInvariant.storage_trans with (t:=popped); [apply RenameMemoInvariant.completed_storage|].
           apply RenameMemoInvariant.inserted_storage. unfold RenameMemoPut.storage_frame. repeat split; assumption.
        -- exact (RenameMemoHit.hit_parameters {|machine:=s;bools:=bs;nums:=ns|} stored top root depth left_id 0 0 0).
Qed.
End RenameMemoFalsity.
