From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift FormulaEncoding Representation RenameStack RenameFrames
  RenameMemoTable RenameMemoLookup RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant RenameMemoMeaning
  RenameMemoVisit RenameMemoHitRefinement RenameMemoFalsityRefinement RenameMemoFalsityAccounting RenameMemoAtomRefinement
  RenameMemoPushRefinement RenameMemoNextRefinement RenameMemoJoinRefinement RenameMemoContinuation RenameMemoState
  RenameMemoTransition RenameMemoNativeEvent RenameMemoAccounting ObservedLocal.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoStep.
Import IndexExecution SipHashExecution IndexSemantics ObservedLocal RenameMemoInit RenameMemoControl.
Definition post (f : Frame) fs count rho stack old_value target final next next_stack value size :=
  RenameMemoState.represents (machine final) next rho size next_stack value target /\
  (exists extra, next=fs++extra) /\ (length next<=S (length fs))%nat /\
  RenameMemoHit.parameters f final /\ (RenameStack.pending next_stack<RenameStack.pending stack)%nat /\
  RenameMemoTransition.step rho stack old_value next_stack value /\
  RenameMemoNativeEvent.event (machine f) fs count (machine final) next size stack next_stack.
Local Ltac pack final next stack value size Hrun Hstate Hextends Hgrowth Hparameters Hdecrease Hnative :=
  exists final,next,stack,value,size; split; [exact Hrun|];
  unfold post; split; [exact Hstate|]; split; [exact Hextends|]; split; [first [exact Hgrowth|Hgrowth]|];
  split; [exact Hparameters|]; split; [first [exact Hdecrease|Hdecrease]|]; split;
  [first [apply RenameMemoTransition.cached | apply RenameMemoTransition.expanded |
    match goal with Hleft : ?left = _, Hright : ?right = _ |- _ =>
      rewrite Hleft,Hright; apply RenameMemoTransition.expanded end |
    match goal with Hbody : ?body = _ |- _ => rewrite Hbody; apply RenameMemoTransition.expanded end]|first [exact Hnative|Hnative]].
Lemma same_arena fs : exists extra : list SetTheory.formula, fs=fs++extra.
Proof. exists []; now rewrite app_nil_r. Qed.
Theorem generated (f : Frame) fs m shift arg count task stack value target :
  nums f vardef_0__rename_mode=mode_number m -> nums f vardef_0__rename_shift=Z.of_nat shift ->
  nums f vardef_0__rename_arg=Z.of_nat arg ->
  RenameMemoState.represents (machine f) fs (renaming m shift arg) count (task::stack) value target ->
  RenameMemoState.resources (machine f) fs m shift arg count (task::stack) ->
  forall observations, exists final next next_stack next_value size,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    post f fs count (renaming m shift arg) (task::stack) value target final next next_stack next_value size.
Proof.
  intros Hmode Hshift Harg Hstate Hresources observations.
  pose proof Hstate as [Hvalid Harena Hframes Hready Hcorrect Hzero].
  pose proof Hresources as [Hcapacity Hroom Hshiftword Hargword Hfits Hindices].
  destruct task as [source depth|p q depth|p q depth left_value|p depth].
  - destruct (RenameMemoVisit.top_visit (machine f) fs source depth stack Harena Hframes) as [root [left_id Hview]].
    destruct (RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count) as [cached_value|] eqn:Hlookup.
    + assert (Hmeaning : RenameMemoMeaning.entry_meaning fs (renaming m shift arg) (root,Z.of_nat depth) cached_value).
      { exact (RenameMemoTable.scan_meaning (RenameMemoLookup.table (machine f)) count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg))
          (root,Z.of_nat depth) (RenameMemoLookup.hash_start (machine f) (root,Z.of_nat depth) count) count cached_value
          ltac:(pose proof (RenameMemoInvariant.capacity_minimum _ _ _ Hvalid); lia)
          (RenameMemoLookup.hash_start_bound (machine f) (root,Z.of_nat depth) count ltac:(pose proof (RenameMemoInvariant.capacity_minimum _ _ _ Hvalid); lia))
          (RenameMemoInvariant.entries_mean _ _ _ Hvalid) Hlookup). }
      pose proof Hmeaning as [_ [_ [Hcachedword _]]].
      destruct (RenameMemoHitRefinement.generated_cached_visit f fs (renaming m shift arg) source depth stack count root left_id cached_value observations
        Hvalid Harena Hframes Hview Hlookup) as (final & Hrun & Hvalid' & Harena' & Hframes' & Hresult & Hdenotes & Hstorage & Hparameters & Hpassive).
      assert (Hnewstate : RenameMemoState.represents (machine final) fs (renaming m shift arg) count stack
        (RenameStack.renamed (renaming m shift arg) depth source) target).
      { apply RenameMemoState.completed with (fs:=fs); try assumption; [now rewrite Hresult|apply same_arena]. }
      assert (Hdecrease : (RenameStack.pending stack<RenameStack.pending (RenameStack.visit source depth::stack))%nat).
      { pose proof (RenameStack.work_positive source). cbn [RenameStack.pending RenameStack.frame_work]. lia. }
      pack final fs stack (RenameStack.renamed (renaming m shift arg) depth source) count Hrun Hnewstate
        (same_arena fs) ltac:(lia) Hparameters Hdecrease
        ltac:(apply RenameMemoNativeEvent.cached; [exact Hpassive|reflexivity|lia]).
    + pose proof (RenameMemoVisit.root_word _ _ _ _ _ _ _ Hview) as Hrootword.
      pose proof (RenameMemoVisit.source_entry _ _ _ _ _ _ _ Hview) as Hsource.
      pose proof (proj1 (proj2 (proj2 Harena))) as Hunique.
      assert (Hmisses : RenameMemoNativeEvent.misses (machine f) fs count source depth).
      { eapply RenameMemoNativeEvent.misses_source; eassumption. }
      destruct source as [|i j|i j|p q|p]; cbn [RenameMemoState.atomic_bounds] in Hindices.
      * destruct (RenameMemoFalsityAccounting.generated_fresh_miss f fs (renaming m shift arg) depth stack count root left_id observations
          Hvalid Harena Hzero Hframes Hview Hlookup Hfits)
          as (final & size & Hrun & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hstorage & Hparameters & Hcomplete).
        assert (Hnewstate : RenameMemoState.represents (machine final) fs (renaming m shift arg) size stack SetTheory.falsity target).
        { apply RenameMemoState.completed with (fs:=fs); try assumption.
          - rewrite Hresult. unfold word,maximum. lia.
          - now rewrite Hresult.
          - apply same_arena. }
        pack final fs stack SetTheory.falsity size Hrun Hnewstate (same_arena fs) ltac:(lia) Hparameters
          ltac:(cbn [RenameStack.pending RenameStack.frame_work RenameStack.work]; lia)
          ltac:(apply RenameMemoNativeEvent.leaf; [exact I|exact Hmisses|unfold RenameMemoNativeEvent.completes;
            apply RenameMemoAccounting.completed_source with (root:=root); assumption|lia]).
      * destruct Hindices as [Hi [Hj [Hmi Hmj]]].
        destruct (RenameMemoAtomRefinement.generated_atom_miss f 1 fs i j depth stack m shift arg count root left_id observations
          ltac:(now left) Hmode Hshift Harg Hvalid Harena Hcapacity Hframes Hview Hlookup Hi Hj Hshiftword Hargword Hmi Hmj Hfits)
          as (final & next & index & size & Hrun & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hparameters & Hgrowth & Hcomplete).
        assert (Hnewstate : RenameMemoState.represents (machine final) next (renaming m shift arg) size stack
          (RenameStack.renamed (renaming m shift arg) depth (SetTheory.equal i j)) target).
        { apply RenameMemoState.completed with (fs:=fs); try assumption.
          - now rewrite Hresult.
          - now rewrite Hresult,Nat2Z.id. }
        pack final next stack (RenameStack.renamed (renaming m shift arg) depth (SetTheory.equal i j)) size Hrun Hnewstate Hextends Hgrowth Hparameters
          ltac:(cbn [RenameStack.pending RenameStack.frame_work RenameStack.work]; lia)
          ltac:(apply RenameMemoNativeEvent.leaf; [exact I|exact Hmisses|unfold RenameMemoNativeEvent.completes;
            apply RenameMemoAccounting.completed_source with (root:=root); assumption|exact Hgrowth]).
      * destruct Hindices as [Hi [Hj [Hmi Hmj]]].
        destruct (RenameMemoAtomRefinement.generated_atom_miss f 2 fs i j depth stack m shift arg count root left_id observations
          ltac:(now right) Hmode Hshift Harg Hvalid Harena Hcapacity Hframes Hview Hlookup Hi Hj Hshiftword Hargword Hmi Hmj Hfits)
          as (final & next & index & size & Hrun & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hparameters & Hgrowth & Hcomplete).
        assert (Hnewstate : RenameMemoState.represents (machine final) next (renaming m shift arg) size stack
          (RenameStack.renamed (renaming m shift arg) depth (SetTheory.member i j)) target).
        { apply RenameMemoState.completed with (fs:=fs); try assumption.
          - now rewrite Hresult.
          - now rewrite Hresult,Nat2Z.id. }
        pack final next stack (RenameStack.renamed (renaming m shift arg) depth (SetTheory.member i j)) size Hrun Hnewstate Hextends Hgrowth Hparameters
          ltac:(cbn [RenameStack.pending RenameStack.frame_work RenameStack.work]; lia)
          ltac:(apply RenameMemoNativeEvent.leaf; [exact I|exact Hmisses|unfold RenameMemoNativeEvent.completes;
            apply RenameMemoAccounting.completed_source with (root:=root); assumption|exact Hgrowth]).
      * destruct (RenameMemoPushRefinement.generated_fresh_miss f 3 fs (renaming m shift arg) p q depth stack count root left_id observations
          ltac:(now left) ltac:(discriminate) Hvalid Hroom Harena Hframes Hview Hlookup)
          as (final & Hrun & Harena' & Hframes' & Hvalid' & Hparameters & Hpassive).
        assert (Hnewstate : RenameMemoState.represents (machine final) fs (renaming m shift arg) count
          (RenameStack.visit p depth::RenameStack.left_done p q depth::stack) value target).
        { apply RenameMemoState.scheduled; try assumption. cbn [RenameMemoContinuation.correct]. now split. }
        pack final fs (RenameStack.visit p depth::RenameStack.left_done p q depth::stack) value count Hrun Hnewstate (same_arena fs) ltac:(lia) Hparameters
          ltac:(cbn [RenameStack.pending RenameStack.frame_work RenameStack.work]; lia)
          ltac:(apply RenameMemoNativeEvent.binary; [exact Hmisses|exact Hpassive|reflexivity|lia]).
      * destruct (RenameMemoPushRefinement.generated_fresh_miss f 4 fs (renaming m shift arg) p SetTheory.falsity depth stack count root left_id observations
          ltac:(now right) ltac:(intro; exact Hindices) Hvalid Hroom Harena Hframes Hview Hlookup)
          as (final & Hrun & Harena' & Hframes' & Hvalid' & Hparameters & Hpassive).
        assert (Hnewstate : RenameMemoState.represents (machine final) fs (renaming m shift arg) count
          (RenameStack.visit p (S depth)::RenameStack.body_done p depth::stack) value target).
        { apply RenameMemoState.scheduled; try assumption. cbn [RenameMemoContinuation.correct]. now split. }
        pack final fs (RenameStack.visit p (S depth)::RenameStack.body_done p depth::stack) value count Hrun Hnewstate (same_arena fs) ltac:(lia) Hparameters
          ltac:(cbn [RenameStack.pending RenameStack.frame_work RenameStack.work]; lia)
          ltac:(apply RenameMemoNativeEvent.binder; [exact Hmisses|exact Hpassive|reflexivity|lia]).
  - destruct Hready as [Hcurrentword Hcurrent].
    destruct (RenameMemoNextRefinement.generated_next_refines f fs p q depth stack value (meta_value (machine f) 0) count (renaming m shift arg) observations
      Hvalid Hroom Harena Hframes eq_refl Hcurrentword Hcurrent)
      as (final & Hrun & Harena' & Hframes' & Hvalid' & Hparameters & Hpassive).
    assert (Hnewstate : RenameMemoState.represents (machine final) fs (renaming m shift arg) count
      (RenameStack.visit q depth::RenameStack.right_done p q depth value::stack) value target).
    { apply RenameMemoState.scheduled; try assumption. pose proof (RenameMemoContinuation.tick_preserves _ _ _ _ Hcorrect) as Hnext. exact Hnext. }
    pack final fs (RenameStack.visit q depth::RenameStack.right_done p q depth value::stack) value count Hrun Hnewstate (same_arena fs) ltac:(lia) Hparameters
      ltac:(cbn [RenameStack.pending RenameStack.frame_work]; lia)
      ltac:(apply RenameMemoNativeEvent.next; [exact Hpassive|reflexivity|lia]).
  - destruct Hready as [Hcurrentword Hcurrent].
    pose proof Hcorrect as [Hleft [Hright Htail]].
    destruct (RenameMemoJoinRefinement.generated_join f 2 fs (renaming m shift arg) p q depth stack left_value value (meta_value (machine f) 0) count observations
      ltac:(now left) Hvalid Harena Hcapacity Hframes eq_refl Hcurrentword Hcurrent ltac:(intro; now split) ltac:(discriminate) Hfits)
      as (final & next & index & size & internstate & Hrun & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hinternframe & Hstorage & Hparameters & Hgrowth & Hcomplete).
    assert (Hnewstate : RenameMemoState.represents (machine final) next (renaming m shift arg) size stack
      (RenameStack.renamed (renaming m shift arg) depth (SetTheory.implies p q)) target).
    { apply RenameMemoState.completed with (fs:=fs); try assumption.
      - now rewrite Hresult.
      - now rewrite Hresult,Nat2Z.id. }
    pack final next stack (RenameStack.renamed (renaming m shift arg) depth (SetTheory.implies p q)) size Hrun Hnewstate Hextends Hgrowth Hparameters
      ltac:(cbn [RenameStack.pending RenameStack.frame_work]; lia)
      ltac:(apply RenameMemoNativeEvent.joined; [exact Hcomplete|exact Hgrowth]).
  - destruct Hready as [Hcurrentword Hcurrent].
    pose proof Hcorrect as [Hbody Htail].
    destruct (RenameMemoJoinRefinement.generated_join f 3 fs (renaming m shift arg) p SetTheory.falsity depth stack SetTheory.falsity value (meta_value (machine f) 0) count observations
      ltac:(now right) Hvalid Harena Hcapacity Hframes eq_refl Hcurrentword Hcurrent ltac:(discriminate) ltac:(intro; exact Hbody) Hfits)
      as (final & next & index & size & internstate & Hrun & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hinternframe & Hstorage & Hparameters & Hgrowth & Hcomplete).
    assert (Hnewstate : RenameMemoState.represents (machine final) next (renaming m shift arg) size stack
      (RenameStack.renamed (renaming m shift arg) depth (SetTheory.all p)) target).
    { apply RenameMemoState.completed with (fs:=fs); try assumption.
      - now rewrite Hresult.
      - now rewrite Hresult,Nat2Z.id. }
    pack final next stack (RenameStack.renamed (renaming m shift arg) depth (SetTheory.all p)) size Hrun Hnewstate Hextends Hgrowth Hparameters
      ltac:(cbn [RenameStack.pending RenameStack.frame_work]; lia)
      ltac:(apply RenameMemoNativeEvent.closed; [exact Hcomplete|exact Hgrowth]).
Qed.
End RenameMemoStep.
