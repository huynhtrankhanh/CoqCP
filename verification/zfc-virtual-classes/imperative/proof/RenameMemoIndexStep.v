From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash Lift IndexFrame Intern InternGrowth InternLengths FormulaEncoding Representation
  RenameStack RenameFrames RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoTable RenameMemoLookup RenameMemoInvariant
  RenameMemoMeaning RenameMemoVisit RenameMemoHitRefinement RenameMemoIntern RenameMemoJoin RenameMemoAtom RenameMemoIndex RenameMemoStorage
  RenameMemoAccounting Observation ObservedLocal RenameMemoIndexBounds RenameMemoInput RenameMemoArenaPrefix SchemaEvaluationIndexBounds RenameMemoAtomRefinement RenameMemoJoinRefinement.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From NativeProof Require Import Index SipHash Lift FormulaEncoding Representation RenameStack RenameFrames
  RenameMemoTable RenameMemoLookup RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant RenameMemoMeaning
  RenameMemoVisit RenameMemoHitRefinement RenameMemoFalsityRefinement RenameMemoFalsityAccounting RenameMemoAtomRefinement
  RenameMemoPushRefinement RenameMemoNextRefinement RenameMemoJoinRefinement RenameMemoContinuation RenameMemoState
  RenameMemoTransition RenameMemoNativeEvent RenameMemoAccounting ObservedLocal RenameMemoStep.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameMemoIndexStep.
Import IndexExecution SipHashExecution IndexSemantics ObservedLocal RenameMemoInit RenameMemoControl.
Lemma same_semantics_raw before after fs bound :
 NativeRepresentation.canonical_arena before fs -> NativeRepresentation.canonical_arena after fs ->
 SchemaEvaluationIndexBounds.raw_arena before (length fs) bound ->
 SchemaEvaluationIndexBounds.raw_arena after (length fs) bound.
Proof.
 intros Hbefore Hafter Hraw node Hnode.
 rewrite (RenameMemoArenaPrefix.canonical_prefix before after fs [] Hbefore ltac:(now rewrite app_nil_r) node Hnode).
 exact (Hraw node Hnode).
Qed.
Module Atom.
Import RenameMemoAtomRefinement.
Theorem generated_atom_miss (f : Frame) tag fs i j depth stack m shift arg count root left_id target_bound observations :
  (tag=1 \/ tag=2) ->
  nums f vardef_0__rename_mode=mode_number m -> nums f vardef_0__rename_shift=Z.of_nat shift ->
  nums f vardef_0__rename_arg=Z.of_nat arg ->
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)) ->
  NativeRepresentation.canonical_arena (machine f) fs -> Z.of_nat (length fs)<=9223372036854775807 ->
  RenameFrames.represents (machine f) fs (RenameStack.visit (atom tag i j) depth::stack) ->
  RenameMemoVisit.view (machine f) fs (atom tag i j) depth stack root left_id ->
  RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count=None ->
  word (Z.of_nat i) -> word (Z.of_nat j) -> word (Z.of_nat shift) -> word (Z.of_nat arg) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) i)) ->
  word (Z.of_nat (under_binders depth (renaming m shift arg) j)) ->
  (Z.of_nat count/2<=meta_value (machine f) 30 -> Z.of_nat count<=9223372036854775807) ->
  SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) target_bound ->
  (under_binders depth (renaming m shift arg) i<=target_bound)%nat ->
  (under_binders depth (renaming m shift arg) j<=target_bound)%nat ->
  exists final next index size,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) target_bound /\
    (size=count \/ size=(2*count)%nat) /\
    RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (RenameStack.renamed (renaming m shift arg) depth (atom tag i j)) /\
    (exists extra, next=fs++extra) /\ RenameMemoHit.parameters f final /\ (length next<=S (length fs))%nat /\
    RenameMemoAccounting.completed (machine f) count (machine final) size (root,Z.of_nat depth).
Proof.
  intros Htag Hmode Hshift Harg Hvalid Harena Hcapacity Hstack Hview Hnone Hi Hj Hshiftword Hargword Hmapped_i Hmapped_j Hfits HrawArena Htarget_i Htarget_j.
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity0 Hmin HcapWord Hmemo Hlive Hload Hentries Hindexed].
  destruct Hview as [Hcount Hcountword Hroot Hdepth Hframes Hnth Hlookup Hnativebound].
  assert (Hsourcebound : (Z.to_nat root<length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hformula : List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)=(tag,Z.of_nat i,Z.of_nat j)).
  { apply (FormulaEncoding.decode_injective fs _ _ (atom tag i j) (proj1 (proj2 (proj2 Harena)))).
    - exact (proj2 (proj2 (proj2 Harena)) _ Hsourcebound).
    - now apply normal.
    - exact (NativeRepresentation.represented_lookup _ _ _ _ (proj1 (proj2 Harena)) Hlookup).
    - now apply decoded. }
  set (looked:=RenameMemoLookup.result_state (machine f) (root,Z.of_nat depth) count).
  assert (Hlookvalid : RenameMemoInvariant.valid looked count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)))
    by now apply RenameMemoInvariant.lookup_valid.
  assert (Hget : execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)))
    (machine f,observations)=Some (tt,(looked,observations))).
  { pose proof (RenameMemoLookup.generated_lookup_exact (machine f) (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)) count observations
      Hmeta Hsip Hpositive Hcapacity0 ltac:(lia) HcapWord Hmemo) as Hrun.
    cbv beta iota zeta delta [RenameMemoHit.arguments] in Hrun.
    rewrite updated_same,updated_other,updated_same in Hrun by discriminate. exact Hrun. }
  assert (Hmiss : meta_value looked 31=maximum).
  { unfold looked. rewrite RenameMemoLookup.result_value,Hnone by exact Hmeta. reflexivity. }
  assert (Hlookarena : NativeRepresentation.canonical_arena looked fs).
  { apply RenameMemoStorage.canonical_arena with (s:=machine f); [apply RenameMemoInvariant.lookup_storage|exact Harena]. }
  assert (Hlookframes : RenameFrames.represents looked fs (RenameStack.visit (atom tag i j) depth::stack)).
  { pose proof (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) as [Ha [Hm _]].
    apply RenameFrames.transport with (s:=machine f); [apply Hm; lia|apply Ha; discriminate|exact Hstack]. }
  set (first:=IndexFrame.result_state looked m (Z.of_nat i) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)).
  set (second:=IndexFrame.result_state first m (Z.of_nat j) (Z.of_nat depth) (Z.of_nat shift) (Z.of_nat arg)).
  set (mapped_i:=under_binders depth (renaming m shift arg) i).
  set (mapped_j:=under_binders depth (renaming m shift arg) j).
  assert (Hfirstvalid : RenameMemoInvariant.valid first count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)))
    by now apply RenameMemoIndex.index_valid.
  assert (Hsecondvalid : RenameMemoInvariant.valid second count (RenameMemoMeaning.entry_meaning fs (renaming m shift arg)))
    by now apply RenameMemoIndex.index_valid.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid) as Hlookmeta.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hfirstvalid) as Hfirstmeta.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hsecondvalid) as Hsecondmeta.
  assert (Hfirst : execObserved (funcdef_0__renameIndex (fun _=>false)
    (IndexFrame.native_arguments (Z.of_nat i) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
    (looked,observations)=Some (tt,(first,observations))).
  { apply IndexFrame.generated_native; try assumption; [lia|now rewrite index_semantics]. }
  assert (Hfirstvalue : meta_value first 0=Z.of_nat mapped_i).
  { unfold first,mapped_i. rewrite IndexFrame.result_value by lia. apply index_semantics. }
  assert (Hsecond : execObserved (funcdef_0__renameIndex (fun _=>false)
    (IndexFrame.native_arguments (Z.of_nat j) (Z.of_nat depth) (mode_number m) (Z.of_nat shift) (Z.of_nat arg)))
    (first,observations)=Some (tt,(second,observations))).
  { apply IndexFrame.generated_native; try assumption; [lia|now rewrite index_semantics]. }
  assert (Hsecondvalue : meta_value second 0=Z.of_nat mapped_j).
  { unfold second,mapped_j. rewrite IndexFrame.result_value by lia. apply index_semantics. }
  assert (Hsecondarena : NativeRepresentation.canonical_arena second fs)
    by (apply IndexFrame.result_arena; now apply IndexFrame.result_arena).
  assert (Hsecondframes : RenameFrames.represents second fs (RenameStack.visit (atom tag i j) depth::stack))
    by (apply IndexFrame.result_frames; now apply IndexFrame.result_frames).
  assert (Hnormal : FormulaEncoding.normal (tag,Z.of_nat mapped_i,Z.of_nat mapped_j)) by now apply normal.
  pose proof (decoded fs tag mapped_i mapped_j Htag) as Hdecode.
  destruct (RenameMemoIntern.generated second (fun _=>false) (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j))
    fs (atom tag mapped_i mapped_j) count (renaming m shift arg) observations Hsecondvalid Hsecondarena Hcapacity Hnormal Hdecode)
    as [internstate [next [index [Hintern [Hframe [Hnext [Hcache [Hindex [Hindexword [Hmeaning Hextends]]]]]]]]]].
  assert (HsecondIndices:SchemaEvaluationIndexBounds.raw_arena second (length fs) target_bound).
  { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HrawArena].
    unfold second,first,looked. rewrite !IndexFrame.result_other by discriminate.
    exact (proj1 (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) arraydef_0__formulas ltac:(discriminate) ltac:(discriminate)). }
  assert (HrawTuple:RenameMemoInput.raw_bound target_bound
    ((RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)) vardef_0__intern_tag,
     (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)) vardef_0__intern_a,
     (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)) vardef_0__intern_b)).
  { change (RenameMemoInput.raw_bound target_bound (tag,Z.of_nat mapped_i,Z.of_nat mapped_j)).
    unfold RenameMemoInput.raw_bound. rewrite !Nat2Z.id. intros _. split;assumption. }
  pose proof (SchemaEvaluationIndexBounds.observed_intern second internstate (fun _=>false)
    (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)) fs next target_bound observations observations
    Hsecondarena (RenameMemoInvariant.error_clear _ _ _ Hsecondvalid) Hcapacity HsecondIndices HrawTuple Hintern Hnext) as HinternIndices.
  assert (Hplain : exec (funcdef_0__intern (fun _=>false) (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j)))
    second=Some (tt,internstate)).
  { pose proof (execObserved_erases (funcdef_0__intern (fun _=>false) (RenameMemoAtom.intern_arguments tag (Z.of_nat mapped_i) (Z.of_nat mapped_j))) (second,observations)) as Herases. rewrite Hintern in Herases. exact (eq_sym Herases). }
  pose proof (InternGrowth.at_most_one second internstate _ _ fs next Hsecondarena
    (RenameMemoInvariant.error_clear _ _ _ Hsecondvalid) Hcapacity Hplain Hnext) as Hgrowth.
  assert (Hrenamed : atom tag mapped_i mapped_j=RenameStack.renamed (renaming m shift arg) depth (atom tag i j)).
  { symmetry. apply renamed_atom. exact Htag. }
  assert (Hentrymeaning : RenameMemoMeaning.entry_meaning next (renaming m shift arg) (root,Z.of_nat depth) (meta_value internstate 0)).
  { rewrite Hindex. split; [exact Hroot|]. split; [exact Hdepth|]. split; [exact Hindexword|]. exists (atom tag i j). split.
    - destruct Hextends as [extra ->]. now apply FormulaEncoding.nth_error_extend.
    - cbn [snd]. rewrite !Nat2Z.id. now rewrite <-Hrenamed. }
  assert (Hpostfits : Z.of_nat count/2<=meta_value internstate 30 -> Z.of_nat count<=9223372036854775807).
  { pose proof Hframe as [_ [Hm _]]. rewrite Hm by lia. unfold second,first.
    rewrite !IndexFrame.result_meta_other by lia. unfold looked.
    pose proof (RenameMemoLookup.result_frame (machine f) (root,Z.of_nat depth) count) as [_ [Hlookupmeta _]].
    rewrite Hlookupmeta by lia. exact Hfits. }
  destruct (RenameMemoAccounting.complete internstate root (Z.of_nat depth) (length stack) count
    (RenameMemoMeaning.entry_meaning next (renaming m shift arg)) observations Hcache Hpostfits Hentrymeaning)
    as (stored & size & Hput & Hchoice & Hstored & Hresult & Hpop & Hputframe & Hstorage & Hupper & Hnew & Hcovered).
  assert (HstoredIndices:SchemaEvaluationIndexBounds.raw_arena stored (length next) target_bound).
  { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HinternIndices].
    exact (proj1 Hstorage arraydef_0__formulas ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
  exists (RenameMemoAtom.result f stored (length stack) root (Z.of_nat depth) left_id tag (Z.of_nat i) (Z.of_nat j)
    (Z.of_nat mapped_i) (Z.of_nat mapped_j)),next,index,size. split.
  - eapply RenameMemoAtom.generated_atom_composition with (looked:=looked) (first:=first) (second:=second)
      (mode:=mode_number m) (shift:=Z.of_nat shift) (arg:=Z.of_nat arg); try eassumption.
    + exact (RenameMemoInvariant.error_clear _ _ _ Hlookvalid).
    + exact (RenameMemoInvariant.metadata_ready _ _ _ Hcache).
    + exact (RenameMemoInvariant.error_clear _ _ _ Hcache).
  - split;[exact HstoredIndices|]. split; [exact Hchoice|]. split; [exact Hstored|]. split.
    + now apply RenameMemoStorage.canonical_arena with (s:=internstate).
    + split.
      * apply RenameMemoStorage.popped_frames with (s:=internstate) (task:=RenameStack.visit (atom tag i j) depth); try assumption.
        -- pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hcache). lia.
        -- destruct Hframe as [Ha [Hm _]]. apply RenameFrames.transport with (s:=second).
           ++ apply Hm; lia.
           ++ apply Ha; discriminate.
           ++ destruct Hextends as [extra ->]. now apply RenameFrames.extend.
      * split; [change (meta_value stored 0=Z.of_nat index); now rewrite Hresult|]. split; [exact Hindexword|].
        split; [now rewrite <-Hrenamed|]. split; [exact Hextends|]. split; [apply RenameMemoAtom.parameters|].
        split; [exact Hgrowth|]. apply RenameMemoAccounting.completed_before with (middle:=internstate).
        -- apply RenameMemoAccounting.passive_trans with (t:=looked); [apply RenameMemoAccounting.lookup|].
           apply RenameMemoAccounting.passive_trans with (t:=first); [apply RenameMemoAccounting.index|].
           apply RenameMemoAccounting.passive_trans with (t:=second); [apply RenameMemoAccounting.index|].
           exact (RenameMemoAccounting.intern second internstate Hframe).
        -- unfold RenameMemoAccounting.completed. auto.
Qed.
End Atom.
Module Join.
Import RenameMemoJoinRefinement.
Theorem generated_join (f : Frame) phase fs rho p q depth stack left_value right_value current count target_bound observations :
  (phase=2 \/ phase=3) ->
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena (machine f) fs -> Z.of_nat (length fs)<=9223372036854775807 ->
  RenameFrames.represents (machine f) fs (task phase p q depth left_value::stack) ->
  meta_value (machine f) 0=current -> word current -> nth_error fs (Z.to_nat current)=Some right_value ->
  (phase=2 -> left_value=RenameStack.renamed rho depth p /\ right_value=RenameStack.renamed rho depth q) ->
  (phase=3 -> right_value=RenameStack.renamed rho (S depth) p) ->
  (Z.of_nat count/2<=meta_value (machine f) 30 -> Z.of_nat count<=9223372036854775807) ->
  SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) target_bound ->
  exists final next index size internstate,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) target_bound /\
    (size=count \/ size=(2*count)%nat) /\
    RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning next rho) /\
    NativeRepresentation.canonical_arena (machine final) next /\ RenameFrames.represents (machine final) next stack /\
    meta_value (machine final) 0=Z.of_nat index /\ word (Z.of_nat index) /\
    nth_error next index=Some (RenameStack.renamed rho depth (parent phase p q)) /\
    (exists extra, next=fs++extra) /\
    InternExecution.logical_frame (machine f) internstate /\
    RenameMemoInvariant.storage_frame internstate (machine final) /\ RenameMemoHit.parameters f final /\
    (length next<=S (length fs))%nat /\
    (forall root, word root -> nth_error fs (Z.to_nat root)=Some (parent phase p q) ->
      RenameMemoAccounting.completed (machine f) count (machine final) size (root,Z.of_nat depth)).
Proof.
  intros Hphase Hvalid Harena Hcapacity Hstack Hcurrent Hcurrentword Hlookup Himp Hall Hfits HrawArena.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hvalid) as Hmeta.
  pose proof (RenameMemoInvariant.error_clear _ _ _ Hvalid) as Herror.
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hframes]]].
  destruct (fields fs raw phase p q depth left_value Hphase Hentry)
    as [root [left_id [-> [Hroot [Hdepth [Hparent Hleft]]]]]].
  assert (Hparentbound : (Z.to_nat root<length fs)%nat) by (apply nth_error_Some; congruence).
  assert (Hnativebound : (Z.to_nat root<length (memory (machine f) arraydef_0__formulas))%nat).
  { pose proof (proj1 (proj1 Harena)) as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  destruct (List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)) as [[tag a] b] eqn:Hformula.
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0)=
    (root,Z.of_nat depth,phase,left_id)) by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  destruct (arguments_spec phase fs left_id current left_value right_value Hphase Hleft Hcurrentword Hlookup) as [Hnormal Hdecode].
  destruct (RenameMemoIntern.generated (machine f) (fun _=>false) (RenameMemoJoin.arguments phase left_id current)
    fs (joined phase left_value right_value) count rho observations Hvalid Harena Hcapacity Hnormal Hdecode)
    as [internstate [next [index [Hintern [Hframe [Hnext [Hcache [Hindex [Hindexword [Hmeaning Hextends]]]]]]]]]].
  assert (HrawTuple:RenameMemoInput.raw_bound target_bound
    ((RenameMemoJoin.arguments phase left_id current) vardef_0__intern_tag,
     (RenameMemoJoin.arguments phase left_id current) vardef_0__intern_a,
     (RenameMemoJoin.arguments phase left_id current) vardef_0__intern_b)).
  { destruct Hphase as [Hphase|Hphase];subst phase.
    - change (RenameMemoInput.raw_bound target_bound (3,left_id,current)). unfold RenameMemoInput.raw_bound. intros Hbad;lia.
    - change (RenameMemoInput.raw_bound target_bound (4,current,0)). unfold RenameMemoInput.raw_bound. intros Hbad;lia. }
  pose proof (SchemaEvaluationIndexBounds.observed_intern (machine f) internstate (fun _=>false)
    (RenameMemoJoin.arguments phase left_id current) fs next target_bound observations observations
    Harena Herror Hcapacity HrawArena HrawTuple Hintern Hnext) as HinternIndices.
  assert (Hplain : exec (funcdef_0__intern (fun _=>false) (RenameMemoJoin.arguments phase left_id current)) (machine f)=Some (tt,internstate)).
  { pose proof (execObserved_erases (funcdef_0__intern (fun _=>false) (RenameMemoJoin.arguments phase left_id current)) (machine f,observations)) as Herases. rewrite Hintern in Herases. exact (eq_sym Herases). }
  pose proof (InternGrowth.at_most_one (machine f) internstate _ _ fs next Harena Herror Hcapacity Hplain Hnext) as Hgrowth.
  pose proof (joined_renamed phase rho p q depth left_value right_value Hphase Himp Hall) as Hrenamed.
  assert (Hentrymeaning : RenameMemoMeaning.entry_meaning next rho (root,Z.of_nat depth) (meta_value internstate 0)).
  { rewrite Hindex. split; [exact Hroot|]. split; [exact Hdepth|]. split; [exact Hindexword|].
    exists (parent phase p q). split.
    - destruct Hextends as [extra ->]. now apply FormulaEncoding.nth_error_extend.
    - cbn [snd]. rewrite !Nat2Z.id. now rewrite <-Hrenamed.
  }
  assert (Hpostfits : Z.of_nat count/2<=meta_value internstate 30 -> Z.of_nat count<=9223372036854775807).
  { pose proof Hframe as [_ [Hm _]]. rewrite Hm by lia. exact Hfits. }
  destruct (RenameMemoAccounting.complete internstate root (Z.of_nat depth) (length stack) count
    (RenameMemoMeaning.entry_meaning next rho) observations Hcache Hpostfits Hentrymeaning)
    as (stored & size & Hput & Hchoice & Hstored & Hresult & Hpop & Hputframe & Hstorage & Hupper & Hnew & Hcovered).
  pose proof Hstack as [Hcount [Hcountword Hentries]]. cbn [length] in Hcount,Hcountword.
  pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hcache) as Hpostmeta.
  pose proof (RenameMemoInvariant.error_clear _ _ _ Hcache) as Hposterror.
  assert (HstoredIndices:SchemaEvaluationIndexBounds.raw_arena stored (length next) target_bound).
  { eapply SchemaEvaluationIndexBounds.raw_array_frame;[|exact HinternIndices].
    exact (proj1 Hstorage arraydef_0__formulas ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). }
  exists (RenameMemoJoin.result f stored (length stack) root (Z.of_nat depth) phase left_id tag a b),next,index,size,internstate.
  split.
  - eapply RenameMemoJoin.generated_join_composition with (right_id:=current); eassumption.
  - split;[exact HstoredIndices|]. split; [exact Hchoice|]. split; [exact Hstored|]. split.
    + now apply RenameMemoStorage.canonical_arena with (s:=internstate).
    + split.
      * apply RenameMemoStorage.popped_frames with (s:=internstate) (task:=task phase p q depth left_value); try assumption; [lia|].
        destruct Hframe as [Ha [Hm _]]. apply RenameFrames.transport with (s:=machine f).
        -- apply Hm; lia.
        -- apply Ha; discriminate.
        -- destruct Hextends as [extra ->]. now apply RenameFrames.extend.
      * split; [change (meta_value stored 0=Z.of_nat index); now rewrite Hresult|]. split; [exact Hindexword|]. split; [now rewrite <-Hrenamed|].
        split; [exact Hextends|]. split; [exact Hframe|]. split; [exact Hstorage|]. split; [apply RenameMemoJoin.parameters|].
        split; [exact Hgrowth|]. apply RenameMemoAccounting.completed_source with (root:=root).
        -- exact (proj1 (proj2 (proj2 Harena))).
        -- exact Hroot.
        -- exact Hparent.
        -- apply RenameMemoAccounting.completed_before with (middle:=internstate).
           ++ now apply RenameMemoAccounting.intern.
           ++ unfold RenameMemoAccounting.completed. auto.
Qed.
End Join.
Module Step.
Definition post (f : Frame) fs count rho stack old_value target final next next_stack value size :=
  RenameMemoState.represents (machine final) next rho size next_stack value target /\
  (exists extra, next=fs++extra) /\ (length next<=S (length fs))%nat /\
  RenameMemoHit.parameters f final /\ (RenameStack.pending next_stack<RenameStack.pending stack)%nat /\
  RenameMemoTransition.step rho stack old_value next_stack value /\
  RenameMemoNativeEvent.event (machine f) fs count (machine final) next size stack next_stack.
Local Ltac arena_indices := first [assumption |
 lazymatch goal with |- SchemaEvaluationIndexBounds.raw_arena ?after ?count ?bound =>
  match goal with
  | Hbefore:NativeRepresentation.canonical_arena ?before ?fs,
    Hafter:NativeRepresentation.canonical_arena after ?fs,
    Hraw:SchemaEvaluationIndexBounds.raw_arena ?before (length ?fs) bound |- _ =>
      exact (same_semantics_raw before after fs bound Hbefore Hafter Hraw)
  end
 end].
Local Ltac pack final next stack value size Hrun Hstate Hextends Hgrowth Hparameters Hdecrease Hnative :=
  exists final,next,stack,value,size; split; [exact Hrun|];
  split; [arena_indices|];
  unfold post; split; [exact Hstate|]; split; [exact Hextends|]; split; [first [exact Hgrowth|Hgrowth]|];
  split; [exact Hparameters|]; split; [first [exact Hdecrease|Hdecrease]|]; split;
  [first [apply RenameMemoTransition.cached | apply RenameMemoTransition.expanded |
    match goal with Hleft : ?left = _, Hright : ?right = _ |- _ =>
      rewrite Hleft,Hright; apply RenameMemoTransition.expanded end |
    match goal with Hbody : ?body = _ |- _ => rewrite Hbody; apply RenameMemoTransition.expanded end]|first [exact Hnative|Hnative]].
Lemma same_arena fs : exists extra : list SetTheory.formula, fs=fs++extra.
Proof. exists []; now rewrite app_nil_r. Qed.
Theorem generated (f : Frame) fs m shift arg count task stack value target source_bound target_bound :
  nums f vardef_0__rename_mode=mode_number m -> nums f vardef_0__rename_shift=Z.of_nat shift ->
  nums f vardef_0__rename_arg=Z.of_nat arg ->
  RenameMemoState.represents (machine f) fs (renaming m shift arg) count (task::stack) value target ->
  RenameMemoState.resources (machine f) fs m shift arg count (task::stack) ->
  SchemaEvaluationIndexBounds.raw_arena (machine f) (length fs) target_bound ->
  RenameMemoIndexBounds.stack_bound source_bound (task::stack) ->
  (source_bound+RenameMemoIndexBounds.increment m shift arg<=target_bound)%nat ->
  forall observations, exists final next next_stack next_value size,
    execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    SchemaEvaluationIndexBounds.raw_arena (machine final) (length next) target_bound /\
    post f fs count (renaming m shift arg) (task::stack) value target final next next_stack next_value size.
Proof.
  intros Hmode Hshift Harg Hstate Hresources HrawArena HstackIndices HtargetBound observations.
  pose proof (List.Forall_inv HstackIndices) as HtaskBound.
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
        destruct (Atom.generated_atom_miss f 1 fs i j depth stack m shift arg count root left_id target_bound observations
          ltac:(now left) Hmode Hshift Harg Hvalid Harena Hcapacity Hframes Hview Hlookup Hi Hj Hshiftword Hargword Hmi Hmj Hfits HrawArena
          ltac:(cbn [RenameMemoIndexBounds.source RenameMemoIndexBounds.formula_bound] in HtaskBound;
            pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg i);lia)
          ltac:(cbn [RenameMemoIndexBounds.source RenameMemoIndexBounds.formula_bound] in HtaskBound;
            pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg j);lia))
          as (final & next & index & size & Hrun & HnextIndices & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hparameters & Hgrowth & Hcomplete).
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
        destruct (Atom.generated_atom_miss f 2 fs i j depth stack m shift arg count root left_id target_bound observations
          ltac:(now right) Hmode Hshift Harg Hvalid Harena Hcapacity Hframes Hview Hlookup Hi Hj Hshiftword Hargword Hmi Hmj Hfits HrawArena
          ltac:(cbn [RenameMemoIndexBounds.source RenameMemoIndexBounds.formula_bound] in HtaskBound;
            pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg i);lia)
          ltac:(cbn [RenameMemoIndexBounds.source RenameMemoIndexBounds.formula_bound] in HtaskBound;
            pose proof (RenameMemoIndexBounds.binder_bound depth m shift arg j);lia))
          as (final & next & index & size & Hrun & HnextIndices & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hparameters & Hgrowth & Hcomplete).
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
    destruct (Join.generated_join f 2 fs (renaming m shift arg) p q depth stack left_value value (meta_value (machine f) 0) count target_bound observations
      ltac:(now left) Hvalid Harena Hcapacity Hframes eq_refl Hcurrentword Hcurrent ltac:(intro; now split) ltac:(discriminate) Hfits HrawArena)
      as (final & next & index & size & internstate & Hrun & HnextIndices & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hinternframe & Hstorage & Hparameters & Hgrowth & Hcomplete).
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
    destruct (Join.generated_join f 3 fs (renaming m shift arg) p SetTheory.falsity depth stack SetTheory.falsity value (meta_value (machine f) 0) count target_bound observations
      ltac:(now right) Hvalid Harena Hcapacity Hframes eq_refl Hcurrentword Hcurrent ltac:(discriminate) ltac:(intro; exact Hbody) Hfits HrawArena)
      as (final & next & index & size & internstate & Hrun & HnextIndices & Hchoice & Hvalid' & Harena' & Hframes' & Hresult & Hword & Hdenotes & Hextends & Hinternframe & Hstorage & Hparameters & Hgrowth & Hcomplete).
    assert (Hnewstate : RenameMemoState.represents (machine final) next (renaming m shift arg) size stack
      (RenameStack.renamed (renaming m shift arg) depth (SetTheory.all p)) target).
    { apply RenameMemoState.completed with (fs:=fs); try assumption.
      - now rewrite Hresult.
      - now rewrite Hresult,Nat2Z.id. }
    pack final next stack (RenameStack.renamed (renaming m shift arg) depth (SetTheory.all p)) size Hrun Hnewstate Hextends Hgrowth Hparameters
      ltac:(cbn [RenameStack.pending RenameStack.frame_work]; lia)
      ltac:(apply RenameMemoNativeEvent.closed; [exact Hcomplete|exact Hgrowth]).
Qed.
End Step.
End RenameMemoIndexStep.
