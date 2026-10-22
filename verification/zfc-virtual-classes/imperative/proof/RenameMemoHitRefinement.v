From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash RenameStack RenameFrames Representation RenameMemoTable RenameMemoLookup
  RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant RenameMemoStorage RenameMemoMeaning RenameMemoVisit
  RenameMemoAccounting ObservedLocal Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoHitRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Local Opaque funcdef_0__renameCacheGet Imperative.update.
Theorem generated_cached_visit (f : Frame) fs rho source depth stack count root left_id value observations :
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.visit source depth::stack) ->
  RenameMemoVisit.view (machine f) fs source depth stack root left_id ->
  RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count=Some value ->
  exists final, execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    RenameMemoInvariant.valid (machine final) count (RenameMemoMeaning.entry_meaning fs rho) /\
    NativeRepresentation.canonical_arena (machine final) fs /\ RenameFrames.represents (machine final) fs stack /\
    meta_value (machine final) 0=value /\ nth_error fs (Z.to_nat (meta_value (machine final) 0))=Some (RenameStack.renamed rho depth source) /\
    RenameMemoInvariant.storage_frame (machine f) (machine final) /\ RenameMemoHit.parameters f final /\
    RenameMemoAccounting.passive (machine f) (machine final).
Proof.
  intros Hvalid Harena Hframes Hview Hcached.
  destruct Hview as [Hcount Hword Hroot Hdepth Hframecap Hframe Hsource Hnodecap].
  pose proof Hvalid as [Hmeta Hsip Hpositive Herror Hcapacity Hmin HcapWord Hmemo Hlive Hload Hentries Hindexed].
  assert (Hmeaning : RenameMemoMeaning.entry_meaning fs rho (root,Z.of_nat depth) value).
  { exact (RenameMemoTable.scan_meaning (RenameMemoLookup.table (machine f)) count (RenameMemoMeaning.entry_meaning fs rho)
      (root,Z.of_nat depth) (RenameMemoLookup.hash_start (machine f) (root,Z.of_nat depth) count) count value
      ltac:(lia) (RenameMemoLookup.hash_start_bound (machine f) (root,Z.of_nat depth) count ltac:(lia)) Hentries Hcached). }
  assert (Hsentinel : value<>maximum).
  { pose proof (RenameMemoMeaning.below_sentinel (machine f) fs rho (root,Z.of_nat depth) value Harena Hmeaning). lia. }
  set (looked:=RenameMemoLookup.result_state (machine f) (root,Z.of_nat depth) count).
  assert (Hlookvalid : RenameMemoInvariant.valid looked count (RenameMemoMeaning.entry_meaning fs rho)) by
    (now apply RenameMemoInvariant.lookup_valid).
  assert (Hget : execObserved (funcdef_0__renameCacheGet (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)))
    (machine f,observations)=Some (tt,(looked,observations))).
  { pose proof (RenameMemoLookup.generated_lookup_exact (machine f) (fun _=>false) (RenameMemoHit.arguments root (Z.of_nat depth)) count observations
      Hmeta Hsip Hpositive Hcapacity ltac:(lia) HcapWord Hmemo) as Hrun.
    cbv beta iota zeta delta [RenameMemoHit.arguments] in Hrun.
    rewrite updated_same,updated_other,updated_same in Hrun by discriminate. exact Hrun. }
  assert (Hpeek : meta_value looked 31=value).
  { unfold looked. rewrite RenameMemoLookup.result_value,Hcached by exact Hmeta. reflexivity. }
  destruct (List.nth (Z.to_nat root) (memory (machine f) arraydef_0__formulas) (0,0,0)) as [[tag a] b] eqn:Hraw.
  set (final:=RenameMemoHit.hit_frame f looked (length stack) root (Z.of_nat depth) left_id tag a b).
  assert (Hstorage : RenameMemoInvariant.storage_frame (machine f) (machine final)).
  { apply RenameMemoInvariant.storage_trans with (t:=looked); [apply RenameMemoInvariant.lookup_storage|].
    exact (RenameMemoInvariant.completed_storage looked (length stack) (meta_value looked 31)). }
  assert (HcountFinal : meta_value (machine final) 10=Z.of_nat (length stack)).
  { change (meta_value (RenameMemoHit.hit_state looked (length stack)) 10=Z.of_nat (length stack)).
    unfold RenameMemoHit.hit_state. apply meta_store_same. rewrite store_meta_length.
    pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid). lia. }
  assert (HvalueFinal : meta_value (machine final) 0=value).
  { change (meta_value (RenameMemoHit.hit_state looked (length stack)) 0=value).
    unfold RenameMemoHit.hit_state. rewrite meta_store_other by lia. rewrite meta_store_same; [exact Hpeek|].
    pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid). lia. }
  exists final. split.
  - apply RenameMemoHit.generated_hit_composition; try assumption.
    + exact (RenameMemoInvariant.metadata_ready _ _ _ Hlookvalid).
    + now rewrite Hpeek.
  - split.
    + exact (RenameMemoInvariant.completed_valid looked (length stack) (meta_value looked 31) count
        (RenameMemoMeaning.entry_meaning fs rho) Hlookvalid).
    + split; [exact (RenameMemoStorage.canonical_arena (machine f) (machine final) fs Hstorage Harena)|].
      split.
      * apply RenameMemoStorage.popped_frames with (s:=machine f) (task:=RenameStack.visit source depth); try assumption. lia.
      * split; [exact HvalueFinal|]. split.
        -- rewrite HvalueFinal. exact (RenameMemoMeaning.result fs rho root depth value source Hmeaning Hsource).
        -- split; [exact Hstorage|]. split; [apply RenameMemoHit.hit_parameters|].
           apply RenameMemoAccounting.passive_trans with (t:=looked); [apply RenameMemoAccounting.lookup|].
           change (RenameMemoAccounting.passive looked (RenameMemoHit.hit_state looked (length stack))).
           unfold RenameMemoAccounting.passive,RenameMemoHit.hit_state. split.
           ++ unfold RenameMemoLookup.table. now rewrite !store_meta_other by discriminate.
           ++ split; rewrite !meta_store_other by lia; reflexivity.
Qed.
End RenameMemoHitRefinement.
