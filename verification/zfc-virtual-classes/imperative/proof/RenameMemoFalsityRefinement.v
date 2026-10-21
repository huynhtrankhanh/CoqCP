From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash RenameStack RenameFrames Representation RenameMemoTable RenameMemoLookup
  RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant RenameMemoStorage RenameMemoMeaning RenameMemoVisit
  RenameMemoHitRefinement RenameMemoFalsity ObservedLocal Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoFalsityRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl.
Theorem generated_falsity s bs ns fs rho depth stack count observations :
  RenameMemoInvariant.valid s count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena s fs -> nth_error fs 0=Some SetTheory.falsity ->
  RenameFrames.represents s fs (RenameStack.visit SetTheory.falsity depth::stack) ->
  (Z.of_nat count/2<=meta_value s 30 -> Z.of_nat count<=9223372036854775807) ->
  exists final size, execLocalObserved iteration ({|machine:=s;bools:=bs;nums:=ns|},observations)=Some (KeepGoing,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\ RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning fs rho) /\
    NativeRepresentation.canonical_arena (machine final) fs /\ RenameFrames.represents (machine final) fs stack /\
    meta_value (machine final) 0=0 /\ RenameMemoInvariant.storage_frame s (machine final) /\
    RenameMemoHit.parameters {|machine:=s;bools:=bs;nums:=ns|} final.
Proof.
  intros Hvalid Harena Hzero Hframes Hfits.
  destruct (RenameMemoVisit.top_visit s fs SetTheory.falsity depth stack Harena Hframes) as [root [left_id Hview]].
  pose proof Hview as [Hcount Hword Hroot Hdepth Hframecap Hframe Hsource Hnodecap].
  destruct (RenameMemoLookup.lookup s (root,Z.of_nat depth) count) as [value|] eqn:Hlookup.
  - assert (Hmeaning : RenameMemoMeaning.entry_meaning fs rho (root,Z.of_nat depth) value).
    { exact (RenameMemoTable.scan_meaning (RenameMemoLookup.table s) count (RenameMemoMeaning.entry_meaning fs rho)
        (root,Z.of_nat depth) (RenameMemoLookup.hash_start s (root,Z.of_nat depth) count) count value
        ltac:(pose proof (RenameMemoInvariant.capacity_minimum _ _ _ Hvalid); lia)
        (RenameMemoLookup.hash_start_bound s (root,Z.of_nat depth) count ltac:(pose proof (RenameMemoInvariant.capacity_minimum _ _ _ Hvalid); lia))
        (RenameMemoInvariant.entries_mean _ _ _ Hvalid) Hlookup). }
    assert (Hvalue : value=0).
    { apply RenameMemoMeaning.falsity_value with (fs:=fs) (rho:=rho) (root:=root) (depth:=Z.of_nat depth); try assumption.
      exact (proj1 (proj2 (proj2 Harena))). }
    destruct (RenameMemoHitRefinement.generated_cached_visit {|machine:=s;bools:=bs;nums:=ns|} fs rho SetTheory.falsity depth stack count root left_id value observations
      Hvalid Harena Hframes Hview Hlookup) as [final [Hrun [Hvalid' [Harena' [Hframes' [Hresult [Hdenotes [Hstorage Hparameters]]]]]]]].
    exists final,count. split; [exact Hrun|]. split; [now left|]. split; [exact Hvalid'|]. split; [exact Harena'|].
    split; [exact Hframes'|]. split; [now rewrite Hresult,Hvalue|]. split; assumption.
  - pose proof (RenameMemoVisit.falsity_record s fs root Harena Hsource) as Hraw.
    pose proof (RenameMemoMeaning.falsity fs rho root (Z.of_nat depth) Hroot Hdepth Hsource Hzero) as Hmeaning.
    destruct (RenameMemoFalsity.generated_falsity s bs ns (length stack) root (Z.of_nat depth) left_id count observations
      (RenameMemoMeaning.entry_meaning fs rho) Hvalid Hcount Hword Hframecap Hframe Hnodecap Hraw Hlookup Hfits Hmeaning)
      as [final [size [Hrun [Hchoice [Hvalid' [Hresult [Hcount' [Hstorage Hparameters]]]]]]]].
    exists final,size. split; [exact Hrun|]. split; [exact Hchoice|]. split; [exact Hvalid'|]. split.
    + now apply RenameMemoStorage.canonical_arena with (s:=s).
    + split.
      * apply RenameMemoStorage.popped_frames with (s:=s) (task:=RenameStack.visit SetTheory.falsity depth); try assumption.
        pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hvalid). lia.
      * split; [exact Hresult|]. split; assumption.
Qed.
End RenameMemoFalsityRefinement.
