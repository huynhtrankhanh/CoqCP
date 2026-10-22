From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash RenameStack RenameFrames Representation RenameMemoTable RenameMemoLookup
  RenameMemoInit RenameMemoControl RenameMemoHit RenameMemoInvariant RenameMemoStorage RenameMemoMeaning RenameMemoVisit
  RenameMemoFalsity RenameMemoPut RenameMemoAccounting RenameMemoContents RenameMemoOccupancy ObservedLocal Observation.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.
Module RenameMemoFalsityAccounting.
Import IndexExecution SipHashExecution ObservedLocal RenameMemoInit RenameMemoControl RenameMemoFalsity.
Local Opaque hash_state siphash24 funcdef_0__renameCacheGet funcdef_0__renameCachePut Imperative.update.
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
    RenameMemoInvariant.storage_frame s (machine final) /\ RenameMemoHit.parameters {|machine:=s;bools:=bs;nums:=ns|} final /\
    RenameMemoAccounting.completed s count (machine final) size (root,depth).
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
    destruct (RenameMemoLookup.result_frame s (root,depth) count) as [_ [Hm _]]. exact (Hm 30%nat ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (Hpopfits : Z.of_nat count/2<=meta_value popped 30 -> Z.of_nat count<=9223372036854775807).
  { now rewrite Hcounter. }
  assert (Hresult : meaning (arguments root depth 0 vardef_0__renameCachePut_node,arguments root depth 0 vardef_0__renameCachePut_depth)
    (arguments root depth 0 vardef_0__renameCachePut_value)).
  { destruct (arguments_values root depth 0) as [Hnode [Hdepth Hvalue]]. now rewrite Hnode,Hdepth,Hvalue. }
  destruct (RenameMemoInvariant.generated_put popped (fun _=>false) (arguments root depth 0) count observations meaning
    Hpopvalid Hpopfits Hresult) as [stored [size [Hput [Hchoice [Hstored Hputframe]]]]].
  destruct (RenameMemoContents.executed popped stored (fun _=>false) (arguments root depth 0) count observations meaning
    Hpopvalid Hpopfits Hput) as [actual [Hactual [Hnew Hcovered]]].
  assert (Hsame : actual=size) by (pose proof (RenameMemoInvariant.capacity_value _ _ _ Hstored); lia). subst actual.
  pose proof (RenameMemoOccupancy.executed popped stored (fun _=>false) (arguments root depth 0) count observations meaning
    Hpopvalid Hpopfits Hput) as Hupper. rewrite Hcounter in Hupper.
  destruct (arguments_values root depth 0) as [Hnode [Hdepth Hvalue]]. rewrite Hnode,Hdepth in Hnew.
  assert (Hpoptable : RenameMemoLookup.table popped=RenameMemoLookup.table s).
  { unfold popped,RenameMemoInvariant.completed,RenameMemoLookup.table.
    rewrite !store_meta_other by discriminate. unfold looked.
    destruct (RenameMemoLookup.result_frame s (root,depth) count) as [Ha _]. now rewrite Ha by discriminate. }
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
        -- split; [exact (RenameMemoHit.hit_parameters {|machine:=s;bools:=bs;nums:=ns|} stored top root depth left_id 0 0 0)|].
           change (RenameMemoAccounting.completed s count stored size (root,depth)).
           unfold RenameMemoAccounting.completed. split.
           ++ unfold RenameMemoContents.covers in *. now rewrite Hpoptable in Hcovered.
           ++ split; assumption.
Qed.
Theorem generated_fresh_miss (f : Frame) fs rho depth stack count root left_id observations :
  RenameMemoInvariant.valid (machine f) count (RenameMemoMeaning.entry_meaning fs rho) ->
  NativeRepresentation.canonical_arena (machine f) fs -> nth_error fs 0=Some SetTheory.falsity ->
  RenameFrames.represents (machine f) fs (RenameStack.visit SetTheory.falsity depth::stack) ->
  RenameMemoVisit.view (machine f) fs SetTheory.falsity depth stack root left_id ->
  RenameMemoLookup.lookup (machine f) (root,Z.of_nat depth) count=None ->
  (Z.of_nat count/2<=meta_value (machine f) 30 -> Z.of_nat count<=9223372036854775807) ->
  exists final size, execLocalObserved iteration (f,observations)=Some (KeepGoing,(final,observations)) /\
    (size=count \/ size=(2*count)%nat) /\
    RenameMemoInvariant.valid (machine final) size (RenameMemoMeaning.entry_meaning fs rho) /\
    NativeRepresentation.canonical_arena (machine final) fs /\ RenameFrames.represents (machine final) fs stack /\
    meta_value (machine final) 0=0 /\ RenameMemoInvariant.storage_frame (machine f) (machine final) /\
    RenameMemoHit.parameters f final /\
    RenameMemoAccounting.completed (machine f) count (machine final) size (root,Z.of_nat depth).
Proof.
  intros Hvalid Harena Hzero Hframes Hview Hnone Hfits.
  destruct Hview as [Hcount Hword Hroot Hdepth Hframecap Hframe Hsource Hnodecap].
  pose proof (RenameMemoVisit.falsity_record (machine f) fs root Harena Hsource) as Hraw.
  pose proof (RenameMemoMeaning.falsity fs rho root (Z.of_nat depth) Hroot Hdepth Hsource Hzero) as Hmeaning.
  destruct f as [s bs ns]. cbn [machine] in *.
  destruct (generated_falsity s bs ns (length stack) root (Z.of_nat depth) left_id count observations
    (RenameMemoMeaning.entry_meaning fs rho) Hvalid Hcount Hword Hframecap Hframe Hnodecap Hraw Hnone Hfits Hmeaning)
    as (final & size & Hrun & Hchoice & Hvalid' & Hresult & Hcount' & Hstorage & Hparameters & Hcompleted).
  exists final,size. split; [exact Hrun|]. split; [exact Hchoice|]. split; [exact Hvalid'|]. split.
  - now apply RenameMemoStorage.canonical_arena with (s:=s).
  - split.
    + apply RenameMemoStorage.popped_frames with (s:=s) (task:=RenameStack.visit SetTheory.falsity depth); try assumption.
      pose proof (RenameMemoInvariant.metadata_ready _ _ _ Hvalid). lia.
    + split; [exact Hresult|]. split; [exact Hstorage|]. split; assumption.
Qed.
End RenameMemoFalsityAccounting.
