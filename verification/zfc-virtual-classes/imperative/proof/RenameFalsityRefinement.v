From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From Trusted Require Import SetTheory.
From NativeProof Require Import Index SipHash ObservedLocal RenameStructure RenameStack RenameFrames RenameLeaf RenameConfiguration Representation.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module RenameFalsityRefinement.
Import IndexExecution SipHashExecution ObservedLocal RenameStructure.
Theorem generated_falsity_refines (f : Frame) fs depth stack observations :
  (10 < length (memory (machine f) arraydef_0__meta))%nat -> meta_value (machine f) 8 = 0 ->
  NativeRepresentation.canonical_arena (machine f) fs ->
  RenameFrames.represents (machine f) fs (RenameStack.visit SetTheory.falsity depth :: stack) ->
  exists final, execLocalObserved iteration (f,observations) = Some (KeepGoing,(final,observations)) /\
    NativeRepresentation.canonical_arena (machine final) fs /\ RenameFrames.represents (machine final) fs stack /\
    meta_value (machine final) 0 = 0 /\ meta_value (machine final) 8 = 0 /\ RenameConfiguration.preserved f final.
Proof.
  intros Hmeta Herror Harena Hstack.
  destruct (RenameLeaf.generated_falsity_refines f fs depth stack observations Hmeta Herror Harena Hstack)
    as [final [Hrun [Hnext [Hframes Hvalue]]]].
  destruct (RenameFrames.top_entry (machine f) fs _ stack Hstack) as [raw [Hraw [Hentry Hbound]]].
  destruct raw as [[[root raw_depth] phase] left_id]. cbn [RenameFrames.entry] in Hentry.
  destruct Hentry as [Hroot [Hdepth [Hdepth_eq [Hphase Hlookup]]]]; subst raw_depth phase.
  destruct (RenameLeaf.falsity_record (machine f) fs (Z.to_nat root) Harena Hlookup) as [Hnodebound Hnode].
  assert (Hnth : List.nth (length stack) (memory (machine f) arraydef_0__frames) (0,0,0,0) = (root,Z.of_nat depth,0,left_id))
    by exact (List.nth_error_nth _ _ (0,0,0,0) Hraw).
  pose proof Hstack as [Hcount [Hword Hentries]]. cbn [length] in Hcount,Hword.
  pose proof (RenameLeaf.generated_falsity f (length stack) root (Z.of_nat depth) left_id observations
    Hmeta Hcount Herror Hword Hbound Hnth Hnodebound Hnode) as Hactual.
  rewrite Hactual in Hrun. injection Hrun as <-.
  eexists. split; [exact Hactual|]. split; [exact Hnext|]. split; [exact Hframes|]. split; [exact Hvalue|]. split.
  - change (meta_value (store_meta (store_meta (machine f) 0 0) 10 (Z.of_nat (length stack))) 8 = 0).
    rewrite !meta_store_other by lia. exact Herror.
  - apply RenameConfiguration.falsity.
Qed.
End RenameFalsityRefinement.
