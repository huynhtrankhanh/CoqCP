From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaArrays KoxiaTables KoxiaConvolution KoxiaConvolutionExecution KoxiaConvolutionReady KoxiaFrameLeft KoxiaLeftValues KoxiaFrameStores KoxiaArena.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve.
Definition leftSavedState state len cut span base :=
  if Nat.ltb cut len then readyConvolutionFinal state len cut span base else state.
Theorem leftBranchAction_execution nums start span len cut base depth state :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_length=Z.of_nat len -> nums vardef_0__solve_top=Z.of_nat base ->
  nums vardef_0__solve_depth=Z.of_nat depth ->
  nums vardef_0__solve_middle=Z.of_nat ((start+start+span)/2) ->
  (start+span<length (memory state arraydef_0__prefix))%nat ->
  nth (start+span) (memory state arraydef_0__prefix) 0-nth start (memory state arraydef_0__prefix) 0=Z.of_nat cut ->
  (cut<=span)%nat -> Z.of_nat (len+start+span)<18446744073709551616 ->
  Z.of_nat (S depth)<18446744073709551616 ->
  (S depth<length (memory state arraydef_0__frames))%nat ->
  ((cut<len)%nat -> ConvolutionReady state len cut span base) ->
  exec (leftBranchAction nums) state=
  Some (leftFinishedNums nums (Z.of_nat cut),
    storedChildFrames (leftSavedState state len cut span base) depth start span ((start+start+span)/2) base
      (savedLength len cut span)).
Proof.
  intros leftEq rightEq lenEq topEq depthEq middleEq prefixRoom prefixDiff cutBound addressFit depthFit frameRoom ready.
  assert (prefixStartRoom : (start<length (memory state arraydef_0__prefix))%nat) by lia.
  unfold leftBranchAction,tableRead. cbn [bind]. rewrite leftEq,rightEq.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state
    arraydef_0__prefix (start+span) 0) by exact prefixRoom.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state
    arraydef_0__prefix start 0) by exact prefixStartRoom.
  cbn [arrayType environment1] in *. rewrite prefixDiff.
  rewrite (coerce64_small (Z.of_nat cut)) by lia.
  rewrite lenEq.
  assert (highGuard : bool_decide (Z.of_nat cut<Z.of_nat len)=Nat.ltb cut len).
  { destruct (Nat.ltb cut len) eqn:present.
    - apply Nat.ltb_lt in present. rewrite bool_decide_true by lia. reflexivity.
    - apply Nat.ltb_ge in present. rewrite bool_decide_false by lia. reflexivity. }
  rewrite highGuard. unfold leftSavedState. destruct (Nat.ltb cut len) eqn:present.
  - apply Nat.ltb_lt in present.
    rewrite leftConvolveCall_nat with (start:=start) (span:=span) (len:=len) (base:=base) by (try assumption; lia).
    rewrite exec_bind.
    rewrite ready_convolution_execution with (len:=len) (cut:=cut) (span:=span) (base:=base)
      by (try apply ready; try normalize_frame_updates; try reflexivity; assumption).
    cbn [optionBind fst snd].
    try rewrite leftEq; try rewrite rightEq; try rewrite topEq; try rewrite depthEq; try rewrite middleEq.
    rewrite leftHigh_nat with (start:=start) (span:=span) (len:=len) by assumption.
    rewrite (coerce64_small (Z.of_nat depth+1)) by lia.
    replace (Z.of_nat depth+1) with (Z.of_nat (S depth)) by lia.
    rewrite storeChild_execution.
    2: unfold readyConvolutionFinal; rewrite convolutionFinal_preserves by congruence; exact frameRoom.
    reflexivity.
  - cbn [bind].
    try rewrite leftEq; try rewrite rightEq; try rewrite topEq; try rewrite depthEq; try rewrite middleEq.
    rewrite leftHigh_nat with (start:=start) (span:=span) (len:=len) by assumption.
    rewrite (coerce64_small (Z.of_nat depth+1)) by lia.
    replace (Z.of_nat depth+1) with (Z.of_nat (S depth)) by lia.
    rewrite storeChild_execution by exact frameRoom. reflexivity.
Qed.

Theorem generated_left_frame_execution b nums start span len cut base depth state continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=0 -> nums vardef_0__solve_length=Z.of_nat len ->
  nums vardef_0__solve_top=Z.of_nat base -> nums vardef_0__solve_depth=Z.of_nat depth ->
  (32<span)%nat ->
  (start+span<length (memory state arraydef_0__prefix))%nat ->
  nth (start+span) (memory state arraydef_0__prefix) 0-nth start (memory state arraydef_0__prefix) 0=Z.of_nat cut ->
  (cut<=span)%nat -> Z.of_nat (len+start+start+span)<18446744073709551616 ->
  Z.of_nat (base+savedLength len cut span)<18446744073709551616 ->
  Z.of_nat (S depth)<18446744073709551616 ->
  (S depth<length (memory state arraydef_0__frames))%nat ->
  ((cut<len)%nat -> ConvolutionReady state len cut span base) ->
  exists final,
    exec (eliminateLocalVariables b nums (KoxiaFrames.solvePhaseBody >>= continuation)) state=
    exec (eliminateLocalVariables b final (continuation KeepGoing))
      (storedChildFrames (leftSavedState state len cut span base) depth start span ((start+start+span)/2) base
        (savedLength len cut span)) /\
    final vardef_0__solve_length=Z.of_nat (Nat.min len cut) /\
    final vardef_0__solve_top=Z.of_nat (base+savedLength len cut span) /\
    final vardef_0__solve_depth=Z.of_nat (S depth) /\
    (forall name, name<>vardef_0__solve_special -> name<>vardef_0__solve_small -> name<>vardef_0__solve_hi ->
      name<>vardef_0__solve_top -> name<>vardef_0__solve_length -> name<>vardef_0__solve_depth ->
      name<>vardef_0__solve_middle -> final name=nums name).
Proof.
  intros leftEq rightEq phaseEq lenEq topEq depthEq large prefixRoom prefixDiff cutBound addressFit arenaFit depthFit frameRoom ready.
  rewrite phaseLeftNormalized with (start:=start) (span:=span) by (try assumption; lia).
  set (prepared := update nums vardef_0__solve_middle (Z.of_nat ((start+start+span)/2))).
  assert (preparedLeft : prepared vardef_0__solve_l=Z.of_nat start).
  { unfold prepared. rewrite lookupDifferent by congruence. exact leftEq. }
  assert (preparedRight : prepared vardef_0__solve_r=Z.of_nat (start+span)).
  { unfold prepared. rewrite lookupDifferent by congruence. exact rightEq. }
  assert (preparedLen : prepared vardef_0__solve_length=Z.of_nat len).
  { unfold prepared. rewrite lookupDifferent by congruence. exact lenEq. }
  assert (preparedTop : prepared vardef_0__solve_top=Z.of_nat base).
  { unfold prepared. rewrite lookupDifferent by congruence. exact topEq. }
  assert (preparedDepth : prepared vardef_0__solve_depth=Z.of_nat depth).
  { unfold prepared. rewrite lookupDifferent by congruence. exact depthEq. }
  assert (preparedMiddle : prepared vardef_0__solve_middle=Z.of_nat ((start+start+span)/2)) by (unfold prepared; apply lookupSame).
  rewrite exec_bind,leftBranchAction_execution with (start:=start) (span:=span) (len:=len) (cut:=cut) (base:=base) (depth:=depth)
    by (try assumption; lia).
  cbn [optionBind fst snd]. exists (leftFinishedNums prepared (Z.of_nat cut)). split; [reflexivity|].
  destruct (leftFinishedNums_fields prepared start span len cut base depth preparedLeft preparedRight preparedLen preparedTop
    preparedDepth ltac:(lia) arenaFit depthFit) as [finalLen [finalTop finalDepth]].
  split; [exact finalLen|]. split; [exact finalTop|]. split; [exact finalDepth|].
  intros name notSpecial notSmall notHigh notTop notLength notDepth notMiddle.
  rewrite leftFinishedNums_other by assumption. unfold prepared. rewrite lookupDifferent by congruence. reflexivity.
Qed.
