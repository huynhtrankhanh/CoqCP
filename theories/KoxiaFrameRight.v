From CoqCP Require Import Options Imperative Execution KoxiaIntegers KoxiaArrays KoxiaTables KoxiaTableLoops
  KoxiaFrames SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve.
Ltac normalize_frame_updates := repeat first [rewrite lookupSame | rewrite lookupDifferent by congruence].
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition rightFrameNums (nums : varsfuncdef_0__solve -> Z) start span depth :=
  update (update nums vardef_0__solve_middle (Z.of_nat ((start+start+span)/2)))
    vardef_0__solve_depth (Z.of_nat (S depth)).
Definition rightFrameAction start span depth base saved :=
  tableWrite arraydef_0__frames (Z.of_nat depth)
    (Z.of_nat start,Z.of_nat (start+span),2,base,saved) >>= fun _ =>
  tableWrite arraydef_0__frames (Z.of_nat (S depth))
    (Z.of_nat ((start+start+span)/2),Z.of_nat (start+span),0,0,0).
Lemma phaseRightNormalized b nums start span depth continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=1 -> nums vardef_0__solve_depth=Z.of_nat depth ->
  Z.of_nat (start+start+span)<18446744073709551616 -> Z.of_nat (S depth)<18446744073709551616 ->
  eliminateLocalVariables b nums (solvePhaseBody >>= continuation)=
  rightFrameAction start span depth (nums vardef_0__solve_base) (nums vardef_0__solve_saved) >>= fun _ =>
  eliminateLocalVariables b (rightFrameNums nums start span depth) (continuation KeepGoing).
Proof.
  intros leftEq rightEq phaseEq depthEq addressFit depthFit.
  unfold solvePhaseBody,numberLocalGet,numberLocalSet,addInt,subInt,divIntUnsigned,store.
  normalize_table_loop. try rewrite leftEq; try try rewrite rightEq.
  rewrite (coerce64_small (Z.of_nat start+Z.of_nat (start+span))) by lia.
  try rewrite decide_False by lia.
  replace ((Z.of_nat start+Z.of_nat (start+span))/2) with (Z.of_nat ((start+start+span)/2))
    by (rewrite Nat2Z.inj_div; f_equal; lia).
  rewrite lookupDifferent by congruence. rewrite phaseEq.
  rewrite bool_decide_false by lia. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite phaseEq.
  rewrite bool_decide_true by reflexivity. normalize_table_loop.
  normalize_frame_updates. rewrite leftEq,rightEq,depthEq.
  unfold rightFrameAction,tableWrite. cbn [bind].
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  try rewrite !lookupSame. normalize_frame_updates. try rewrite depthEq.
  rewrite (coerce64_small (Z.of_nat depth+1)) by lia.
  replace (Z.of_nat depth+1) with (Z.of_nat (S depth)) by lia.
  try rewrite !lookupSame. normalize_frame_updates. try rewrite leftEq; try try rewrite rightEq.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop. reflexivity.
Qed.
Theorem generated_right_frame_execution b nums start span depth state frames continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=1 -> nums vardef_0__solve_depth=Z.of_nat depth ->
  Z.of_nat (start+start+span)<18446744073709551616 -> Z.of_nat (S depth)<18446744073709551616 ->
  (S depth<length frames)%nat ->
  exec (eliminateLocalVariables b nums (solvePhaseBody >>= continuation)) (withArray state arraydef_0__frames frames)=
  exec (eliminateLocalVariables b (rightFrameNums nums start span depth) (continuation KeepGoing))
    (withArray state arraydef_0__frames
      (<[S depth:=(Z.of_nat ((start+start+span)/2),Z.of_nat (start+span),0,0,0)]>
        (<[depth:=(Z.of_nat start,Z.of_nat (start+span),2,nums vardef_0__solve_base,nums vardef_0__solve_saved)]>frames))).
Proof.
  intros leftEq rightEq phaseEq depthEq addressFit depthFit frameRoom.
  rewrite phaseRightNormalized with (start:=start) (span:=span) (depth:=depth) by assumption.
  unfold rightFrameAction,tableWrite. cbn [bind]. rewrite execStoreArray by lia.
  rewrite execStoreArray by (rewrite length_insert; exact frameRoom). reflexivity.
Qed.
Lemma rightFrameNums_depth nums start span depth : rightFrameNums nums start span depth vardef_0__solve_depth=Z.of_nat (S depth).
Proof. unfold rightFrameNums. apply lookupSame. Qed.
Lemma rightFrameNums_other nums start span depth name : name<>vardef_0__solve_depth -> name<>vardef_0__solve_middle ->
  rightFrameNums nums start span depth name=nums name.
Proof. intros. unfold rightFrameNums. normalize_frame_updates. reflexivity. Qed.
