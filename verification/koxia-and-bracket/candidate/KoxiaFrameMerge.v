From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaArrays KoxiaTables KoxiaTableLoops KoxiaPolynomialBuffers KoxiaBufferSplit KoxiaFrames KoxiaFrameLeaves KoxiaMerge.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition mergeFinishBody :=
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve vardef_0__solve_size >>= fun size =>
    numberLocalSet _ _ _ vardef_0__solve_length size) >>= fun _ =>
  (numberLocalGet _ _ _ vardef_0__solve_base >>= fun base =>
    numberLocalSet _ _ _ vardef_0__solve_top base) >>= fun _ => popFrameBody.
Definition mergeFrameNums (nums : varsfuncdef_0__solve -> Z) start span len savedLen :=
  update (update nums vardef_0__solve_middle (Z.of_nat ((start+start+span)/2)))
    vardef_0__solve_size (Z.of_nat (Nat.max len savedLen)).
Lemma phaseMergeNormalized b nums start span len savedLen continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=2 -> nums vardef_0__solve_length=Z.of_nat len ->
  nums vardef_0__solve_saved=Z.of_nat savedLen ->
  Z.of_nat (start+start+span)<18446744073709551616 ->
  eliminateLocalVariables b nums (solvePhaseBody >>= continuation)=
  eliminateLocalVariables b (mergeFrameNums nums start span len savedLen)
    (loop (Nat.max len savedLen) (mergeCoefficientBody (Z.of_nat (Nat.max len savedLen))) >>=
      fun _ => mergeFinishBody >>= continuation).
Proof.
  intros leftEq rightEq phaseEq lenEq savedEq addressFit.
  unfold solvePhaseBody,numberLocalGet,numberLocalSet,addInt,subInt,divIntUnsigned.
  normalize_table_loop. rewrite leftEq,rightEq.
  rewrite (coerce64_small (Z.of_nat start+Z.of_nat (start+span))) by lia.
  replace ((Z.of_nat start+Z.of_nat (start+span))/2) with (Z.of_nat ((start+start+span)/2))
    by (rewrite Nat2Z.inj_div; f_equal; lia).
  rewrite lookupDifferent by congruence. rewrite phaseEq.
  rewrite bool_decide_false by lia. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite phaseEq.
  rewrite bool_decide_false by lia. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite lenEq.
  rewrite lookupSame. rewrite !lookupDifferent by congruence. rewrite savedEq.
  cbn [withLocalVariablesReturnValue withArraysReturnValue] in *.
  assert (sizeGuard : bool_decide (Z.of_nat len<Z.of_nat savedLen)=Nat.ltb len savedLen).
  { destruct (Nat.ltb len savedLen) eqn:small.
    - apply Nat.ltb_lt in small. rewrite bool_decide_true by lia. reflexivity.
    - apply Nat.ltb_ge in small. rewrite bool_decide_false by lia. reflexivity. }
  rewrite sizeGuard. unfold mergeFrameNums,mergeFinishBody,numberLocalGet,numberLocalSet,popFrameBody,subInt.
  destruct (Nat.ltb len savedLen) eqn:small.
  - apply Nat.ltb_lt in small. rewrite Nat.max_r by lia. normalize_table_loop.
    rewrite !lookupDifferent by congruence. rewrite savedEq,updateSame,lookupSame,Nat2Z.id.
    cbn [withLocalVariablesReturnValue withinLoopReturnValue] in *.
    rewrite !bind_unit_identity. normalize_table_loop.
    apply f_equal. apply f_equal. apply functional_extensionality. intros [].
    apply f_equal. apply functional_extensionality. intro size.
    apply f_equal. apply functional_extensionality. intros [].
    apply f_equal. apply functional_extensionality. intro base.
    apply f_equal. apply functional_extensionality. intros [].
    apply f_equal. apply functional_extensionality. intro depth.
    cbn [withLocalVariablesReturnValue withinLoopReturnValue] in *.
    destruct (bool_decide (depth=0)); normalize_table_loop; reflexivity.
  - apply Nat.ltb_ge in small. rewrite Nat.max_l by lia. normalize_table_loop.
    rewrite lookupSame,Nat2Z.id.
    cbn [withLocalVariablesReturnValue withinLoopReturnValue] in *.
    rewrite !bind_unit_identity. normalize_table_loop.
    apply f_equal. apply f_equal. apply functional_extensionality. intros [].
    apply f_equal. apply functional_extensionality. intro size.
    apply f_equal. apply functional_extensionality. intros [].
    apply f_equal. apply functional_extensionality. intro base.
    apply f_equal. apply functional_extensionality. intros [].
    apply f_equal. apply functional_extensionality. intro depth.
    cbn [withLocalVariablesReturnValue withinLoopReturnValue] in *.
    destruct (bool_decide (depth=0)); normalize_table_loop; reflexivity.
Qed.
Lemma mergeFinishNormalized b nums depth len base continuation :
  nums vardef_0__solve_depth=Z.of_nat depth -> nums vardef_0__solve_size=Z.of_nat len ->
  nums vardef_0__solve_base=Z.of_nat base -> Z.of_nat depth<18446744073709551616 ->
  eliminateLocalVariables b nums (mergeFinishBody >>= continuation)=
  eliminateLocalVariables b (popNums depth (update (update nums vardef_0__solve_length (Z.of_nat len))
    vardef_0__solve_top (Z.of_nat base))) (continuation (popOutcome depth)).
Proof.
  intros depthEq sizeEq baseEq depthFit.
  unfold mergeFinishBody,numberLocalGet,numberLocalSet. normalize_table_loop.
  rewrite sizeEq,lookupDifferent by congruence. rewrite baseEq.
  rewrite popFrameNormalized with (depth:=depth)
    by (try rewrite !lookupDifferent by congruence; assumption).
  unfold popNums,popOutcome. destruct (Nat.eqb depth 0); reflexivity.
Qed.
Theorem generated_merge_frame_execution b nums start span len base savedLen depth state values continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=2 -> nums vardef_0__solve_length=Z.of_nat len ->
  nums vardef_0__solve_base=Z.of_nat base -> nums vardef_0__solve_saved=Z.of_nat savedLen ->
  nums vardef_0__solve_depth=Z.of_nat depth ->
  Z.of_nat (start+start+span)<18446744073709551616 -> Z.of_nat depth<18446744073709551616 ->
  (Nat.max len savedLen<=length values)%nat ->
  (base+savedLen<=length (memory state arraydef_0__arena))%nat ->
  Z.of_nat (base+Nat.max len savedLen)<18446744073709551616 ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__arena) ->
  exists final,
    exec (eliminateLocalVariables b nums (solvePhaseBody >>= continuation)) (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation (popOutcome depth)))
      (withArray state arraydef_0__poly
        (mergeBuffer values len (skipn base (memory state arraydef_0__arena)) savedLen)) /\
    final vardef_0__solve_length=Z.of_nat (Nat.max len savedLen) /\
    final vardef_0__solve_top=Z.of_nat base /\
    final vardef_0__solve_depth=Z.of_nat (Nat.pred depth) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_middle -> name<>vardef_0__solve_size ->
      name<>vardef_0__solve_length -> name<>vardef_0__solve_top -> name<>vardef_0__solve_depth -> final name=nums name).
Proof.
  intros leftEq rightEq phaseEq lenEq baseEq savedEq depthEq addressFit depthFit room arenaRoom storeFit canonical arenaCanonical.
  rewrite phaseMergeNormalized with (start:=start) (span:=span) (len:=len) (savedLen:=savedLen) by assumption.
  set (prepared := mergeFrameNums nums start span len savedLen).
  assert (preparedLen : prepared vardef_0__solve_length=Z.of_nat len).
  { unfold prepared,mergeFrameNums. rewrite !lookupDifferent by congruence. exact lenEq. }
  assert (preparedBase : prepared vardef_0__solve_base=Z.of_nat base).
  { unfold prepared,mergeFrameNums. rewrite !lookupDifferent by congruence. exact baseEq. }
  assert (preparedSaved : prepared vardef_0__solve_saved=Z.of_nat savedLen).
  { unfold prepared,mergeFrameNums. rewrite !lookupDifferent by congruence. exact savedEq. }
  destruct (generated_merge_loop_execution b prepared len base savedLen state values
    (fun _ => mergeFinishBody >>= continuation) preparedLen preparedBase preparedSaved room arenaRoom storeFit canonical arenaCanonical)
    as [finished [execution preserved]]. rewrite execution.
  assert (finishedDepth : finished vardef_0__solve_depth=Z.of_nat depth).
  { rewrite preserved by congruence. unfold prepared,mergeFrameNums. rewrite !lookupDifferent by congruence. exact depthEq. }
  assert (finishedSize : finished vardef_0__solve_size=Z.of_nat (Nat.max len savedLen)).
  { rewrite preserved by congruence. unfold prepared,mergeFrameNums. apply lookupSame. }
  assert (finishedBase : finished vardef_0__solve_base=Z.of_nat base).
  { rewrite preserved by congruence. exact preparedBase. }
  rewrite mergeFinishNormalized with (depth:=depth) (len:=Nat.max len savedLen) (base:=base) by assumption.
  exists (popNums depth (update (update finished vardef_0__solve_length (Z.of_nat (Nat.max len savedLen)))
    vardef_0__solve_top (Z.of_nat base))). split; [reflexivity|].
  split; [rewrite popNums_length,lookupDifferent by congruence; apply lookupSame|].
  split; [rewrite popNums_other by congruence; apply lookupSame|].
  split; [apply popNums_depth; rewrite !lookupDifferent by congruence; exact finishedDepth|].
  intros name notValue notMiddle notSize notLength notTop notDepth.
  rewrite popNums_other by exact notDepth. rewrite !lookupDifferent by congruence. rewrite preserved by exact notValue.
  unfold prepared,mergeFrameNums. rewrite !lookupDifferent by congruence. reflexivity.
Qed.
