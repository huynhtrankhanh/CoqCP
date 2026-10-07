From CoqCP Require Import Options Imperative Execution KoxiaModular KoxiaIntegers KoxiaArrays KoxiaTables
  KoxiaLeafRun KoxiaLeafEvents KoxiaFrames SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Definition popOutcome depth := if Nat.eqb depth 0 then Stop else KeepGoing.
Definition popNums depth (nums : varsfuncdef_0__solve -> Z) :=
  if Nat.eqb depth 0 then nums else update nums vardef_0__solve_depth (Z.of_nat (depth-1)).
Lemma popNums_length depth nums : popNums depth nums vardef_0__solve_length=nums vardef_0__solve_length.
Proof. unfold popNums. destruct (Nat.eqb depth 0); [reflexivity|rewrite lookupDifferent by congruence; reflexivity]. Qed.
Lemma popNums_depth depth nums : nums vardef_0__solve_depth=Z.of_nat depth ->
  popNums depth nums vardef_0__solve_depth=Z.of_nat (Nat.pred depth).
Proof. intro depthEq. unfold popNums. destruct (Nat.eqb depth 0) eqn:zero.
  - apply Nat.eqb_eq in zero. subst depth. exact depthEq.
  - rewrite lookupSame. f_equal. lia.
Qed.
Lemma popNums_other depth nums name : name<>vardef_0__solve_depth -> popNums depth nums name=nums name.
Proof. intro different. unfold popNums. destruct (Nat.eqb depth 0); [reflexivity|apply lookupDifferent; congruence]. Qed.
Theorem generated_leaf_frame_execution b nums start events depth state values len continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+length events) ->
  nums vardef_0__solve_phase=0 -> nums vardef_0__solve_depth=Z.of_nat depth ->
  nums vardef_0__solve_length=Z.of_nat len -> (length events<=32)%nat ->
  (start+length events<length (memory state arraydef_0__prefix))%nat ->
  Z.of_nat (start+start+length events+1)<18446744073709551616 ->
  Z.of_nat depth<18446744073709551616 ->
  (forall offset, (offset<length events)%nat ->
    nth (start+offset+1) (memory state arraydef_0__prefix) 0-
    nth (start+offset) (memory state arraydef_0__prefix) 0=
    (if nth offset events false then 1 else 0)) ->
  (len+length events<=length values)%nat -> Z.of_nat (len+length events)<koxiaModulus -> tableCanonical values ->
  exists final,
    exec (eliminateLocalVariables b nums (solvePhaseBody >>= continuation))
      (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation (popOutcome depth)))
      (withArray state arraydef_0__poly (fst (runBuffers events values len))) /\
    final vardef_0__solve_length=Z.of_nat (snd (runBuffers events values len)) /\
    final vardef_0__solve_depth=Z.of_nat (Nat.pred depth) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous -> name<>vardef_0__solve_length ->
      name<>vardef_0__solve_flag -> name<>vardef_0__solve_middle -> name<>vardef_0__solve_depth -> final name=nums name).
Proof.
  intros leftEq rightEq phaseEq depthEq lenEq small prefixRoom addressFit depthFit flags room lenBound canonical.
  rewrite phaseLeafNormalized with (start:=start) (span:=length events) by (try assumption; lia).
  set (prepared := update nums vardef_0__solve_middle (Z.of_nat ((start+start+length events)/2))).
  assert (preparedLeft : prepared vardef_0__solve_l=Z.of_nat start).
  { unfold prepared. rewrite lookupDifferent by congruence. exact leftEq. }
  assert (preparedLength : prepared vardef_0__solve_length=Z.of_nat len).
  { unfold prepared. rewrite lookupDifferent by congruence. exact lenEq. }
  assert (adjustedFlags : forall offset, (offset<length events)%nat ->
    nth (start+(length events-length events)+offset+1) (memory state arraydef_0__prefix) 0-
    nth (start+(length events-length events)+offset) (memory state arraydef_0__prefix) 0=
    (if nth offset events false then 1 else 0)).
  { intros offset bound. replace (start+(length events-length events)+offset)%nat with (start+offset)%nat by lia. apply flags. exact bound. }
  destruct (generated_leaf_loop_execution b prepared (length events) (length events) start events state values len
    (fun _ => popFrameBody >>= continuation) eq_refl ltac:(lia) preparedLeft preparedLength prefixRoom ltac:(lia)
    adjustedFlags room lenBound canonical) as [finished [execution [finishedLength preserved]]].
  rewrite execution.
  assert (finishedDepth : finished vardef_0__solve_depth=Z.of_nat depth).
  { rewrite preserved by congruence. unfold prepared. rewrite lookupDifferent by congruence. exact depthEq. }
  rewrite popFrameNormalized with (depth:=depth) by assumption.
  exists (popNums depth finished). split.
  - unfold popNums,popOutcome. destruct (Nat.eqb depth 0); reflexivity.
  - split; [rewrite popNums_length; exact finishedLength|]. split; [apply popNums_depth; exact finishedDepth|].
    intros name notValue notPrevious notLength notFlag notMiddle notDepth.
    rewrite popNums_other by exact notDepth. rewrite preserved by assumption.
    unfold prepared. rewrite lookupDifferent by congruence. reflexivity.
Qed.
