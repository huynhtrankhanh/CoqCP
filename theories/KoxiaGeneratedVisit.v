From CoqCP Require Import Options Imperative Execution KoxiaModular KoxiaArrays KoxiaArrayLoops KoxiaTables KoxiaSolveProgram KoxiaMerge KoxiaBufferSplit KoxiaArena KoxiaConvolutionReady KoxiaFrameStores KoxiaFrames KoxiaFrameLeaves KoxiaFrameRight KoxiaFrameMerge KoxiaLeftExecution KoxiaLeafRun.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.

(* A generated visit first loads its five-word frame, then executes the
   corresponding phase.  This lemma connects that actual generated action to
   the already verified leaf transition. *)
Theorem generated_leaf_visit_execution b nums visits remaining start events depth state values len continuation :
  nums vardef_0__solve_depth=Z.of_nat depth ->
  nums vardef_0__solve_length=Z.of_nat len ->
  (depth<length (memory state arraydef_0__frames))%nat ->
  nth depth (memory state arraydef_0__frames) (0,0,0,0,0)=
    (Z.of_nat start,Z.of_nat (start+length events),0,Z.of_nat 0,Z.of_nat 0) ->
  (length events<=32)%nat ->
  (start+length events<length (memory state arraydef_0__prefix))%nat ->
  Z.of_nat (start+start+length events+1)<18446744073709551616 ->
  Z.of_nat depth<18446744073709551616 ->
  (forall offset, (offset<length events)%nat ->
    nth (start+offset+1) (memory state arraydef_0__prefix) 0-
    nth (start+offset) (memory state arraydef_0__prefix) 0=
    (if nth offset events false then 1 else 0)) ->
  (len+length events<=length values)%nat ->
  Z.of_nat (len+length events)<koxiaModulus ->
  tableCanonical values ->
  exists final,
    exec (eliminateLocalVariables b nums (solveVisitBody visits remaining >>= continuation))
      (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation (popOutcome depth)))
      (withArray state arraydef_0__poly (fst (runBuffers events values len))) /\
    final vardef_0__solve_length=Z.of_nat (snd (runBuffers events values len)) /\
    final vardef_0__solve_depth=Z.of_nat (Nat.pred depth) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_previous ->
      name<>vardef_0__solve_length -> name<>vardef_0__solve_flag ->
      name<>vardef_0__solve_middle -> name<>vardef_0__solve_depth ->
      final name=loadedNums nums
        (Z.of_nat start,Z.of_nat (start+length events),0,Z.of_nat 0,Z.of_nat 0) name).
Proof.
  intros depthEq lenEq depthRoom frameContents small prefixRoom addressFit depthFit flags bufferRoom lengthBound canonical.
  assert (depthRoom' : (depth<length (memory (withArray state arraydef_0__poly values) arraydef_0__frames))%nat).
  { rewrite withArray_preserve_other by congruence. exact depthRoom. }
  rewrite (@generated_frame_load b nums (withArray state arraydef_0__poly values)
    visits remaining depth continuation depthEq depthRoom').
  rewrite withArray_preserve_other by congruence.
  rewrite frameContents.
  eapply generated_leaf_frame_execution; eauto.
Qed.

Theorem generated_left_visit_execution b nums visits remaining start span len cut base depth state values continuation :
  nums vardef_0__solve_depth=Z.of_nat depth ->
  nums vardef_0__solve_length=Z.of_nat len ->
  nums vardef_0__solve_top=Z.of_nat base ->
  (depth<length (memory state arraydef_0__frames))%nat ->
  nth depth (memory state arraydef_0__frames) (0,0,0,0,0)=
    (Z.of_nat start,Z.of_nat (start+span),0,Z.of_nat 0,Z.of_nat 0) ->
  (32<span)%nat ->
  (start+span<length (memory state arraydef_0__prefix))%nat ->
  nth (start+span) (memory state arraydef_0__prefix) 0-
    nth start (memory state arraydef_0__prefix) 0=Z.of_nat cut ->
  (cut<=span)%nat ->
  Z.of_nat (len+start+start+span)<18446744073709551616 ->
  Z.of_nat (base+savedLength len cut span)<18446744073709551616 ->
  Z.of_nat (S depth)<18446744073709551616 ->
  (S depth<length (memory state arraydef_0__frames))%nat ->
  ((cut<len)%nat -> ConvolutionReady (withArray state arraydef_0__poly values) len cut span base) ->
  exists final,
    exec (eliminateLocalVariables b nums (solveVisitBody visits remaining >>= continuation))
      (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation KeepGoing))
      (storedChildFrames
        (leftSavedState (withArray state arraydef_0__poly values) len cut span base)
        depth start span ((start+start+span)/2) base (savedLength len cut span)) /\
    final vardef_0__solve_length=Z.of_nat (Nat.min len cut) /\
    final vardef_0__solve_top=Z.of_nat (base+savedLength len cut span) /\
    final vardef_0__solve_depth=Z.of_nat (S depth) /\
    (forall name, name<>vardef_0__solve_special -> name<>vardef_0__solve_small ->
      name<>vardef_0__solve_hi -> name<>vardef_0__solve_top ->
      name<>vardef_0__solve_length -> name<>vardef_0__solve_depth ->
      name<>vardef_0__solve_middle -> final name=loadedNums nums
        (Z.of_nat start,Z.of_nat (start+span),0,Z.of_nat 0,Z.of_nat 0) name).
Proof.
  intros depthEq lenEq topEq depthRoom frameContents large prefixRoom prefixDiff cutBound addressFit arenaFit depthFit childRoom ready.
  assert (depthRoom' : (depth<length (memory (withArray state arraydef_0__poly values) arraydef_0__frames))%nat).
  { rewrite withArray_preserve_other by congruence. exact depthRoom. }
  assert (childRoom' : (S depth<length (memory (withArray state arraydef_0__poly values) arraydef_0__frames))%nat).
  { rewrite withArray_preserve_other by congruence. exact childRoom. }
  rewrite (@generated_frame_load b nums (withArray state arraydef_0__poly values)
    visits remaining depth continuation depthEq depthRoom').
  rewrite withArray_preserve_other by congruence.
  rewrite frameContents.
  eapply generated_left_frame_execution; eauto.
Qed.

Theorem generated_right_visit_execution b nums visits remaining start span depth base saved state continuation :
  nums vardef_0__solve_depth=Z.of_nat depth ->
  (depth<length (memory state arraydef_0__frames))%nat ->
  nth depth (memory state arraydef_0__frames) (0,0,0,0,0)=
    (Z.of_nat start,Z.of_nat (start+span),1,Z.of_nat base,Z.of_nat saved) ->
  Z.of_nat (start+start+span)<18446744073709551616 ->
  Z.of_nat (S depth)<18446744073709551616 ->
  (S depth<length (memory state arraydef_0__frames))%nat ->
  exec (eliminateLocalVariables b nums (solveVisitBody visits remaining >>= continuation)) state=
  exec (eliminateLocalVariables b
    (rightFrameNums (loadedNums nums
      (Z.of_nat start,Z.of_nat (start+span),1,Z.of_nat base,Z.of_nat saved)) start span depth)
    (continuation KeepGoing))
    (withArray state arraydef_0__frames
      (<[S depth:=(Z.of_nat ((start+start+span)/2),Z.of_nat (start+span),0,0,0)]>
        (<[depth:=(Z.of_nat start,Z.of_nat (start+span),2,Z.of_nat base,Z.of_nat saved)]>
          (memory state arraydef_0__frames)))).
Proof.
  intros depthEq depthRoom frameContents addressFit depthFit childRoom.
  rewrite (@generated_frame_load b nums state visits remaining depth continuation depthEq depthRoom).
  rewrite frameContents.
  rewrite <- (withArray_self state arraydef_0__frames) at 1.
  eapply generated_right_frame_execution; eauto.
Qed.

Theorem generated_merge_visit_execution b nums visits remaining start span len base savedLen depth state values continuation :
  nums vardef_0__solve_depth=Z.of_nat depth ->
  nums vardef_0__solve_length=Z.of_nat len ->
  (depth<length (memory state arraydef_0__frames))%nat ->
  nth depth (memory state arraydef_0__frames) (0,0,0,0,0)=
    (Z.of_nat start,Z.of_nat (start+span),2,Z.of_nat base,Z.of_nat savedLen) ->
  Z.of_nat (start+start+span)<18446744073709551616 ->
  Z.of_nat depth<18446744073709551616 ->
  (Nat.max len savedLen<=length values)%nat ->
  (base+savedLen<=length (memory state arraydef_0__arena))%nat ->
  Z.of_nat (base+Nat.max len savedLen)<18446744073709551616 ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__arena) ->
  exists final,
    exec (eliminateLocalVariables b nums (solveVisitBody visits remaining >>= continuation))
    (withArray state arraydef_0__poly values)=
    exec (eliminateLocalVariables b final (continuation (popOutcome depth)))
      (withArray state arraydef_0__poly
        (mergeBuffer values len (skipn base (memory state arraydef_0__arena)) savedLen)) /\
    final vardef_0__solve_length=Z.of_nat (Nat.max len savedLen) /\
    final vardef_0__solve_top=Z.of_nat base /\
    final vardef_0__solve_depth=Z.of_nat (Nat.pred depth) /\
    (forall name, name<>vardef_0__solve_value -> name<>vardef_0__solve_middle ->
      name<>vardef_0__solve_size -> name<>vardef_0__solve_length ->
      name<>vardef_0__solve_top -> name<>vardef_0__solve_depth ->
      final name=loadedNums nums
        (Z.of_nat start,Z.of_nat (start+span),2,Z.of_nat base,Z.of_nat savedLen) name).
Proof.
  intros depthEq lenEq depthRoom frameContents addressFit depthFit polyRoom arenaRoom storeFit canonical arenaCanonical.
  assert (depthRoom' : (depth<length (memory (withArray state arraydef_0__poly values) arraydef_0__frames))%nat).
  { rewrite withArray_preserve_other by congruence. exact depthRoom. }
  rewrite (@generated_frame_load b nums (withArray state arraydef_0__poly values)
    visits remaining depth continuation depthEq depthRoom').
  rewrite withArray_preserve_other by congruence.
  rewrite frameContents.
  assert (loadedLen : loadedNums nums
    (Z.of_nat start,Z.of_nat (start+span),2,Z.of_nat base,Z.of_nat savedLen)
    vardef_0__solve_length=Z.of_nat len).
  { rewrite loadedNums_other by congruence. exact lenEq. }
  eapply generated_merge_frame_execution; eauto.
Qed.
