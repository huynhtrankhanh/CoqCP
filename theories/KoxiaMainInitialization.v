From CoqCP Require Import Options Imperative Execution KoxiaMainProgram KoxiaMainMemory KoxiaArrays KoxiaWorkspace
  KoxiaArrayLoops KoxiaConvolution KoxiaRoots KoxiaFourier KoxiaSizes KoxiaTables KoxiaTableLoops KoxiaModular KoxiaBinomial KoxiaMemoryPreservation.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque loop funcdef_0__power mainRootStageBody mainFactorialBody mainInverseFactorialBody.

Ltac simplify_initialized_memory := repeat progress
  (simplify_main_memory; try rewrite withResult_other by congruence).

Theorem generated_workspace_execution state b nums n :
  1<=Z.of_nat n<=500000 -> nums vardef_0__main_n=Z.of_nat n -> workspaceEmpty state ->
  length (memory state arraydef_0__frames)=32%nat -> (2<length (memory state arraydef_0__result))%nat ->
  exists finalNums final,
    (forall continuation, exec (eliminateLocalVariables b nums (mainWorkspaceBody >>=continuation)) state=
      exec (eliminateLocalVariables b finalNums (continuation tt)) final) /\
    SolverWorkspace final n (mainStage n) /\
    stdin final=stdin state /\ stdout final=stdout state /\
    memory final arraydef_0__sequence=memory state arraydef_0__sequence /\
    memory final arraydef_0__printBuffer=memory state arraydef_0__printBuffer /\
    finalNums vardef_0__main_n=nums vardef_0__main_n /\
    finalNums vardef_0__main_split=nums vardef_0__main_split.
Proof.
  intros inputBound nEq empty frames result.
  destruct (ceilingStage_correct (2*Z.of_nat n+1) ltac:(lia)) as [stageBound [capacity upper]].
  change (mainStage n<=20)%nat in stageBound.
  change (2*Z.of_nat n+1<=stageSize (mainStage n)) in capacity.
  pose (allocated:=lateAllocated (earlyAllocated state n) (sizeNat (mainStage n))).
  pose (readyNums:=mainReadyNums nums n).
  assert (readyN : readyNums vardef_0__main_n=Z.of_nat n).
  { unfold readyNums,mainReadyNums,mainSizedNums. rewrite !lookupDifferent by congruence. exact nEq. }
  destruct (root_initializer_execution (mainStage n) allocated b readyNums stageBound
    ltac:(unfold readyNums,mainReadyNums; apply lookupSame)
    ltac:(unfold readyNums,mainReadyNums,mainSizedNums; rewrite lookupDifferent by congruence; apply lookupSame)
    ltac:(unfold allocated; rewrite allocated_memory,repeat_length; lia)
    ltac:(unfold allocated; rewrite allocated_memory; apply zeroCanonical)
    ltac:(unfold allocated; rewrite allocated_memory; exact result))
    as [finishedNums [rootState [rootExec [rootValues [rootCanonical [rootCorrect [rootResult
      [rootInput [rootOutput [rootOther rootNums]]]]]]]]]].
  assert (finishedN : finishedNums vardef_0__main_n=Z.of_nat n).
  { rewrite rootNums by congruence. exact readyN. }
  assert (rootUnchanged : forall name, name<>arraydef_0__roots -> name<>arraydef_0__result ->
    memory rootState name=memory allocated name).
  { exact rootOther. }
  pose (factState:=withArray rootState arraydef_0__factorial
    (factorialTableValues n (memory rootState arraydef_0__factorial))).
  pose (final:=withArray (withResult factState (inverseFactorialMod n)) arraydef_0__inverseFactorial
    (inverseFactorialTableValues n (memory factState arraydef_0__inverseFactorial))).
  assert (rootFac : memory rootState arraydef_0__factorial=repeat 0 (S n)).
  { rewrite rootOther by congruence. unfold allocated. apply allocated_memory. }
  assert (rootInv : memory rootState arraydef_0__inverseFactorial=repeat 0 (S n)).
  { rewrite rootOther by congruence. unfold allocated. apply allocated_memory. }
  assert (factInv : memory factState arraydef_0__inverseFactorial=repeat 0 (S n)).
  { unfold factState. rewrite withArray_preserve_other by congruence. exact rootInv. }
  assert (factFac : memory factState arraydef_0__factorial=factorialTableValues n (repeat 0 (S n))).
  { unfold factState. rewrite withArray_preserve_same,rootFac. reflexivity. }
  assert (factResult : (2<length (memory factState arraydef_0__result))%nat).
  { unfold factState. rewrite withArray_preserve_other by congruence. exact rootResult. }
  exists finishedNums,final. split.
  - intro continuation. rewrite mainWorkspaceNormalized with (n:=n) by lia.
    rewrite earlyGrow_execution by exact empty.
    rewrite lateGrow_execution by exact empty. fold allocated readyNums.
    unfold mainTablesBody. rewrite <-!bindAssoc. rewrite rootExec.
    rewrite mainFactorialDynamicNormalized with (n:=n) by exact finishedN.
    rewrite factorial_initializer_execution with (total:=n).
    2: rewrite rootFac,repeat_length; lia.
    2: unfold koxiaModulus; lia.
    2: rewrite rootFac; apply zeroCanonical.
    fold factState.
    rewrite mainInverseDynamicNormalized with (n:=n) by exact finishedN.
    rewrite inverse_initializer_execution with (total:=n).
    2: exact finishedN.
    2: unfold koxiaModulus; lia.
    2: rewrite factInv,repeat_length; lia.
    2: rewrite factInv; apply zeroCanonical.
    2: rewrite factFac,factorialTableValues_length,repeat_length; lia.
    2: rewrite factFac; apply factorialTableValues_lookup; rewrite ?repeat_length; lia.
    2: exact factResult.
    reflexivity.
  - split.
    + apply builtWorkspace.
      * exact inputBound.
      * exact stageBound.
      * exact capacity.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
      * unfold final,factState. simplify_initialized_memory. rewrite rootValues. unfold allocated. rewrite allocated_memory. reflexivity.
      * unfold final. simplify_initialized_memory. exact factFac.
      * unfold final. simplify_initialized_memory. rewrite factInv. reflexivity.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. rewrite allocated_memory. exact frames.
      * unfold final. simplify_initialized_memory. rewrite withResult_memory,length_insert. exact factResult.
    + split; [unfold final,factState; change (stdin rootState=stdin state); rewrite rootInput; reflexivity|].
      split; [unfold final,factState; change (stdout rootState=stdout state); rewrite rootOutput; reflexivity|].
      split.
      * unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
      * split.
        -- unfold final,factState. simplify_initialized_memory. rewrite rootOther by congruence. unfold allocated. apply allocated_memory.
        -- split; rewrite rootNums by congruence; unfold readyNums,mainReadyNums,mainSizedNums;
             rewrite !lookupDifferent by congruence; reflexivity.
Qed.
