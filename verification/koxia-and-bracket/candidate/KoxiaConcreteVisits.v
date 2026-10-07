From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaArrays KoxiaArrayLoops KoxiaModular KoxiaTables KoxiaPolynomial KoxiaLeafRun KoxiaBufferSplit KoxiaArena KoxiaTraversal KoxiaTreeBuffers KoxiaVisitSchedule KoxiaVisitMemory KoxiaSolveProgram KoxiaFrames KoxiaFrameLeaves KoxiaFrameRight KoxiaFrameMerge KoxiaFrameStores KoxiaLeftExecution KoxiaGeneratedVisit KoxiaConvolution KoxiaConvolutionReady.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Logic.FunctionalExtensionality Lia.

Definition SolverMachine := @Machine arrayIndex1 (arrayType _ environment1).
Record VisitConfiguration := {
  configurationStack : list AnnotatedFrame;
  configurationMemory : SolverMachine;
  configurationLength : nat;
  configurationTop : nat
}.

Definition configurationDepth configuration := Nat.pred (length (configurationStack configuration)).
Definition configurationValues configuration := memory (configurationMemory configuration) arraydef_0__poly.
Definition configurationLocals nums configuration :=
  nums vardef_0__solve_depth=Z.of_nat (configurationDepth configuration) /\
  nums vardef_0__solve_length=Z.of_nat (configurationLength configuration) /\
  nums vardef_0__solve_top=Z.of_nat (configurationTop configuration).

Definition nextVisit configuration : VisitConfiguration :=
  let state := configurationMemory configuration in
  let values := configurationValues configuration in
  let len := configurationLength configuration in
  let top := configurationTop configuration in
  match configurationStack configuration with
  | [] => configuration
  | VisitTree start (Leaf events)::stack =>
      let result := runBuffers events values len in
      {| configurationStack:=stack;
         configurationMemory:=withArray state arraydef_0__poly (fst result);
         configurationLength:=snd result; configurationTop:=top |}
  | VisitTree start (Branch leftTree rightTree)::stack =>
      let events := treeEvents leftTree++treeEvents rightTree in
      let span := length events in
      let cut := specialCount events in
      let saved := savedBuffer values len cut span in
      let savedLen := savedLength len cut span in
      let middle := start+length (treeEvents leftTree) in
      {| configurationStack:=VisitTree start leftTree::VisitRight start middle span rightTree saved savedLen top::stack;
         configurationMemory:=storedChildFrames (leftSavedState state len cut span top)
           (length stack) start span middle top savedLen;
         configurationLength:=Nat.min len cut; configurationTop:=top+savedLen |}
  | VisitRight start middle span tree saved savedLen base::stack =>
      {| configurationStack:=VisitTree middle tree::VisitMerge start span saved savedLen base::stack;
         configurationMemory:=withArray state arraydef_0__frames
           (<[S (length stack):=encodeAnnotatedFrame (VisitTree middle tree)]>
             (<[length stack:=encodeAnnotatedFrame (VisitMerge start span saved savedLen base)]>
               (memory state arraydef_0__frames)));
         configurationLength:=len; configurationTop:=top |}
  | VisitMerge start span saved savedLen base::stack =>
      {| configurationStack:=stack;
         configurationMemory:=withArray state arraydef_0__poly (mergeBuffer values len saved savedLen);
         configurationLength:=Nat.max len savedLen; configurationTop:=base |}
  end.

Definition visitOutcome configuration :=
  match configurationStack (nextVisit configuration) with [] => Stop | _ => KeepGoing end.

(* All hypotheses concern data and addresses.  No execution fact is included
   in this safety predicate. *)
Definition visitReady configuration :=
  let state := configurationMemory configuration in
  let values := configurationValues configuration in
  let len := configurationLength configuration in
  let top := configurationTop configuration in
  framesRepresent (memory state arraydef_0__frames) (configurationStack configuration) /\
  match configurationStack configuration with
  | [] => True
  | VisitTree start (Leaf events)::stack =>
      length events<=32 /\ start+length events<length (memory state arraydef_0__prefix) /\
      (Z.of_nat (start+start+length events+1)<18446744073709551616)%Z /\
      (Z.of_nat (length stack)<18446744073709551616)%Z /\
      (forall offset, offset<length events ->
        (nth (start+offset+1) (memory state arraydef_0__prefix) 0-
         nth (start+offset) (memory state arraydef_0__prefix) 0=
         (if nth offset events false then 1 else 0))%Z) /\
      len+length events<=length values /\ (Z.of_nat (len+length events)<koxiaModulus)%Z /\
      tableCanonical values
  | VisitTree start (Branch leftTree rightTree)::stack =>
      let events := treeEvents leftTree++treeEvents rightTree in
      let span := length events in
      let cut := specialCount events in
      32<span /\ start+length (treeEvents leftTree)=(start+start+span)/2 /\
      start+span<length (memory state arraydef_0__prefix) /\
      (nth (start+span) (memory state arraydef_0__prefix) 0-
       nth start (memory state arraydef_0__prefix) 0=Z.of_nat cut)%Z /\
      cut<=span /\
      (Z.of_nat (len+start+start+span)<18446744073709551616)%Z /\
      (Z.of_nat (top+savedLength len cut span)<18446744073709551616)%Z /\
      (Z.of_nat (S (length stack))<18446744073709551616)%Z /\
      S (length stack)<length (memory state arraydef_0__frames) /\
      (cut<len -> ConvolutionReady state len cut span top)
  | VisitRight start middle span tree saved savedLen base::stack =>
      middle=(start+start+span)/2 /\ middle+length (treeEvents tree)=start+span /\
      (Z.of_nat (start+start+span)<18446744073709551616)%Z /\
      (Z.of_nat (S (length stack))<18446744073709551616)%Z /\
      S (length stack)<length (memory state arraydef_0__frames)
  | VisitMerge start span saved savedLen base::stack =>
      savedLen=length saved /\ arenaContains (memory state arraydef_0__arena) base saved /\
      (Z.of_nat (start+start+span)<18446744073709551616)%Z /\
      (Z.of_nat (length stack)<18446744073709551616)%Z /\
      Nat.max len savedLen<=length values /\ base+savedLen<=length (memory state arraydef_0__arena) /\
      (Z.of_nat (base+Nat.max len savedLen)<18446744073709551616)%Z /\
      tableCanonical values /\ tableCanonical (memory state arraydef_0__arena)
  end.

Lemma solveVisitBody_constant visits remaining : solveVisitBody visits remaining=solveVisitBody 0%Z 0.
Proof. reflexivity. Qed.

Lemma configurationLocals_cons nums frame stack state len top :
  configurationLocals nums
    {| configurationStack:=frame::stack; configurationMemory:=state;
       configurationLength:=len; configurationTop:=top |} ->
  nums vardef_0__solve_depth=Z.of_nat (length stack) /\
  nums vardef_0__solve_length=Z.of_nat len /\ nums vardef_0__solve_top=Z.of_nat top.
Proof. exact (fun hypothesis=>hypothesis). Qed.

Lemma popOutcome_stack (stack : list AnnotatedFrame) : popOutcome (length stack)=match stack with []=>Stop | _=>KeepGoing end.
Proof. destruct stack; reflexivity. Qed.

Theorem generated_visit_step b nums visits remaining configuration continuation :
  configurationStack configuration<>[] -> visitReady configuration -> configurationLocals nums configuration ->
  exists final,
    exec (eliminateLocalVariables b nums (solveVisitBody visits remaining >>= continuation))
      (configurationMemory configuration)=
    exec (eliminateLocalVariables b final (continuation (visitOutcome configuration)))
      (configurationMemory (nextVisit configuration)) /\
    final vardef_0__solve_length=Z.of_nat (configurationLength (nextVisit configuration)) /\
    final vardef_0__solve_depth=Z.of_nat (configurationDepth (nextVisit configuration)) /\
    final vardef_0__solve_top=Z.of_nat (configurationTop (nextVisit configuration)).
Proof.
  destruct configuration as [stack state len top].
  destruct stack as [|frame stack]; [intros impossible; exfalso; apply impossible; reflexivity|].
  intros nonempty [frames ready] [depthEq [lenEq topEq]].
  cbn [configurationMemory configurationStack configurationLength configurationTop configurationValues configurationDepth] in *.
  assert (depthRoom : length stack<length (memory state arraydef_0__frames)).
  { pose proof (framesRepresent_room _ _ frames) as room. cbn [length configurationStack configurationMemory] in room. exact room. }
  change (nums vardef_0__solve_depth=Z.of_nat (length stack)) in depthEq.
  pose proof (framesRepresent_top _ _ _ frames) as frameContents.
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
  - destruct tree as [events|leftTree rightTree].
    + cbn [visitReady configurationMemory configurationValues configurationLength configurationTop configurationStack] in ready.
      destruct ready as [small [prefixRoom [addressFit [depthFit [flags [polyRoom [lengthBound canonical]]]]]]].
      destruct (@generated_leaf_visit_execution b nums visits remaining start events (length stack) state
        (memory state arraydef_0__poly) len continuation depthEq lenEq depthRoom frameContents
        small prefixRoom addressFit depthFit flags polyRoom lengthBound canonical)
        as [final [execution [finalLen [finalDepth others]]]].
      rewrite withArray_self in execution.
      exists final. cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop
        configurationStack configurationDepth visitOutcome].
      rewrite <-popOutcome_stack. split; [exact execution|]. split; [exact finalLen|].
      split; [exact finalDepth|]. rewrite others by congruence.
      rewrite loadedNums_other by congruence. exact topEq.
    + cbn [visitReady configurationMemory configurationValues configurationLength configurationTop configurationStack] in ready.
      destruct ready as [large [middleEq [prefixRoom [difference [cutBound [addressFit [arenaFit [depthFit [childRoom ready]]]]]]]]].
      assert (ready' : specialCount (treeEvents leftTree++treeEvents rightTree)<len ->
        ConvolutionReady (withArray state arraydef_0__poly (memory state arraydef_0__poly)) len
          (specialCount (treeEvents leftTree++treeEvents rightTree))
          (length (treeEvents leftTree++treeEvents rightTree)) top).
      { rewrite withArray_self. exact ready. }
      destruct (@generated_left_visit_execution b nums visits remaining start
        (length (treeEvents leftTree++treeEvents rightTree)) len
        (specialCount (treeEvents leftTree++treeEvents rightTree)) top (length stack) state
        (memory state arraydef_0__poly) continuation depthEq lenEq topEq depthRoom frameContents
        large prefixRoom difference cutBound addressFit arenaFit depthFit childRoom ready')
        as [final [execution [finalLen [finalTop [finalDepth others]]]]].
      rewrite withArray_self in execution. rewrite <-middleEq in execution.
      exists final. cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop
        configurationStack configurationDepth visitOutcome].
      repeat split; assumption.
  - cbn [visitReady configurationMemory configurationValues configurationLength configurationTop configurationStack] in ready.
    destruct ready as [middleEq [endEq [addressFit [depthFit childRoom]]]].
    pose proof (@generated_right_visit_execution b nums visits remaining start span (length stack) base savedLen state
      continuation depthEq depthRoom frameContents addressFit depthFit childRoom) as execution.
    rewrite <-middleEq,<-endEq in execution.
    exists (rightFrameNums (loadedNums nums
      (Z.of_nat start,Z.of_nat (start+span),1%Z,Z.of_nat base,Z.of_nat savedLen)) start span (length stack)).
    cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop
      configurationStack configurationDepth visitOutcome encodeAnnotatedFrame].
    rewrite <-endEq.
    split; [exact execution|]. split.
    + rewrite rightFrameNums_other,loadedNums_other by congruence. exact lenEq.
    + split; [apply rightFrameNums_depth|].
      rewrite rightFrameNums_other,loadedNums_other by congruence. exact topEq.
  - cbn [visitReady configurationMemory configurationValues configurationLength configurationTop configurationStack] in ready.
    destruct ready as [savedLengthEq [contains [addressFit [depthFit [polyRoom [arenaRoom [storeFit [canonical arenaCanonical]]]]]]]].
    destruct (@generated_merge_visit_execution b nums visits remaining start span len base savedLen (length stack)
      state (memory state arraydef_0__poly) continuation depthEq lenEq depthRoom frameContents addressFit depthFit
      polyRoom arenaRoom storeFit canonical arenaCanonical)
      as [final [execution [finalLen [finalTop [finalDepth others]]]]].
    rewrite withArray_self in execution. rewrite savedLengthEq,mergeBuffer_saved in execution by exact contains.
    exists final. cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop
      configurationStack configurationDepth visitOutcome].
    rewrite <-popOutcome_stack. rewrite <-savedLengthEq in execution. repeat split; assumption.
Qed.

Lemma leftSavedState_io state len cut span base :
  stdin (leftSavedState state len cut span base)=stdin state /\
  stdout (leftSavedState state len cut span base)=stdout state.
Proof. unfold leftSavedState. destruct (Nat.ltb cut len); split; reflexivity. Qed.

Lemma nextVisit_io configuration :
  stdin (configurationMemory (nextVisit configuration))=stdin (configurationMemory configuration) /\
  stdout (configurationMemory (nextVisit configuration))=stdout (configurationMemory configuration).
Proof.
  destruct configuration as [stack state len top]. destruct stack as [|frame stack]; [split; reflexivity|].
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
  - destruct tree as [events|leftTree rightTree]; [split; reflexivity|].
    cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop
      configurationStack storedChildFrames withArray withMemory stdin stdout].
    apply leftSavedState_io.
  - split; reflexivity.
  - split; reflexivity.
Qed.

Lemma nextVisit_preserves configuration name : name<>arraydef_0__poly -> name<>arraydef_0__frames ->
  name<>arraydef_0__work -> name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
  memory (configurationMemory (nextVisit configuration)) name=memory (configurationMemory configuration) name.
Proof.
  intros. destruct configuration as [stack state len top]. destruct stack as [|frame stack]; [reflexivity|].
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base];
    [destruct tree as [events|leftTree rightTree]| |].
  all: cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop configurationStack].
  - apply withArray_preserve_other; assumption.
  - rewrite storedChildFrames_preserves,leftSavedState_preserves by assumption. reflexivity.
  - apply withArray_preserve_other; assumption.
  - apply withArray_preserve_other; assumption.
Qed.

Fixpoint runConcreteVisits fuel configuration :=
  match fuel,configurationStack configuration with
  | O,_ | _,[] => configuration
  | S fuel,_ => runConcreteVisits fuel (nextVisit configuration)
  end.

Fixpoint safeConcreteVisits fuel configuration : Prop :=
  match fuel,configurationStack configuration with
  | O,_ | _,[] => True
  | S fuel,_ => visitReady configuration /\ safeConcreteVisits fuel (nextVisit configuration)
  end.

Lemma runConcreteVisits_empty fuel configuration : configurationStack configuration=[] ->
  runConcreteVisits fuel configuration=configuration.
Proof. intro empty. destruct fuel; [reflexivity|cbn [runConcreteVisits]; rewrite empty; reflexivity]. Qed.

Theorem generated_visit_loop_execution b nums visits fuel configuration continuation :
  (configurationStack configuration<>[] \/ fuel=0) ->
  safeConcreteVisits fuel configuration -> configurationLocals nums configuration ->
  exists final,
    exec (eliminateLocalVariables b nums (loop fuel (solveVisitBody visits) >>= continuation))
      (configurationMemory configuration)=
    exec (eliminateLocalVariables b final (continuation tt))
      (configurationMemory (runConcreteVisits fuel configuration)) /\
    configurationLocals final (runConcreteVisits fuel configuration).
Proof.
  induction fuel as [|fuel IH] in nums,configuration |- *.
  - intros nonempty safe locals. exists nums. split; [reflexivity|exact locals].
  - intros [nonempty|impossible] safe locals; [|discriminate].
    cbn [safeConcreteVisits] in safe. destruct (configurationStack configuration) eqn:stackEq;
      [exfalso; apply nonempty; reflexivity|].
    destruct safe as [ready safe].
    rewrite loop_S,<-bindAssoc.
    destruct (generated_visit_step b nums visits fuel configuration
      (fun outcome => (match outcome with KeepGoing=>loop fuel (solveVisitBody visits)
        | Stop=>Done _ _ _ tt end) >>= continuation) ltac:(rewrite stackEq; discriminate) ready locals)
      as [finished [execution [finalLen [finalDepth finalTop]]]].
    rewrite execution.
    assert (nextLocals : configurationLocals finished (nextVisit configuration)).
    { repeat split; assumption. }
    destruct (configurationStack (nextVisit configuration)) eqn:nextStack.
    + assert (outcome : visitOutcome configuration=Stop) by (unfold visitOutcome; rewrite nextStack; reflexivity).
      rewrite outcome. cbn [bind]. exists finished.
      cbn [runConcreteVisits]. rewrite stackEq,runConcreteVisits_empty by exact nextStack.
      split; [reflexivity|exact nextLocals].
    + assert (outcome : visitOutcome configuration=KeepGoing) by (unfold visitOutcome; rewrite nextStack; reflexivity).
      rewrite outcome. cbn [runConcreteVisits]. rewrite stackEq.
      apply IH; [left; rewrite nextStack; discriminate|exact safe|exact nextLocals].
Qed.

Definition abstractConfiguration configuration :=
  (configurationStack configuration,
    (configurationValues configuration,configurationLength configuration,configurationTop configuration)).

Lemma nextVisit_abstract configuration :
  abstractConfiguration (nextVisit configuration)=
  annotatedVisit 1 (configurationStack configuration) (configurationValues configuration)
    (configurationLength configuration) (configurationTop configuration).
Proof.
  destruct configuration as [stack state len top]. destruct stack as [|frame stack].
  - reflexivity.
  - destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
    + destruct tree as [events|leftTree rightTree].
      * cbv beta iota zeta delta [abstractConfiguration nextVisit configurationMemory configurationValues
          configurationLength configurationTop configurationStack annotatedVisit].
        rewrite withArray_preserve_same. reflexivity.
      * cbv beta iota zeta delta [abstractConfiguration nextVisit configurationMemory configurationValues
          configurationLength configurationTop configurationStack annotatedVisit].
        rewrite storedChildFrames_preserves by congruence.
        rewrite leftSavedState_preserves by congruence. reflexivity.
    + cbv beta iota zeta delta [abstractConfiguration nextVisit configurationMemory configurationValues
        configurationLength configurationTop configurationStack annotatedVisit].
      rewrite withArray_preserve_other by congruence. reflexivity.
    + cbv beta iota zeta delta [abstractConfiguration nextVisit configurationMemory configurationValues
        configurationLength configurationTop configurationStack annotatedVisit].
      rewrite withArray_preserve_same. reflexivity.
Qed.

Lemma annotatedVisit_step fuel stack values len top :
  annotatedVisit (S fuel) stack values len top=
  let next := annotatedVisit 1 stack values len top in
  annotatedVisit fuel (fst next) (fst (fst (snd next))) (snd (fst (snd next))) (snd (snd next)).
Proof.
  destruct stack as [|frame stack]; [symmetry; apply annotatedVisit_empty|].
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base];
    [destruct tree| |]; reflexivity.
Qed.

Theorem runConcreteVisits_abstract fuel configuration :
  abstractConfiguration (runConcreteVisits fuel configuration)=
  annotatedVisit fuel (configurationStack configuration) (configurationValues configuration)
    (configurationLength configuration) (configurationTop configuration).
Proof.
  induction fuel as [|fuel IH] in configuration |- *; [reflexivity|].
  cbn [runConcreteVisits]. destruct (configurationStack configuration) eqn:stackEq.
  - unfold abstractConfiguration. rewrite stackEq. reflexivity.
  - rewrite IH,annotatedVisit_step.
    rewrite <-stackEq,<-nextVisit_abstract. reflexivity.
Qed.

Theorem runConcreteVisits_io fuel configuration :
  stdin (configurationMemory (runConcreteVisits fuel configuration))=stdin (configurationMemory configuration) /\
  stdout (configurationMemory (runConcreteVisits fuel configuration))=stdout (configurationMemory configuration).
Proof.
  induction fuel as [|fuel IH] in configuration |- *; [split; reflexivity|].
  cbn [runConcreteVisits]. destruct (configurationStack configuration); [split; reflexivity|].
  destruct (IH (nextVisit configuration)) as [input output].
  destruct (nextVisit_io configuration) as [inputStep outputStep]. split; congruence.
Qed.

Theorem runConcreteVisits_preserves fuel configuration name : name<>arraydef_0__poly -> name<>arraydef_0__frames ->
  name<>arraydef_0__work -> name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
  memory (configurationMemory (runConcreteVisits fuel configuration)) name=memory (configurationMemory configuration) name.
Proof.
  intros. induction fuel as [|fuel IH] in configuration |- *; [reflexivity|].
  cbn [runConcreteVisits]. destruct (configurationStack configuration); [reflexivity|].
  rewrite IH,nextVisit_preserves by assumption. reflexivity.
Qed.
