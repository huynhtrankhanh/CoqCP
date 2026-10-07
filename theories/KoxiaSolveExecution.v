From CoqCP Require Import Options Imperative Execution KoxiaIntegers KoxiaArrays KoxiaArrayLoops KoxiaModular
  KoxiaTables KoxiaTableLoops KoxiaPolynomial KoxiaPolynomialBuffers KoxiaLeafRun KoxiaBufferSplit KoxiaArena
  KoxiaPaths KoxiaTraversal KoxiaTreeBuffers KoxiaPrefixFlags KoxiaVisitSchedule KoxiaVisitMemory
  KoxiaConcreteVisits KoxiaVisitInvariant KoxiaSolveProgram KoxiaPreprocess KoxiaWorkspace
  KoxiaConvolution KoxiaFrameStores KoxiaFourier KoxiaMemoryPreservation SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque solvePrepBody solveVisitBody funcdef_0__convolve funcdef_0__ntt balancedTree treeBuffers runConcreteVisits.
Ltac change_exec_state state :=
  match goal with |- exec ?code ?before = ?outcome => change (exec code state = outcome) end.

Lemma eliminateLiftOnly {I T V} `{EqDecision V} b nums
  (action : Action (WithArrays I T) withArraysReturnValue unit) :
  eliminateLocalVariables b nums (@liftToWithLocalVariables I T V unit action)=action.
Proof.
  rewrite <-(bind_unit_identity (liftToWithLocalVariables action)) at 1.
  rewrite eliminateLift. cbn [eliminateLocalVariables]. apply bind_unit_identity.
Qed.

Lemma eliminate_then_array {I T V} `{EqDecision V} b nums
  (code : Action (WithLocalVariables I T V) withLocalVariablesReturnValue unit)
  (action : Action (WithArrays I T) withArraysReturnValue unit) :
  eliminateLocalVariables b nums (code >>= fun _=>liftToWithLocalVariables action)=
  eliminateLocalVariables b nums code >>=fun _=>action.
Proof.
  induction code as [value|effect continuation IH] in b,nums |- *.
  - destruct value. cbn [bind eliminateLocalVariables]. apply eliminateLiftOnly.
  - destruct effect; cbn [bind].
    + rewrite !pushDispatch. cbn [bind]. apply f_equal. apply functional_extensionality. intro value. apply IH.
    + rewrite !pushBooleanGet. apply IH.
    + rewrite !pushBooleanSet. apply IH.
    + rewrite !pushNumberGet. apply IH.
    + rewrite !pushNumberSet. apply IH.
Qed.

Definition solveResultAction : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  tableRead arraydef_0__poly 0 >>= fun value=>tableWrite arraydef_0__result 0 value.

Definition solveAfterPrepBody : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve)
  withLocalVariablesReturnValue unit :=
  store _ _ _ arraydef_0__poly 0 1 >>=fun _=>
  numberLocalSet _ _ _ vardef_0__solve_length 1 >>=fun _=>
  (numberLocalGet _ _ _ vardef_0__solve_count >>=fun count=>store _ _ _ arraydef_0__frames 0 (0,count,0,0,0)) >>=fun _=>
  (addInt 64 (multInt 64 (Done _ _ _ 4) (numberLocalGet _ _ _ vardef_0__solve_count)) (Done _ _ _ 1) >>=fun visits=>
    loop (Z.to_nat visits) (solveVisitBody visits)) >>=fun _=>liftToWithLocalVariables solveResultAction.

Definition solvePhased : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve)
  withLocalVariablesReturnValue unit :=
  store _ _ _ arraydef_0__prefix 0 0 >>=fun _=>
  (subInt 64 (numberLocalGet _ _ _ vardef_0__solve_end) (numberLocalGet _ _ _ vardef_0__solve_begin) >>=fun total=>
    loop (Z.to_nat total) (solvePrepBody total)) >>=fun _=>solveAfterPrepBody.

Lemma solvePhased_exact : solvePhased=funcdef_0__solve_body.
Proof.
  rewrite <-solveCompact_exact. unfold solvePhased,solveAfterPrepBody,solveResultAction,solveCompact,
    store,retrieve,numberLocalGet,numberLocalSet,tableRead,tableWrite,liftToWithLocalVariables.
  reflexivity.
Qed.

Lemma solvePrepareNormalized b nums total : nums vardef_0__solve_end-nums vardef_0__solve_begin=Z.of_nat total ->
  Z.of_nat total<18446744073709551616 ->
  eliminateLocalVariables b nums solvePhased=
  tableWrite arraydef_0__prefix 0 0 >>=fun _=>
    eliminateLocalVariables b nums (loop total (solvePrepBody (Z.of_nat total)) >>=fun _=>solveAfterPrepBody).
Proof.
  intros difference fit. unfold solvePhased,store,numberLocalGet,subInt,tableWrite.
  normalize_table_loop. apply f_equal. apply functional_extensionality. intros [].
  normalize_table_loop. rewrite difference,coerce64_small by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma solveAfterPrepNormalized b nums count : nums vardef_0__solve_count=Z.of_nat count -> Z.of_nat count<=500000 ->
  eliminateLocalVariables b nums solveAfterPrepBody=
  tableWrite arraydef_0__poly 0 1 >>=fun _=>
  tableWrite arraydef_0__frames 0 (0,Z.of_nat count,0,0,0) >>=fun _=>
  eliminateLocalVariables b (update nums vardef_0__solve_length 1)
    (loop (4*count+1)%nat (solveVisitBody (Z.of_nat (4*count+1)))) >>=fun _=>solveResultAction.
Proof.
  intros countEq countBound. unfold solveAfterPrepBody,store,numberLocalGet,numberLocalSet,multInt,addInt,tableWrite.
  normalize_table_loop. apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  try rewrite lookupDifferent by congruence. try rewrite countEq.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  try rewrite lookupDifferent by congruence. try rewrite countEq.
  rewrite (coerce64_small (4*Z.of_nat count)) by lia.
  rewrite coerce64_small by lia.
  replace (4*Z.of_nat count+1) with (Z.of_nat (4*count+1)) by lia. rewrite Nat2Z.id.
  apply eliminate_then_array.
Qed.

Lemma eventsFrom_length_bound word height : (length (eventsFrom word height)<=length word)%nat.
Proof.
  induction word as [|opening word IH] in height |- *; [reflexivity|].
  destruct opening; cbn [eventsFrom length]; [pose proof (IH (S height)); lia|].
  destruct height as [|height]; cbn [length].
  - pose proof (IH 0%nat). lia.
  - pose proof (IH height). lia.
Qed.

Lemma framesRepresent_initial frames frame : (0<length frames)%nat ->
  framesRepresent (<[0%nat:=encodeAnnotatedFrame frame]>frames) [frame].
Proof.
  destruct frames as [|old tail]; [cbn [length]; lia|]. intro room.
  exists tail. cbn [insert list_insert]. rewrite encodeAnnotatedStack_cons.
  cbn [encodeAnnotatedStack rev map app]. reflexivity.
Qed.

Lemma active_one_initial values : nth 0 values 0=1 -> activeCoefficient values 1=pathCoefficients [0%nat].
Proof.
  intro first. apply functional_extensionality. intro index.
  destruct (Z_lt_ge_dec index 0) as [negative|nonnegative].
  - rewrite activeCoefficient_outside,pathCoefficients_negative by lia. reflexivity.
  - destruct (Z.eq_dec index 0) as [->|positive].
    + rewrite activeCoefficient_inside by lia. change (nth 0 values 0=1). exact first.
    + rewrite activeCoefficient_outside,pathCoefficients_nonnegative by lia.
      rewrite occurrences_cons. unfold indicator. destruct (Nat.eq_dec 0%nat (Z.to_nat index)) as [zero|different].
      * pose proof (Z2Nat.id index ltac:(lia)) as converted. rewrite <-zero in converted.
        change (0=index) in converted. congruence.
      * reflexivity.
Qed.

Lemma treeBuffers_initial_zero tree values : (1+length (treeEvents tree)<=length values)%nat ->
  tableCanonical values -> nth 0 values 0=1 ->
  nth 0 (fst (treeBuffers tree values 1)) 0=
    run (treeEvents tree) (pathCoefficients [0%nat]) 0 mod koxiaModulus.
Proof.
  intros room canonical first.
  pose proof (treeBuffers_correct tree values 1 room 0) as correct.
  rewrite active_one_initial in correct by exact first.
  rewrite activeCoefficient_inside in correct by (rewrite treeBuffers_active; lia).
  cbn [Z.to_nat] in correct. unfold congruent in correct.
  rewrite Z.mod_small in correct; [exact correct|].
  apply tableCanonical_nth; [apply treeBuffers_canonical; assumption|].
  rewrite treeBuffers_length. lia.
Qed.

Lemma workspace_result state n stage values : SolverWorkspace state n stage ->
  length values=length (memory state arraydef_0__result) ->
  SolverWorkspace (withArray state arraydef_0__result values) n stage.
Proof.
  intros workspace sameLength. apply workspace_transfer with (before:=state).
  - exact workspace.
  - apply withArray_lengths. exact sameLength.
  - apply withArray_preserve_other; congruence.
  - apply withArray_preserve_other; congruence.
  - apply withArray_preserve_other; congruence.
  - rewrite withArray_preserve_other by congruence. exact (workspace_work_canonical _ _ _ workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_other_canonical _ _ _ workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_roots_canonical _ _ _ workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_poly_canonical _ _ _ workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_arena_canonical _ _ _ workspace).
Qed.

Theorem generated_solve_execution b nums state word n stage : SolverWorkspace state n stage ->
  (length word<=n)%nat -> nums vardef_0__solve_end-nums vardef_0__solve_begin=Z.of_nat (length word) ->
  nums vardef_0__solve_balance=0 -> nums vardef_0__solve_minimum=0 -> nums vardef_0__solve_count=0 ->
  nums vardef_0__solve_depth=0 -> nums vardef_0__solve_top=0 ->
  prepInput state nums (b vardef_0__solve_reverse) (Z.of_nat (length word)) word ->
  exists final,
    exec (funcdef_0__solve b nums) state=Some (tt,final) /\
    nth 0 (memory final arraydef_0__result) 0=
      run (eventsFrom word 0) (pathCoefficients [0%nat]) 0 mod koxiaModulus /\
    SolverWorkspace final n stage /\ stdin final=stdin state /\ stdout final=stdout state /\
    (forall name, name<>arraydef_0__prefix -> name<>arraydef_0__poly -> name<>arraydef_0__frames ->
      name<>arraydef_0__work -> name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
      memory final name=memory state name).
Proof.
  intros workspace wordRoom difference balanceEq minimumEq countEq depthEq topEq input.
  pose proof (workspace_input_bound _ _ _ workspace) as inputBound.
  pose proof (workspace_prefix_length _ _ _ workspace) as prefixLength.
  pose (initialized := withArray state arraydef_0__prefix (<[0%nat:=0]>(memory state arraydef_0__prefix))).
  assert (initializedWorkspace : SolverWorkspace initialized n stage).
  { apply workspace_preprocess_transfer with (before:=state); [exact workspace| |].
    - unfold initialized. rewrite withArray_preserve_same,length_insert. reflexivity.
    - intros name different. apply withArray_preserve_other. exact different. }
  assert (initializedInput : prepInput initialized nums (b vardef_0__solve_reverse) (Z.of_nat (length word)) word).
  { apply prepInput_transfer with (before:=state) (nums:=nums); [exact input| |reflexivity|reflexivity].
    apply withArray_preserve_other; congruence. }
  destruct (@generated_preprocess_loop b nums (Z.of_nat (length word)) initialized word n stage
    initializedWorkspace wordRoom balanceEq minimumEq countEq
    ltac:(unfold initialized; rewrite withArray_preserve_same,nthUpdate; [reflexivity|rewrite prefixLength; lia]) initializedInput)
    as [prepared [scanned [prepExecution [preparedCount [flags [scannedWorkspace [scanInput [scanOutput [scanArrays scanNums]]]]]]]]].
  pose (events:=eventsFrom word 0).
  assert (eventsRoom : (length events<=n)%nat).
  { unfold events. pose proof (eventsFrom_length_bound word 0). lia. }
  assert (preparedDepth : prepared vardef_0__solve_depth=0).
  { rewrite scanNums by congruence. exact depthEq. }
  assert (preparedTop : prepared vardef_0__solve_top=0).
  { rewrite scanNums by congruence. exact topEq. }
  pose (values:=<[0%nat:=1]>(memory scanned arraydef_0__poly)).
  pose (polyState:=withArray scanned arraydef_0__poly values).
  assert (polyWorkspace : SolverWorkspace polyState n stage).
  { apply workspace_poly; [exact scannedWorkspace|apply length_insert|].
    unfold values,tableCanonical. apply Forall_insert; [exact (workspace_poly_canonical _ _ _ scannedWorkspace)|].
    unfold koxiaModulus. lia. }
  pose (rootState:=withArray polyState arraydef_0__frames
    (<[0%nat:=(0,Z.of_nat (length events),0,0,0)]>(memory polyState arraydef_0__frames))).
  assert (rootWorkspace : SolverWorkspace rootState n stage).
  { apply workspace_frames; [exact polyWorkspace|apply length_insert]. }
  assert (rootFrames : framesRepresent (memory rootState arraydef_0__frames) [VisitTree 0 (balancedTree 20 events)]).
  { unfold rootState. rewrite withArray_preserve_same.
    replace (0,Z.of_nat (length events),0,0,0) with (encodeAnnotatedFrame (VisitTree 0 (balancedTree 20 events))).
    - apply framesRepresent_initial. pose proof (workspace_frames_length _ _ _ polyWorkspace) as frameLength.
      change (@List.length (Z*Z*Z*Z*Z)%type (memory polyState arraydef_0__frames)=32%nat) in frameLength.
      rewrite frameLength. lia.
    - unfold encodeAnnotatedFrame. rewrite balancedTree_events. reflexivity. }
  assert (rootFlags : prefixFlags (memory rootState arraydef_0__prefix) 0 events).
  { unfold rootState,polyState. rewrite !withArray_preserve_other by congruence. exact flags. }
  destruct (@generated_root_visit_loop b (update prepared vardef_0__solve_length 1) rootState n stage events
    rootWorkspace eventsRoom rootFrames rootFlags
    ltac:(rewrite lookupDifferent by congruence; exact preparedDepth) ltac:(apply lookupSame)
    ltac:(rewrite lookupDifferent by congruence; exact preparedTop))
    as [visited [visitExecution [visitValues [visitedWorkspace [visitInput [visitOutput visitArrays]]]]]].
  pose (result:=nth 0 (memory visited arraydef_0__poly) 0).
  pose (final:=withArray visited arraydef_0__result (<[0%nat:=result]>(memory visited arraydef_0__result))).
  exists final. split.
  - unfold funcdef_0__solve. rewrite <-solvePhased_exact,solvePrepareNormalized with (total:=length word) by lia.
    rewrite tableStore_execution with (index:=0%nat) by (rewrite prefixLength; lia).
    change_exec_state initialized. rewrite (prepExecution (fun _=>solveAfterPrepBody)).
    rewrite solveAfterPrepNormalized with (count:=length events) by (try exact preparedCount; lia).
    rewrite tableStore_execution with (index:=0%nat) by (pose proof (workspace_poly_room _ _ _ scannedWorkspace); lia).
    change_exec_state polyState.
    rewrite tableStore_execution with (index:=0%nat) by (rewrite (workspace_frames_length _ _ _ polyWorkspace); lia).
    change_exec_state rootState. rewrite exec_bind,visitExecution. cbn [optionBind fst snd].
    unfold solveResultAction. rewrite exec_bind,tableRead_execution with (index:=0%nat) by
      (try congruence; pose proof (workspace_poly_room _ _ _ visitedWorkspace); lia).
    cbn [optionBind fst snd intValue]. fold result.
    pose proof (@integerWrite_execution arraydef_0__result visited (memory visited arraydef_0__result) 0 result
      ltac:(congruence) ltac:(pose proof (workspace_result_room _ _ _ visitedWorkspace) as room;
        change (2<@List.length Z (memory visited arraydef_0__result))%nat in room; lia)) as stored.
    cbn [intValue intValues] in stored. rewrite withArray_self in stored. exact stored.
  - assert (resultCorrect : result=run events (pathCoefficients [0%nat]) 0 mod koxiaModulus).
    { unfold result. change (@List.nth Z 0 (memory visited arraydef_0__poly) 0=
        run events (pathCoefficients [0%nat]) 0 mod koxiaModulus).
      rewrite visitValues. unfold rootState,polyState.
      rewrite withArray_preserve_other by congruence. rewrite withArray_preserve_same.
      rewrite <-(@balancedTree_events 20 events) at 2. apply treeBuffers_initial_zero.
      - rewrite balancedTree_events. unfold values. rewrite length_insert.
        pose proof (workspace_poly_room _ _ _ scannedWorkspace) as room.
        change (S n<=@List.length Z (memory scanned arraydef_0__poly))%nat in room. lia.
      - exact (workspace_poly_canonical _ _ _ polyWorkspace).
      - unfold values. rewrite nthUpdate; [reflexivity|].
        pose proof (workspace_poly_room _ _ _ scannedWorkspace) as room.
        change (S n<=@List.length Z (memory scanned arraydef_0__poly))%nat in room. lia. }
    split.
    + unfold final. rewrite withArray_preserve_same,nthUpdate; [exact resultCorrect|].
      pose proof (workspace_result_room _ _ _ visitedWorkspace). lia.
    + split; [apply workspace_result; [exact visitedWorkspace|apply length_insert]|].
      split.
      * unfold final. change (stdin visited=stdin state). rewrite visitInput.
        change (stdin scanned=stdin state). rewrite scanInput. reflexivity.
      * split.
        -- unfold final. change (stdout visited=stdout state). rewrite visitOutput.
           change (stdout scanned=stdout state). rewrite scanOutput. reflexivity.
        -- intros name notPrefix notPoly notFrames notWork notOther notResult notArena.
           unfold final. rewrite withArray_preserve_other by assumption. rewrite visitArrays by assumption.
           unfold rootState,polyState. rewrite !withArray_preserve_other by assumption.
           rewrite scanArrays by assumption. unfold initialized. apply withArray_preserve_other. exact notPrefix.
Qed.
