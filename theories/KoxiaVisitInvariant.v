From CoqCP Require Import Options Imperative Execution KoxiaArrays KoxiaArrayLoops KoxiaModular
  KoxiaTables KoxiaPolynomial KoxiaPolynomialBuffers KoxiaLeafRun KoxiaBufferSplit KoxiaArena KoxiaTraversal
  KoxiaCapacity KoxiaTreeBuffers KoxiaVisitSchedule KoxiaVisitMemory KoxiaVisitBounds KoxiaPrefixFlags
  KoxiaConcreteVisits KoxiaSolveProgram KoxiaConvolution KoxiaConvolutionReady KoxiaMemoryPreservation KoxiaWorkspace
  KoxiaFrameStores KoxiaLeftExecution SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Lia.
Local Opaque loop solveVisitBody funcdef_0__convolve funcdef_0__ntt.

Record VisitInvariant configuration n stage : Prop := {
  invariant_workspace : SolverWorkspace (configurationMemory configuration) n stage;
  invariant_frames : framesRepresent (memory (configurationMemory configuration) arraydef_0__frames)
    (configurationStack configuration);
  invariant_structure : stackStructure (memory (configurationMemory configuration) arraydef_0__prefix)
    n (configurationStack configuration);
  invariant_poly_room : stackPolyRoom (S n) (configurationStack configuration) (configurationLength configuration);
  invariant_arena_room : stackArenaRoom (4*n+128) (configurationStack configuration)
    (configurationLength configuration) (configurationTop configuration);
  invariant_arena_layout : stackArenaLayout (memory (configurationMemory configuration) arraydef_0__arena)
    (configurationStack configuration) (configurationTop configuration)
}.

Theorem invariant_visit_ready configuration n stage : VisitInvariant configuration n stage -> visitReady configuration.
Proof.
  destruct configuration as [stack state len top]. intros [workspace frames structure polyRoom arenaRoom layout].
  cbv beta iota zeta delta [visitReady configurationMemory configurationValues configurationLength configurationTop configurationStack].
  split; [exact frames|]. destruct stack as [|frame stack]; [exact I|].
  cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack]
    in workspace,frames,structure,polyRoom,arenaRoom,layout.
  pose proof (workspace_input_bound _ _ _ workspace) as inputBound.
  pose proof (workspace_poly_room _ _ _ workspace) as bufferRoom.
  pose proof (workspace_poly_canonical _ _ _ workspace) as canonical.
  pose proof (workspace_prefix_length _ _ _ workspace) as prefixLength.
  pose proof (workspace_frames_length _ _ _ workspace) as framesLength.
  pose proof (workspace_arena_length _ _ _ workspace) as arenaLength.
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
  - destruct tree as [events|leftTree rightTree].
    + cbn [stackStructure frameStructure wellSplit treeEvents treeHeight stackPolyRoom] in structure,polyRoom.
      destruct structure as [[small [interval [flags height]]] outer]. destruct polyRoom as [room restRoom].
      repeat split; try assumption; try lia.
      * unfold koxiaModulus. lia.
    + cbn [stackStructure frameStructure wellSplit treeEvents treeHeight stackPolyRoom stackArenaRoom arenaNeed] in structure,polyRoom,arenaRoom.
      destruct structure as [[[large [half [leftSplit rightSplit]]] [interval [flags height]]] outer].
      destruct polyRoom as [room restRoom]. destruct arenaRoom as [topRoom [allocationRoom restArena]].
      split; [exact large|]. split; [rewrite interval_middle,<-half; reflexivity|].
      split; [lia|]. split; [apply prefixFlags_difference; exact flags|].
      split; [apply specialCount_bound|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros present. apply workspace_convolution_ready with (n:=n) (stage:=stage); try assumption; try lia.
      unfold savedLength in allocationRoom. rewrite (proj2 (Nat.ltb_lt _ _) present) in allocationRoom. lia.
  - cbn [stackStructure frameStructure] in structure. destruct structure as [[split [interval [middleEq [endEq [flags height]]]]] outer].
    repeat split; try assumption; try lia.
  - cbn [stackStructure frameStructure stackPolyRoom stackArenaLayout] in structure,polyRoom,layout.
    destruct structure as [[interval height] outer]. destruct polyRoom as [room restRoom].
    destruct layout as [topEq [savedLengthEq [contains restLayout]]].
    cbn [stackArenaRoom] in arenaRoom. destruct arenaRoom as [topRoom restArena].
    repeat split; try assumption; try lia.
    exact (workspace_arena_canonical _ _ _ workspace).
Qed.

Lemma leaf_invariant_next state len top start events stack n stage :
  VisitInvariant {|configurationStack:=VisitTree start (Leaf events)::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|} n stage ->
  VisitInvariant (nextVisit {|configurationStack:=VisitTree start (Leaf events)::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|}) n stage.
Proof.
  intros [workspace frames structure polyRoom arenaRoom layout].
  cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack]
    in workspace,frames,structure,polyRoom,arenaRoom,layout.
  cbn [stackPolyRoom treeEvents] in polyRoom. destruct polyRoom as [room restRoom].
  pose proof (workspace_poly_room _ _ _ workspace) as bufferRoom.
  pose proof (workspace_poly_canonical _ _ _ workspace) as canonical.
  cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop configurationStack].
  constructor; cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack].
  - apply workspace_poly; [exact workspace|apply runBuffers_length|].
    apply runBuffers_canonical; [exact (Nat.le_trans _ _ _ room bufferRoom)|exact canonical].
  - rewrite withArray_preserve_other by congruence. apply framesRepresent_pop with (frame:=VisitTree start (Leaf events)). exact frames.
  - rewrite withArray_preserve_other by congruence. exact (proj2 structure).
  - rewrite runBuffers_active. exact restRoom.
  - cbn [stackArenaRoom treeEvents] in arenaRoom. rewrite runBuffers_active. exact (proj2 (proj2 arenaRoom)).
  - rewrite withArray_preserve_other by congruence. exact layout.
Qed.

Lemma branch_invariant_next state len top start leftTree rightTree stack n stage :
  VisitInvariant {|configurationStack:=VisitTree start (Branch leftTree rightTree)::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|} n stage ->
  VisitInvariant (nextVisit {|configurationStack:=VisitTree start (Branch leftTree rightTree)::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|}) n stage.
Proof.
  intro invariant. pose proof (invariant_visit_ready _ _ _ invariant) as ready.
  destruct invariant as [workspace frames structure polyRoom arenaRoom layout].
  cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack]
    in workspace,frames,structure,polyRoom,arenaRoom,layout.
  cbv beta iota zeta delta [visitReady configurationMemory configurationValues configurationLength configurationTop configurationStack] in ready.
  destruct ready as [represented [large [middleEq [prefixRoom [difference [cutBound [addressFit [arenaFit [depthFit [childRoom convolutionReady]]]]]]]]]].
  cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop configurationStack].
  constructor; cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack].
  - apply workspace_storedChildFrames,workspace_leftSavedState; assumption.
  - unfold storedChildFrames. rewrite withArray_preserve_same.
    rewrite leftSavedState_preserves by congruence.
    replace (Z.of_nat start,Z.of_nat (start+length (treeEvents leftTree++treeEvents rightTree)),1%Z,Z.of_nat top,
      Z.of_nat (savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
        (length (treeEvents leftTree++treeEvents rightTree)))) with
      (encodeAnnotatedFrame (VisitRight start (start+length (treeEvents leftTree))
        (length (treeEvents leftTree++treeEvents rightTree)) rightTree
        (savedBuffer (memory state arraydef_0__poly) len (specialCount (treeEvents leftTree++treeEvents rightTree))
          (length (treeEvents leftTree++treeEvents rightTree)))
        (savedLength len (specialCount (treeEvents leftTree++treeEvents rightTree))
          (length (treeEvents leftTree++treeEvents rightTree))) top)) by reflexivity.
    replace (Z.of_nat start,Z.of_nat (start+length (treeEvents leftTree)),0%Z,0%Z,0%Z) with
      (encodeAnnotatedFrame (VisitTree start leftTree)) by reflexivity.
    apply framesRepresent_push with (old:=VisitTree start (Branch leftTree rightTree)); assumption.
  - rewrite storedChildFrames_preserves,leftSavedState_preserves by congruence.
    apply stackStructure_branch. exact structure.
  - apply stackPolyRoom_branch. exact polyRoom.
  - apply stackArenaRoom_branch. exact arenaRoom.
  - rewrite storedChildFrames_preserves by congruence.
    cbn [stackArenaLayout]. split; [reflexivity|]. split; [symmetry; apply savedBuffer_length|]. split.
    + pose proof (@leftSavedState_contains state (memory state arraydef_0__poly) len
        (specialCount (treeEvents leftTree++treeEvents rightTree))
        (length (treeEvents leftTree++treeEvents rightTree)) top
        ltac:(rewrite withArray_self; exact convolutionReady)) as contains.
      rewrite withArray_self in contains. exact contains.
    + apply stackArenaLayout_transfer with (before:=memory state arraydef_0__arena); [exact layout|].
      intros index below. apply leftSavedState_arena_prefix; assumption.
Qed.

Lemma right_invariant_next state len top start middle span tree saved savedLen base stack n stage :
  VisitInvariant {|configurationStack:=VisitRight start middle span tree saved savedLen base::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|} n stage ->
  VisitInvariant (nextVisit {|configurationStack:=VisitRight start middle span tree saved savedLen base::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|}) n stage.
Proof.
  intros [workspace frames structure polyRoom arenaRoom layout].
  cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack]
    in workspace,frames,structure,polyRoom,arenaRoom,layout.
  cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop configurationStack].
  cbn [stackStructure frameStructure] in structure.
  destruct structure as [[split [interval [middleEq [endEq [flags height]]]]] outer].
  constructor; cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack].
  - apply workspace_frames; [exact workspace|rewrite !length_insert; reflexivity].
  - rewrite withArray_preserve_same. apply framesRepresent_push with
      (old:=VisitRight start middle span tree saved savedLen base); [exact frames|].
    pose proof (workspace_frames_length _ _ _ workspace) as frameLength.
    change (@List.length (Z*Z*Z*Z*Z)%type (memory state arraydef_0__frames)=32) in frameLength.
    rewrite frameLength. lia.
  - rewrite withArray_preserve_other by congruence.
    cbn [stackStructure frameStructure length]. repeat split; try assumption; lia.
  - cbn [stackPolyRoom] in polyRoom |- *. destruct polyRoom as [room restRoom].
    split; [exact room|]. split; [|exact restRoom].
    apply stackPolyRoom_current with (stack:=stack). exact restRoom.
  - cbn [stackArenaRoom] in arenaRoom |- *. destruct arenaRoom as [topRoom [needed restArena]].
    split; [exact topRoom|]. split; [exact needed|]. split; [exact topRoom|exact restArena].
  - rewrite withArray_preserve_other by congruence. exact layout.
Qed.

Lemma merge_invariant_next state len top start span saved savedLen base stack n stage :
  VisitInvariant {|configurationStack:=VisitMerge start span saved savedLen base::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|} n stage ->
  VisitInvariant (nextVisit {|configurationStack:=VisitMerge start span saved savedLen base::stack;
    configurationMemory:=state;configurationLength:=len;configurationTop:=top|}) n stage.
Proof.
  intros [workspace frames structure polyRoom arenaRoom layout].
  cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack]
    in workspace,frames,structure,polyRoom,arenaRoom,layout.
  cbv beta iota zeta delta [nextVisit configurationMemory configurationValues configurationLength configurationTop configurationStack].
  constructor; cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack].
  - apply workspace_poly; [exact workspace|apply mergeBuffer_length|apply mergeBuffer_canonical].
    exact (workspace_poly_canonical _ _ _ workspace).
  - rewrite withArray_preserve_other by congruence.
    apply framesRepresent_pop with (frame:=VisitMerge start span saved savedLen base). exact frames.
  - rewrite withArray_preserve_other by congruence. exact (proj2 structure).
  - exact (proj2 polyRoom).
  - exact (proj2 arenaRoom).
  - rewrite withArray_preserve_other by congruence. exact (proj2 (proj2 (proj2 layout))).
Qed.

Theorem invariant_next_visit configuration n stage : VisitInvariant configuration n stage ->
  VisitInvariant (nextVisit configuration) n stage.
Proof.
  destruct configuration as [stack state len top]. destruct stack as [|frame stack]; [exact (fun hypothesis=>hypothesis)|].
  destruct frame as [start tree|start middle span tree saved savedLen base|start span saved savedLen base].
  - destruct tree; [apply leaf_invariant_next|apply branch_invariant_next].
  - apply right_invariant_next.
  - apply merge_invariant_next.
Qed.

Theorem invariant_safe_visits fuel configuration n stage : VisitInvariant configuration n stage ->
  safeConcreteVisits fuel configuration.
Proof.
  induction fuel as [|fuel IH] in configuration |- *; [intros; exact I|].
  intro invariant. cbn [safeConcreteVisits]. destruct (configurationStack configuration); [exact I|].
  split; [apply invariant_visit_ready with (n:=n) (stage:=stage); exact invariant|].
  apply IH,invariant_next_visit. exact invariant.
Qed.

Theorem root_visit_invariant state n stage events : SolverWorkspace state n stage ->
  length events<=n ->
  framesRepresent (memory state arraydef_0__frames) [VisitTree 0 (balancedTree 20 events)] ->
  prefixFlags (memory state arraydef_0__prefix) 0 events ->
  VisitInvariant {|configurationStack:=[VisitTree 0 (balancedTree 20 events)];configurationMemory:=state;
    configurationLength:=1;configurationTop:=0|} n stage.
Proof.
  intros workspace eventsBound frames flags.
  pose proof (workspace_input_bound _ _ _ workspace) as inputBound.
  destruct (balancedTree_root_bounds events n ltac:(lia) ltac:(lia)) as [small [height [visits arena]]].
  constructor; cbv beta iota zeta delta [configurationMemory configurationValues configurationLength configurationTop configurationStack].
  - exact workspace.
  - exact frames.
  - cbn [stackStructure frameStructure length]. rewrite balancedTree_events.
    repeat split; try assumption. apply balancedTree_wellSplit. exact small.
  - cbn [stackPolyRoom]. rewrite balancedTree_events. pose proof (ordinaryCount_bound events). lia.
  - cbn [stackArenaRoom]. repeat split; try lia; exact I.
  - exact I.
Qed.

Theorem invariant_run_visits fuel configuration n stage : VisitInvariant configuration n stage ->
  VisitInvariant (runConcreteVisits fuel configuration) n stage.
Proof.
  induction fuel as [|fuel IH] in configuration |- *; [exact (fun hypothesis=>hypothesis)|].
  intro invariant. cbn [runConcreteVisits]. destruct (configurationStack configuration); [exact invariant|].
  apply IH,invariant_next_visit. exact invariant.
Qed.

Local Opaque balancedTree treeBuffers runConcreteVisits.
Theorem generated_root_visit_loop b nums state n stage events : SolverWorkspace state n stage ->
  length events<=n ->
  framesRepresent (memory state arraydef_0__frames) [VisitTree 0 (balancedTree 20 events)] ->
  prefixFlags (memory state arraydef_0__prefix) 0 events ->
  nums vardef_0__solve_depth=0%Z -> nums vardef_0__solve_length=1%Z -> nums vardef_0__solve_top=0%Z ->
  exists final,
    exec (eliminateLocalVariables b nums
      (loop (4*length events+1) (solveVisitBody (Z.of_nat (4*length events+1))))) state=Some (tt,final) /\
    memory final arraydef_0__poly=fst (treeBuffers (balancedTree 20 events) (memory state arraydef_0__poly) 1) /\
    SolverWorkspace final n stage /\ stdin final=stdin state /\ stdout final=stdout state /\
    (forall name, name<>arraydef_0__poly -> name<>arraydef_0__frames -> name<>arraydef_0__work ->
      name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
      memory final name=memory state name).
Proof.
  intros workspace eventsBound frames flags depthEq lenEq topEq.
  pose (configuration := {|configurationStack:=[VisitTree 0 (balancedTree 20 events)];configurationMemory:=state;
    configurationLength:=1;configurationTop:=0|}).
  assert (invariant : VisitInvariant configuration n stage).
  { apply root_visit_invariant; assumption. }
  assert (locals : configurationLocals nums configuration).
  { repeat split; assumption. }
  destruct (@generated_visit_loop_execution b nums (Z.of_nat (4*length events+1)) (4*length events+1)
    configuration (fun _=>Done _ _ _ tt) ltac:(left; discriminate)
    (invariant_safe_visits _ _ _ _ invariant) locals) as [finished [execution finalLocals]].
  rewrite bind_unit_identity in execution.
  change (exec (eliminateLocalVariables b nums
      (loop (4*length events+1) (solveVisitBody (Z.of_nat (4*length events+1))))) state=
    Some (tt,configurationMemory (runConcreteVisits (4*length events+1) configuration))) in execution.
  exists (configurationMemory (runConcreteVisits (4*length events+1) configuration)).
  split; [exact execution|].
  pose proof (runConcreteVisits_abstract (4*length events+1) configuration) as abstract.
  cbv beta iota zeta delta [configuration configurationStack configurationValues configurationMemory
    configurationLength configurationTop] in abstract.
  rewrite annotatedVisit_balanced_complete in abstract.
  split.
  - change (fst (fst (snd (abstractConfiguration (runConcreteVisits (4*length events+1) configuration))))=
      fst (treeBuffers (balancedTree 20 events) (memory state arraydef_0__poly) 1)).
    unfold configuration. rewrite abstract. cbv beta iota zeta delta [fst snd]. reflexivity.
  - split; [exact (invariant_workspace _ _ _ (invariant_run_visits _ _ _ _ invariant))|].
    destruct (runConcreteVisits_io (4*length events+1) configuration) as [input output].
    split; [exact input|]. split; [exact output|].
    intros name. apply runConcreteVisits_preserves.
Qed.
