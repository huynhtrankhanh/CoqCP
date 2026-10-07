From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaRoots KoxiaFourier KoxiaBinomial KoxiaSizes KoxiaCapacity KoxiaNTTCorrect KoxiaArrays KoxiaArrayLoops KoxiaTables KoxiaConvolution KoxiaConvolutionReady KoxiaMemoryPreservation KoxiaConvolutionExecution.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Local Opaque stageRoot stageInverse modularPower.
Record SolverWorkspace (state : @Machine arrayIndex1 (arrayType _ environment1)) n stage : Prop := {
  workspace_input_bound : 1<=Z.of_nat n<=500000;
  workspace_stage_bound : (stage<=20)%nat;
  workspace_transform_capacity : 2*Z.of_nat n+1<=stageSize stage;
  workspace_work_room : (sizeNat stage<=length (memory state arraydef_0__work))%nat;
  workspace_other_room : (sizeNat stage<=length (memory state arraydef_0__other))%nat;
  workspace_roots_room : (sizeNat stage<=length (memory state arraydef_0__roots))%nat;
  workspace_work_bound : Z.of_nat (length (memory state arraydef_0__work))<=1048576;
  workspace_roots_bound : Z.of_nat (length (memory state arraydef_0__roots))<=1048576;
  workspace_poly_room : (S n<=length (memory state arraydef_0__poly))%nat;
  workspace_arena_length : length (memory state arraydef_0__arena)=(4*n+128)%nat;
  workspace_frames_length : length (memory state arraydef_0__frames)=32%nat;
  workspace_prefix_length : length (memory state arraydef_0__prefix)=S n;
  workspace_factorial_room : (n<length (memory state arraydef_0__factorial))%nat;
  workspace_inverse_room : (n<length (memory state arraydef_0__inverseFactorial))%nat;
  workspace_factorial_correct : forall i, (i<=n)%nat -> nth i (memory state arraydef_0__factorial) 0=factorialMod i;
  workspace_inverse_correct : forall i, (i<=n)%nat -> nth i (memory state arraydef_0__inverseFactorial) 0=inverseFactorialMod i;
  workspace_work_canonical : tableCanonical (memory state arraydef_0__work);
  workspace_other_canonical : tableCanonical (memory state arraydef_0__other);
  workspace_roots_canonical : tableCanonical (memory state arraydef_0__roots);
  workspace_poly_canonical : tableCanonical (memory state arraydef_0__poly);
  workspace_arena_canonical : tableCanonical (memory state arraydef_0__arena);
  workspace_result_room : (2<length (memory state arraydef_0__result))%nat;
  workspace_roots_correct : forall step, (step<stage)%nat -> rootTableCorrect (memory state arraydef_0__roots) step
}.
Theorem workspace_convolution_ready state n stage len cut span base : SolverWorkspace state n stage ->
  (len+span<=S n)%nat -> (span<=n)%nat -> (cut<len)%nat ->
  (base+(len-cut+span)<=length (memory state arraydef_0__arena))%nat ->
  ConvolutionReady state len cut span base.
Proof.
  intros workspace nodeRoom spanBound highPresent arenaRoom.
  destruct workspace as [inputBound stageBound capacity workRoom otherRoom rootsRoom workBound rootsBound polyRoom
    arenaLength framesLength prefixLength factRoom inverseRoom factorial inverse workCanonical otherCanonical rootsCanonical
    polyCanonical arenaCanonical resultRoom rootsCorrect].
  assert (countBound : 1<=Z.of_nat (len-cut+span)<=1048576) by lia.
  assert (transformCap : (ceilingStage 20 (Z.of_nat (len-cut+span)) 0<=stage)%nat).
  { apply ceilingStage_cap; [lia|lia|lia]. }
  assert (sizeCap : (sizeNat (ceilingStage 20 (Z.of_nat (len-cut+span)) 0)<=sizeNat stage)%nat).
  { apply Nat2Z.inj_le. rewrite <-!stageSize_nat. apply stageSize_monotone. exact transformCap. }
  constructor; try assumption; try lia.
  - unfold koxiaModulus. lia.
  - apply factorial. exact spanBound.
  - intros i range. apply inverse. lia.
  - intros step range. apply rootsCorrect. lia.
Qed.
Theorem workspace_transfer before after n stage : SolverWorkspace before n stage ->
  (forall name, length (memory after name)=length (memory before name)) ->
  memory after arraydef_0__roots=memory before arraydef_0__roots ->
  memory after arraydef_0__factorial=memory before arraydef_0__factorial ->
  memory after arraydef_0__inverseFactorial=memory before arraydef_0__inverseFactorial ->
  tableCanonical (memory after arraydef_0__work) -> tableCanonical (memory after arraydef_0__other) ->
  tableCanonical (memory after arraydef_0__roots) -> tableCanonical (memory after arraydef_0__poly) ->
  tableCanonical (memory after arraydef_0__arena) -> SolverWorkspace after n stage.
Proof.
  intros workspace lengths sameRoots sameFactorial sameInverse workCanonical otherCanonical rootsCanonical polyCanonical arenaCanonical.
  destruct workspace. constructor.
  all: try rewrite lengths; try rewrite sameRoots; try rewrite sameFactorial; try rewrite sameInverse; assumption.
Qed.
Theorem workspace_frames state n stage frames : SolverWorkspace state n stage ->
  length frames=length (memory state arraydef_0__frames) ->
  SolverWorkspace (withArray state arraydef_0__frames frames) n stage.
Proof.
  intros workspace sameLength. apply workspace_transfer with (before:=state); [exact workspace| | | | | | | | |].
  - apply withArray_lengths. exact sameLength.
  - apply withArray_preserve_other; congruence.
  - apply withArray_preserve_other; congruence.
  - apply withArray_preserve_other; congruence.
  - rewrite withArray_preserve_other by congruence. exact (workspace_work_canonical state n stage workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_other_canonical state n stage workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_roots_canonical state n stage workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_poly_canonical state n stage workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_arena_canonical state n stage workspace).
Qed.
Theorem workspace_poly state n stage values : SolverWorkspace state n stage ->
  length values=length (memory state arraydef_0__poly) -> tableCanonical values ->
  SolverWorkspace (withArray state arraydef_0__poly values) n stage.
Proof.
  intros workspace sameLength canonical. apply workspace_transfer with (before:=state); [exact workspace| | | | | | | | |].
  - apply withArray_lengths. exact sameLength.
  - apply withArray_preserve_other; congruence.
  - apply withArray_preserve_other; congruence.
  - apply withArray_preserve_other; congruence.
  - rewrite withArray_preserve_other by congruence. exact (workspace_work_canonical state n stage workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_other_canonical state n stage workspace).
  - rewrite withArray_preserve_other by congruence. exact (workspace_roots_canonical state n stage workspace).
  - rewrite withArray_preserve_same. exact canonical.
  - rewrite withArray_preserve_other by congruence. exact (workspace_arena_canonical state n stage workspace).
Qed.
Theorem workspace_convolution state n stage len cut span base : SolverWorkspace state n stage ->
  ConvolutionReady state len cut span base -> SolverWorkspace (readyConvolutionFinal state len cut span base) n stage.
Proof.
  intros workspace ready. destruct (readyConvolution_canonical state len cut span base ready
    (workspace_arena_canonical state n stage workspace)) as [workCanonical [otherCanonical arenaCanonical]].
  apply workspace_transfer with (before:=state); try assumption.
  - intro name. unfold readyConvolutionFinal. apply convolutionFinal_lengths.
  - apply readyConvolution_preserves; congruence.
  - apply readyConvolution_preserves; congruence.
  - apply readyConvolution_preserves; congruence.
  - rewrite readyConvolution_preserves by congruence. exact (workspace_roots_canonical state n stage workspace).
  - rewrite readyConvolution_preserves by congruence. exact (workspace_poly_canonical state n stage workspace).
Qed.
