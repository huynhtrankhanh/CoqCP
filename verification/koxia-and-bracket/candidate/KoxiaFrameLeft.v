From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaArrays KoxiaTables KoxiaTableLoops KoxiaConvolutionProgram KoxiaFrames.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve.
Ltac normalize_frame_updates := repeat first [rewrite lookupSame | rewrite lookupDifferent by congruence].
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition leftSmall (nums : varsfuncdef_0__solve -> Z) cut :=
  if bool_decide (nums vardef_0__solve_length<cut) then nums vardef_0__solve_length else cut.
Definition leftHigh (nums : varsfuncdef_0__solve -> Z) cut :=
  if bool_decide (cut<nums vardef_0__solve_length) then
    coerceInt (coerceInt (coerceInt (nums vardef_0__solve_length-cut) 64+nums vardef_0__solve_r) 64-
      nums vardef_0__solve_l) 64 else 0.
Definition leftPreparedNums (nums : varsfuncdef_0__solve -> Z) cut :=
  update (update (update nums vardef_0__solve_special cut) vardef_0__solve_small (leftSmall nums cut))
    vardef_0__solve_hi (leftHigh nums cut).
Definition leftFinishedNums (nums : varsfuncdef_0__solve -> Z) cut :=
  update (update (update (leftPreparedNums nums cut) vardef_0__solve_top
    (coerceInt (nums vardef_0__solve_top+leftHigh nums cut) 64))
    vardef_0__solve_length (leftSmall nums cut)) vardef_0__solve_depth
    (coerceInt (nums vardef_0__solve_depth+1) 64).
Definition leftConvolveCall (nums : varsfuncdef_0__solve -> Z) cut :=
  funcdef_0__convolve (fun _=>false)
    (update (update (update (update (fun _=>0) vardef_0__convolve_skip cut)
      vardef_0__convolve_length (nums vardef_0__solve_length))
      vardef_0__convolve_span (coerceInt (nums vardef_0__solve_r-nums vardef_0__solve_l) 64))
      vardef_0__convolve_base (nums vardef_0__solve_top)).
Definition leftBranchAction nums :=
  tableRead arraydef_0__prefix (nums vardef_0__solve_r) >>= fun last =>
  tableRead arraydef_0__prefix (nums vardef_0__solve_l) >>= fun first =>
  let cut := coerceInt (last-first) 64 in
  (if bool_decide (cut<nums vardef_0__solve_length) then leftConvolveCall nums cut else Done _ _ _ tt) >>= fun _ =>
  tableWrite arraydef_0__frames (nums vardef_0__solve_depth)
    (nums vardef_0__solve_l,nums vardef_0__solve_r,1,nums vardef_0__solve_top,leftHigh nums cut) >>= fun _ =>
  tableWrite arraydef_0__frames (coerceInt (nums vardef_0__solve_depth+1) 64)
    (nums vardef_0__solve_l,nums vardef_0__solve_middle,0,0,0) >>= fun _ =>
  Done _ _ _ (leftFinishedNums nums cut).
Lemma phaseLeftNormalized b nums start span continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=0 -> (32<span)%nat ->
  Z.of_nat (start+start+span)<18446744073709551616 ->
  eliminateLocalVariables b nums (solvePhaseBody >>= continuation)=
  leftBranchAction (update nums vardef_0__solve_middle (Z.of_nat ((start+start+span)/2))) >>= fun final =>
  eliminateLocalVariables b final (continuation KeepGoing).
Proof.
  intros leftEq rightEq phaseEq large addressFit.
  unfold solvePhaseBody,numberLocalGet,numberLocalSet,addInt,subInt,divIntUnsigned,retrieve,store.
  normalize_table_loop. try rewrite leftEq; try try rewrite rightEq.
  rewrite (coerce64_small (Z.of_nat start+Z.of_nat (start+span))) by lia.
  replace ((Z.of_nat start+Z.of_nat (start+span))/2) with (Z.of_nat ((start+start+span)/2))
    by (rewrite Nat2Z.inj_div; f_equal; lia).
  rewrite lookupDifferent by congruence. rewrite phaseEq.
  rewrite bool_decide_true by reflexivity. normalize_table_loop.
  normalize_frame_updates. try rewrite leftEq; try try rewrite rightEq.
  rewrite (coerce64_small (Z.of_nat (start+span)-Z.of_nat start)) by lia.
  replace (Z.of_nat (start+span)-Z.of_nat start) with (Z.of_nat span) by lia.
  rewrite bool_decide_false by lia. normalize_table_loop.
  unfold leftBranchAction,tableRead,tableWrite. cbn [bind].
  normalize_frame_updates. try rewrite leftEq; try try rewrite rightEq.
  apply f_equal. apply functional_extensionality. intro last. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite leftEq.
  apply f_equal. apply functional_extensionality. intro first. normalize_table_loop.
  cbn [withLocalVariablesReturnValue withArraysReturnValue arrayType environment1] in *.
  try rewrite !lookupSame. normalize_frame_updates.
  unfold leftFinishedNums,leftPreparedNums,leftSmall,leftHigh,leftConvolveCall.
  normalize_frame_updates.
  destruct (bool_decide (nums vardef_0__solve_length<coerceInt (last-first) 64)) eqn:lowSmall;
    normalize_table_loop; normalize_frame_updates; rewrite ?lookupSame;
    destruct (bool_decide (coerceInt (last-first) 64<nums vardef_0__solve_length)) eqn:highPresent;
    normalize_table_loop; normalize_frame_updates; rewrite ?lookupSame.
  all: try (exfalso; apply bool_decide_eq_true in lowSmall; apply bool_decide_eq_true in highPresent; lia).
  all: try rewrite leftEq; try rewrite rightEq; try rewrite <-!bindAssoc.
  all: try rewrite eliminateLift; try rewrite <-!bindAssoc.
  all: repeat (apply f_equal; apply functional_extensionality; intros []).
  all: normalize_table_loop; normalize_frame_updates; try rewrite !lookupSame; rewrite ?updateSame.
  all: try rewrite leftEq; try rewrite rightEq.
  all: repeat (apply f_equal; apply functional_extensionality; intros []).
  all: normalize_table_loop; normalize_frame_updates; try rewrite leftEq; try rewrite rightEq; rewrite ?updateSame.
  all: reflexivity.
Qed.
