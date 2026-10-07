From CoqCP Require Import Options Imperative Execution KoxiaIntegers KoxiaArrays KoxiaTables KoxiaTableLoops
  KoxiaSolveProgram KoxiaLeafEvents KoxiaMerge SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition solvePhaseBody : Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
dropWithinLoop ((
(liftToWithinLoop ((divIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r))) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle) x)) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_phase)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    ((liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun a => (Done _ _ _ 33%Z) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
      (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun x => loop (Z.to_nat x) (leafEventBody x))) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
        (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      (liftToWithinLoop ((subInt 64 ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((subInt 64 (addInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r))) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi) x)) >>=
        fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_special)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun preset1 => (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l))) >>= fun preset2 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top)) >>= fun preset3 => (((((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_skip) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_length) preset1)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_span) preset2)) >>= fun x => Done _ _ _ (update x (vardef_0__convolve_base) preset3)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__convolve y x))) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun tuple_element_1 => ((Done _ _ _ 1%Z) >>= fun tuple_element_2 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top)) >>= fun tuple_element_3 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi)) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_hi))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_small)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  ) else (
    ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_phase)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun tuple_element_1 => ((Done _ _ _ 2%Z) >>= fun tuple_element_2 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base)) >>= fun tuple_element_3 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle)) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
        (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size) x)) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size)) >>= fun x => loop (Z.to_nat x) (mergeCoefficientBody x))) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_size)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x)) >>=
      fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_top) x)) >>=
      fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
        (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) >>=
        fun _ => Done _ _ _ tt
      ) else (
        Done _ _ _ tt
      )) >>=
      fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth) x)) >>=
      fun _ => Done _ _ _ tt
    )) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)).

Definition loadedNums (nums : varsfuncdef_0__solve -> Z) (frame : Z*Z*Z*Z*Z) :=
  update (update (update (update (update nums vardef_0__solve_l (fst (fst (fst (fst frame)))))
    vardef_0__solve_r (snd (fst (fst (fst frame)))))
    vardef_0__solve_phase (snd (fst (fst frame))))
    vardef_0__solve_base (snd (fst frame))) vardef_0__solve_saved (snd frame).
Lemma generated_frame_load b nums state visits remaining depth continuation :
  nums vardef_0__solve_depth=Z.of_nat depth ->
  (depth<length (memory state arraydef_0__frames))%nat ->
  exec (eliminateLocalVariables b nums (solveVisitBody visits remaining >>= continuation)) state=
  exec (eliminateLocalVariables b (loadedNums nums
    (nth depth (memory state arraydef_0__frames) (0,0,0,0,0)))
    (solvePhaseBody >>= continuation)) state.
Proof.
  intros depthEq room.
  unfold solveVisitBody,numberLocalGet,numberLocalSet,retrieve.
  normalize_table_loop. rewrite depthEq.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    state arraydef_0__frames depth (0,0,0,0,0)) by exact room.
  normalize_table_loop. rewrite lookupDifferent by congruence. rewrite depthEq.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    state arraydef_0__frames depth (0,0,0,0,0)) by exact room.
  normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite depthEq.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    state arraydef_0__frames depth (0,0,0,0,0)) by exact room.
  normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite depthEq.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    state arraydef_0__frames depth (0,0,0,0,0)) by exact room.
  normalize_table_loop. rewrite !lookupDifferent by congruence. rewrite depthEq.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    state arraydef_0__frames depth (0,0,0,0,0)) by exact room.
  unfold loadedNums,solvePhaseBody,numberLocalGet,numberLocalSet,retrieve. normalize_table_loop. reflexivity.
Qed.
Lemma loadedNums_other nums frame name : name<>vardef_0__solve_l -> name<>vardef_0__solve_r ->
  name<>vardef_0__solve_phase -> name<>vardef_0__solve_base -> name<>vardef_0__solve_saved ->
  loadedNums nums frame name=nums name.
Proof. intros. unfold loadedNums. rewrite !lookupDifferent by congruence. reflexivity. Qed.
Lemma loadedNums_fields nums l r phase base saved :
  loadedNums nums (l,r,phase,base,saved) vardef_0__solve_l=l /\
  loadedNums nums (l,r,phase,base,saved) vardef_0__solve_r=r /\
  loadedNums nums (l,r,phase,base,saved) vardef_0__solve_phase=phase /\
  loadedNums nums (l,r,phase,base,saved) vardef_0__solve_base=base /\
  loadedNums nums (l,r,phase,base,saved) vardef_0__solve_saved=saved.
Proof. unfold loadedNums. cbn [fst snd]. rewrite !lookupDifferent by congruence. rewrite !lookupSame. tauto. Qed.

Definition popFrameBody : Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
  dropWithinLoop
    ((liftToWithinLoop (numberLocalGet _ _ _ vardef_0__solve_depth >>= fun depth => Done _ _ _ (bool_decide (depth=0))) >>= fun zero =>
      (if zero then break _ _ _ >>= fun _ => Done _ _ _ tt else Done _ _ _ tt) >>= fun _ =>
      liftToWithinLoop (subInt 64 (numberLocalGet _ _ _ vardef_0__solve_depth) (Done _ _ _ 1) >>= fun depth =>
        numberLocalSet _ _ _ vardef_0__solve_depth depth) >>= fun _ => Done _ _ _ tt)).
Lemma popFrameNormalized b nums depth continuation :
  nums vardef_0__solve_depth=Z.of_nat depth -> Z.of_nat depth<18446744073709551616 ->
  eliminateLocalVariables b nums (popFrameBody >>= continuation)=
  if Nat.eqb depth 0 then eliminateLocalVariables b nums (continuation Stop)
  else eliminateLocalVariables b (update nums vardef_0__solve_depth (Z.of_nat (depth-1))) (continuation KeepGoing).
Proof.
  intros depthEq depthBound. unfold popFrameBody,numberLocalGet,numberLocalSet,subInt.
  normalize_table_loop. rewrite depthEq.
  assert (zeroGuard : bool_decide (Z.of_nat depth=0)=Nat.eqb depth 0).
  { destruct (Nat.eqb depth 0) eqn:zero.
    - apply Nat.eqb_eq in zero. rewrite bool_decide_true by lia. reflexivity.
    - apply Nat.eqb_neq in zero. rewrite bool_decide_false by lia. reflexivity. }
  cbn [withLocalVariablesReturnValue withArraysReturnValue] in *.
  rewrite zeroGuard. destruct (Nat.eqb depth 0) eqn:zero; normalize_table_loop; [reflexivity|].
  rewrite depthEq. apply Nat.eqb_neq in zero. rewrite coerce64_small by lia.
  replace (Z.of_nat depth-1) with (Z.of_nat (depth-1)) by lia. reflexivity.
Qed.
Lemma phaseLeafNormalized b nums start span continuation :
  nums vardef_0__solve_l=Z.of_nat start -> nums vardef_0__solve_r=Z.of_nat (start+span) ->
  nums vardef_0__solve_phase=0 -> (span<=32)%nat ->
  Z.of_nat (start+start+span)<18446744073709551616 ->
  eliminateLocalVariables b nums (solvePhaseBody >>= continuation)=
  eliminateLocalVariables b (update nums vardef_0__solve_middle (Z.of_nat ((start+start+span)/2)))
    (loop span (KoxiaLeafEvents.leafEventBody (Z.of_nat span)) >>= fun _ => popFrameBody >>= continuation).
Proof.
  intros leftEq rightEq phaseEq small addressesFit.
  unfold solvePhaseBody,numberLocalGet,numberLocalSet,addInt,subInt,divIntUnsigned.
  normalize_table_loop. rewrite leftEq,rightEq.
  rewrite (coerce64_small (Z.of_nat start+Z.of_nat (start+span))) by lia.
  try rewrite decide_False by lia.
  replace ((Z.of_nat start+Z.of_nat (start+span))/2) with (Z.of_nat ((start+start+span)/2))
    by (rewrite Nat2Z.inj_div; f_equal; lia).
  rewrite !lookupDifferent by congruence. rewrite phaseEq.
  rewrite bool_decide_true by reflexivity. normalize_table_loop.
  rewrite !lookupDifferent by congruence. rewrite leftEq,rightEq.
  rewrite (coerce64_small (Z.of_nat (start+span)-Z.of_nat start)) by lia.
  replace (Z.of_nat (start+span)-Z.of_nat start) with (Z.of_nat span) by lia.
  rewrite bool_decide_true by lia. normalize_table_loop.
  rewrite !lookupDifferent by congruence. rewrite leftEq,rightEq.
  rewrite (coerce64_small (Z.of_nat (start+span)-Z.of_nat start)) by lia.
  replace (Z.of_nat (start+span)-Z.of_nat start) with (Z.of_nat span) by lia.
  rewrite Nat2Z.id.
  unfold popFrameBody,numberLocalGet,numberLocalSet,subInt. normalize_table_loop. cbn [withLocalVariablesReturnValue withinLoopReturnValue] in *. rewrite !bind_unit_identity. normalize_table_loop.
  apply f_equal. apply f_equal. apply functional_extensionality. intros [].
  apply f_equal. apply functional_extensionality. intro currentDepth.
  cbn [withLocalVariablesReturnValue withinLoopReturnValue] in *.
  destruct (bool_decide (currentDepth=0)); normalize_table_loop; reflexivity.
Qed.
