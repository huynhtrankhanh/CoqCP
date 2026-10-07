From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaLeaf KoxiaLeafEvents KoxiaMerge.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
Local Open Scope Z_scope.
Definition solvePrepBody (x : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (booleanLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_reverse))) >>= fun x => if x then (
    (liftToWithinLoop ((xorBits (((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_end)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__sequence) x) >>= fun x => Done _ _ _ (coerceInt x 64)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_ch) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_begin)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__sequence) x) >>= fun x => Done _ _ _ (coerceInt x 64)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_ch) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance) x)) >>=
    fun _ => (liftToWithinLoop ((Done _ _ _ 0%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag) x)) >>=
    fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_minimum)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64))))) >>= fun x => if x then (
      (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_balance)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_minimum) x)) >>=
      fun _ => (liftToWithinLoop ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag) x)) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) (Done _ _ _ 1%Z)) >>= fun x => ((addInt 64 ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_flag))) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x y)) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)).
Definition solveVisitBody (x : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ (fst (fst (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (fst (element_tuple)))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (fst (element_tuple))))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_phase) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (fst (element_tuple)))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_base) x)) >>=
  fun _ => (liftToWithinLoop ((((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_depth)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x) >>= (fun element_tuple => Done _ _ _ ((snd (element_tuple))))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_saved) x)) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_l)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_r))) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_middle) x)) >>=
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
Definition solveCompact : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve) withLocalVariablesReturnValue unit := (((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__prefix) x y) >>=
fun _ => ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_end)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_begin))) >>= fun x => loop (Z.to_nat x) (solvePrepBody x)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x y) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_length) x) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count)) >>= fun tuple_element_1 => ((Done _ _ _ 0%Z) >>= fun tuple_element_2 => ((Done _ _ _ 0%Z) >>= fun tuple_element_3 => ((Done _ _ _ 0%Z) >>= fun tuple_element_4 => Done _ _ _ (tuple_element_0, tuple_element_1, tuple_element_2, tuple_element_3, tuple_element_4)))))) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__frames) x y) >>=
fun _ => ((addInt 64 (multInt 64 (Done _ _ _ 4%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (vardef_0__solve_count))) (Done _ _ _ 1%Z)) >>= fun x => loop (Z.to_nat x) (solveVisitBody x)) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__poly) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__solve (arraydef_0__result) x y) >>=
fun _ => Done _ _ _ tt).
Lemma solveCompact_exact : solveCompact=funcdef_0__solve_body.
Proof. unfold solveCompact,solvePrepBody,solveVisitBody,leafEventBody,ordinaryCoefficientBody,specialCoefficientBody,mergeCoefficientBody. reflexivity. Qed.
