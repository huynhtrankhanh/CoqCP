From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaInput KoxiaPrinter KoxiaIntegers KoxiaSizes KoxiaRoots KoxiaTables KoxiaTableLoops KoxiaLiterals KoxiaSolveExecution KoxiaMainMemory KoxiaFourier.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque loop funcdef_0__solve funcdef_0__power.

Definition mainSizeBody : nat->Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub 20%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun a => (addInt 64 (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 1%Z)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size) x)) >>=
  fun _ => Done _ _ _ tt
)).

Definition mainInverseDynamic : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue unit :=
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial total) >>=fun base=>
  liftToWithLocalVariables (funcdef_0__power (fun _=>false)
    (update (update (fun _=>0) vardef_0__power_base base) vardef_0__power_exponent 998244351)) >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__result 2 >>=fun inverse=>
    store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__inverseFactorial total inverse) >>=fun _=>
  numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>loop (Z.to_nat total) (mainInverseFactorialBody total).

Definition mainWorkspaceBody : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue unit :=
  (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n) (Done _ _ _ 1) >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__prefix size 0) >>=fun _=>
  (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n) (Done _ _ _ 1) >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial size 0) >>=fun _=>
  (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n) (Done _ _ _ 1) >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__inverseFactorial size 0) >>=fun _=>
  (addInt 64 (multInt 64 (Done _ _ _ 2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n)) (Done _ _ _ 64) >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__poly size 0) >>=fun _=>
  (addInt 64 (multInt 64 (Done _ _ _ 4) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n)) (Done _ _ _ 128) >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__arena size 0) >>=fun _=>
  numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_size 1 >>=fun _=>loop 20 mainSizeBody >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_size >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__work size 0) >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_size >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__other size 0) >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_size >>=fun size=>grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__roots size 0) >>=fun _=>
  numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_k 1 >>=fun _=>loop 20 mainRootStageBody >>=fun _=>
  store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial 0 1 >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>loop (Z.to_nat total) (mainFactorialBody total)) >>=fun _=>
  mainInverseDynamic.

Definition mainSolveProductBody : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue unit :=
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_split >>=fun split=>liftToWithLocalVariables
    (funcdef_0__solve (fun _=>false) (update (update (fun _=>0) vardef_0__solve_begin 0) vardef_0__solve_end split))) >>=fun _=>
  (retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__result 0 >>=fun value=>numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_answer value) >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_split >>=fun split=>numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>
    liftToWithLocalVariables (funcdef_0__solve (update (fun _=>false) vardef_0__solve_reverse true)
      (update (update (fun _=>0) vardef_0__solve_begin split) vardef_0__solve_end total))) >>=fun _=>
  (modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_answer)
    (retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__result 0)) (Done _ _ _ 998244353) >>=fun value=>numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_answer value) >>=fun _=>
  numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_answer >>=fun value=>liftToWithLocalVariables (mappedPrinter value).

Definition MainContinuation := unit->Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue unit.
Definition mainWorkspaceCPS (continuation:MainContinuation) : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue unit :=
((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__prefix) size (0%Z)) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) size (0%Z)) >>=
fun _ => ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) size (0%Z)) >>=
fun _ => ((addInt 64 (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 64%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__poly) size (0%Z)) >>=
fun _ => ((addInt 64 (multInt 64 (Done _ _ _ 4%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 128%Z)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__arena) size (0%Z)) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun a => (addInt 64 (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n))) (Done _ _ _ 1%Z)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__work) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__other) size (0%Z)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) size (0%Z)) >>=
fun _ => ((Done _ _ _ 1%Z) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k) x) >>=
fun _ => ((Done _ _ _ 20%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_size)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 3%Z) >>= fun preset0 => (divIntUnsigned (Done _ _ _ 998244352%Z) (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)))) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__power_base) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__power_exponent) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__power y x))) >>=
  fun _ => (liftToWithinLoop (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_z) x)) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x y)) >>=
  fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) (Done _ _ _ 1%Z)) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) binder_1) (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_z))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x y)) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k) x)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => ((Done _ _ _ 0%Z) >>= fun x => ((Done _ _ _ 1%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x y) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x) (addInt 64 binder_0 (Done _ _ _ 1%Z))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x) >>= fun preset0 => (Done _ _ _ 998244351%Z) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__power_base) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__power_exponent) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__power y x)) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => (((Done _ _ _ 2%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x y) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x) (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0)) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x y)) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => continuation tt.

Definition mainSolveProductCPS (continuation:MainContinuation) : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue unit :=
((Done _ _ _ 0%Z) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split)) >>= fun preset1 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_begin) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_end) preset1)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (funcdef_0__solve y x)) >>=
fun _ => (((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer) x) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split)) >>= fun preset0 => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun preset1 => (Done _ _ _ true) >>= fun preset2 => (((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_begin) preset0)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_end) preset1)) >>= fun x => ((Done _ _ _ (fun x => false)) >>= fun x => Done _ _ _ (update x (vardef_0__solve_reverse) preset2)) >>= fun y => liftToWithLocalVariables (funcdef_0__solve y x)) >>=
fun _ => ((modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer)) ((Done _ _ _ 0%Z) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__result) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer) x) >>=
fun _ => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_answer)) >>= fun preset0 => ((Done _ _ _ (fun x => 0%Z)) >>= fun x => Done _ _ _ (update x (vardef_0_PrintInt64_unsigned_num) preset0)) >>= fun x => (Done _ _ _ (fun x => false)) >>= fun y => liftToWithLocalVariables (translateArrays (funcdef_0_PrintInt64_unsigned y x) (arrayType _ environment1) (fun name => match name with| arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end) (fun name => ltac:(destruct name; reflexivity)))) >>=
fun _ => continuation tt.

Definition mainCompact : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue unit :=
((Done _ _ _ 500000%Z) >>= fun size => grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__sequence) size (0%Z)) >>=
fun _ => ((Done _ _ _ 500001%Z) >>= fun x => loop (Z.to_nat x) (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 41%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__sequence) x y)) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n) x)) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_minimum)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64))))) >>= fun x => if x then (
    (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_minimum) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)))) >>=
fun _ => mainWorkspaceCPS (fun _ => mainSolveProductCPS (fun _ => (((Done _ _ _ 10%Z) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main x) >>=
fun _ => Done _ _ _ tt)).

Lemma mainCompact_exact : mainCompact=funcdef_0__main_body.
Proof. reflexivity. Qed.

#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 @dropWithinLoop_break : koxia_table_steps.
Lemma mainSizeStep b nums remaining n continuation : nums vardef_0__main_n=Z.of_nat n -> Z.of_nat n<=500000 ->
  eliminateLocalVariables b nums (mainSizeBody remaining >>=continuation)=
  if bool_decide (nums vardef_0__main_size<2*Z.of_nat n+1)
  then eliminateLocalVariables b (update nums vardef_0__main_size (coerceInt (nums vardef_0__main_size*2) 64)) (continuation KeepGoing)
  else eliminateLocalVariables b nums (continuation Stop).
Proof.
  intros nEq nBound. unfold mainSizeBody,numberLocalGet,numberLocalSet,addInt,multInt.
  normalize_table_loop. rewrite nEq.
  rewrite (coerce64_small (2*Z.of_nat n)),coerce64_small by lia.
  destruct (bool_decide (nums vardef_0__main_size<2*Z.of_nat n+1)); cbn [negb]; normalize_table_loop; reflexivity.
Qed.

Theorem mainSizeLoopNormalized b nums fuel stage n continuation :
  (stage+fuel<=20)%nat -> nums vardef_0__main_size=stageSize stage ->
  nums vardef_0__main_n=Z.of_nat n -> Z.of_nat n<=500000 ->
  eliminateLocalVariables b nums (loop fuel mainSizeBody >>=continuation)=
  eliminateLocalVariables b
    (update nums vardef_0__main_size (stageSize (ceilingStage fuel (2*Z.of_nat n+1) stage))) (continuation tt).
Proof.
  induction fuel as [|fuel IH] in stage,nums |- *.
  - intros bound sizeEq nEq nBound. cbn [ceilingStage loop]. rewrite <-sizeEq,update_own. reflexivity.
  - intros bound sizeEq nEq nBound.
    rewrite loop_S,<-bindAssoc,mainSizeStep with (n:=n) by assumption.
    rewrite sizeEq. cbn [ceilingStage].
    destruct (bool_decide (stageSize stage<2*Z.of_nat n+1)).
    + assert (nextSize : coerceInt (stageSize stage*2) 64=stageSize (S stage)).
      { rewrite stageSize_succ. replace (stageSize stage*2) with (2*stageSize stage) by ring.
        apply coerce64_small. pose proof (stageSize_positive (S stage)).
        pose proof (stageSize_bound (S stage) ltac:(lia)). rewrite stageSize_succ in *.
        change (0<=2*stageSize stage<18446744073709551616). lia. }
      rewrite nextSize.
      rewrite (IH (update nums vardef_0__main_size (stageSize (S stage))) (S stage)
        ltac:(lia) ltac:(apply lookupSame) ltac:(rewrite lookupDifferent by congruence; exact nEq) nBound).
      rewrite updateSame. reflexivity.
    + rewrite <-sizeEq,update_own. reflexivity.
Qed.

Lemma mainInverseDynamicNormalized b nums n continuation : nums vardef_0__main_n=Z.of_nat n ->
  eliminateLocalVariables b nums (mainInverseDynamic >>=continuation)=
  eliminateLocalVariables b nums (mainInverseInitializer n >>=continuation).
Proof.
  intro nEq. unfold mainInverseDynamic,mainInverseInitializer,numberLocalGet,retrieve,store.
  normalize_table_loop. rewrite nEq. apply f_equal. apply functional_extensionality. intro base.
  normalize_table_loop. rewrite !eliminateLift. apply f_equal. apply functional_extensionality. intros [].
  normalize_table_loop. rewrite nEq. apply f_equal. apply functional_extensionality. intro inverse.
  normalize_table_loop. rewrite nEq,Nat2Z.id. reflexivity.
Qed.

Definition mainStage n := ceilingStage 20 (2*Z.of_nat n+1) 0.
Definition mainSizedNums nums n := update nums vardef_0__main_size (stageSize (mainStage n)).
Definition mainReadyNums nums n := update (mainSizedNums nums n) vardef_0__main_k 1.
Definition mainTablesBody (n:nat) : Action (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue unit :=
  loop 20 mainRootStageBody >>=fun _=>
  store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial 0 1 >>=fun _=>
  (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>loop (Z.to_nat total) (mainFactorialBody total)) >>=fun _=>mainInverseDynamic.
Lemma mainWorkspaceNormalized b nums n continuation :
  nums vardef_0__main_n=Z.of_nat n -> Z.of_nat n<=500000 ->
  eliminateLocalVariables b nums (mainWorkspaceBody >>=continuation)=
  earlyGrow n >>=fun _=>lateGrow (sizeNat (mainStage n)) >>=fun _=>
  eliminateLocalVariables b (mainReadyNums nums n) (mainTablesBody n >>=continuation).
Proof.
  intros nEq nBound.
  unfold mainWorkspaceBody,mainReadyNums,mainSizedNums,mainTablesBody,earlyGrow,lateGrow,arrayGrow,
    numberLocalGet,numberLocalSet,grow,addInt,multInt.
  rewrite <-!bindAssoc. normalize_table_loop.
  rewrite nEq.
  rewrite !(coerce64_small (Z.of_nat n+1)),(coerce64_small (2*Z.of_nat n)),(coerce64_small (4*Z.of_nat n)) by (cbn; lia).
  rewrite (coerce64_small (2*Z.of_nat n+64)),(coerce64_small (4*Z.of_nat n+128)) by (cbn; lia).
  rewrite !Nat2Z.inj_succ,!Nat2Z.inj_add,!Nat2Z.inj_mul.
  do 5 (apply f_equal; apply functional_extensionality; intros []).
  rewrite mainSizeLoopNormalized with (stage:=0%nat) (n:=n)
    by (first [lia | apply lookupSame | rewrite lookupDifferent by congruence; exact nEq | reflexivity]).
  unfold mainStage. try rewrite updateSame.
  normalize_table_loop. rewrite !lookupSame,<-stageSize_nat.
  do 3 (apply f_equal; apply functional_extensionality; intros []).
  normalize_table_loop. reflexivity.
Qed.

Ltac peel_main_bind :=
  match goal with
  | |- @bind ?E ?R ?A ?B ?left ?lc = @bind _ _ _ _ ?right ?rc =>
      change (@bind E R A B left lc = @bind E R A B left rc);
      refine (@f_equal (A->Action E R B) (Action E R B) (fun k => @bind E R A B left k) lc rc _);
      apply functional_extensionality; let r:=fresh "r" in intro r
  end.

Lemma mainWorkspaceCPS_exact continuation : mainWorkspaceCPS continuation=mainWorkspaceBody >>=continuation.
Proof.
  unfold mainWorkspaceCPS,mainWorkspaceBody,mainInverseDynamic.
  fold mainSizeBody mainRootStageBody mainFactorialBody mainInverseFactorialBody.
  repeat progress (try rewrite <-!bindAssoc; try rewrite !leftIdentity).
  repeat first [progress (try rewrite <-!bindAssoc; try rewrite !leftIdentity) | timeout 2 peel_main_bind | timeout 1 (progress f_equal) | match goal with |- tt = ?u => destruct u; reflexivity | |- ?u = tt => destruct u; reflexivity end | timeout 1 reflexivity].
Qed.
Lemma mainSolveProductCPS_exact continuation : mainSolveProductCPS continuation=mainSolveProductBody >>=continuation.
Proof.
  unfold mainSolveProductCPS,mainSolveProductBody,mappedPrinter.
  repeat progress (try rewrite <-!bindAssoc; try rewrite !leftIdentity).
  repeat first [progress (try rewrite <-!bindAssoc; try rewrite !leftIdentity) | timeout 2 peel_main_bind | timeout 1 (progress f_equal) | match goal with |- tt = ?u => destruct u; reflexivity | |- ?u = tt => destruct u; reflexivity end | timeout 1 reflexivity].
Qed.

Lemma mainFactorialDynamicNormalized b nums n continuation : nums vardef_0__main_n=Z.of_nat n ->
  eliminateLocalVariables b nums
    (store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial 0 1 >>=fun _=>
     numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main vardef_0__main_n >>=fun total=>
       loop (Z.to_nat total) (mainFactorialBody total) >>=continuation)=
  eliminateLocalVariables b nums
    (store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial 0 1 >>=fun _=>
     loop n (mainFactorialBody (Z.of_nat n)) >>=continuation).
Proof.
  intro nEq. unfold store,numberLocalGet. normalize_table_loop. rewrite nEq,Nat2Z.id. reflexivity.
Qed.

Lemma mainCompact_input_shape : mainCompact=
  grow arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__sequence 500000 0 >>=fun _=>
  loop (Z.to_nat 500001) inputLoopBody >>=fun _=>
  mainWorkspaceCPS (fun _=>mainSolveProductCPS (fun _=>
    writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main 10 >>=fun _=>Done _ _ _ tt)).
Proof. Timeout 10 reflexivity. Qed.

Lemma inputNums_zero : inputNums 0 0 0 0 0=(fun _=>0).
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.

Lemma mainInputNormalized b :
  eliminateLocalVariables b (fun _=>0) mainCompact=
  arrayGrow arraydef_0__sequence 500000%nat 0 >>=fun _=>
  inputAction 500001 (inputNums 0 0 0 0 0) >>=fun finished=>
  eliminateLocalVariables b finished
    (mainWorkspaceCPS (fun _=>mainSolveProductCPS (fun _=>
      writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main 10 >>=fun _=>Done _ _ _ tt))).
Proof.
  rewrite <-inputNums_zero,mainCompact_input_shape. unfold arrayGrow,grow. try rewrite <-!bindAssoc. normalize_table_loop.
  pose proof capacityLiteral as sizeEq.
  pose proof fuelLiteral as fuelEq.
  rewrite sizeEq,fuelEq.
  apply f_equal. apply functional_extensionality. intros [].
  match goal with |- _ = ?right => change (eliminateLocalVariables b (inputNums 0 0 0 0 0)
    (loop 500001 inputLoopBody >>=fun _=>mainWorkspaceCPS (fun _=>mainSolveProductCPS (fun _=>
      writeChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main 10 >>=fun _=>Done _ _ _ tt)))=right) end.
  rewrite inputLoopNormalized. reflexivity.
Qed.
