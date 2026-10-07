From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaMainProgram KoxiaMainSegments KoxiaSolveExecution KoxiaPreprocess KoxiaWorkspace KoxiaConvolution KoxiaTables KoxiaTableLoops KoxiaIntegers KoxiaModular KoxiaPolynomial KoxiaPaths KoxiaLeafRun KoxiaPrinter.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__solve mappedPrinter.
Definition mainAnswerAction split total : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue Z :=
  funcdef_0__solve (fun _=>false) (solveForwardNums split) >>=fun _=>
  tableRead arraydef_0__result 0 >>=fun left=>
  funcdef_0__solve (update (fun _=>false) vardef_0__solve_reverse true) (solveReverseNums split total) >>=fun _=>
  tableRead arraydef_0__result 0 >>=fun right=>Done _ _ _ (coerceInt (left*right) 64 mod koxiaModulus).
Lemma mainSolveProductNormalized b nums continuation :
  eliminateLocalVariables b nums (mainSolveProductBody >>=continuation)=
  mainAnswerAction (nums vardef_0__main_split) (nums vardef_0__main_n) >>=fun answer=>
  mappedPrinter answer >>=fun _=>eliminateLocalVariables b (update nums vardef_0__main_answer answer) (continuation tt).
Proof.
  unfold mainSolveProductBody,mainAnswerAction,solveForwardNums,solveReverseNums,
    numberLocalGet,numberLocalSet,retrieve,multInt,modIntUnsigned,tableRead.
  rewrite <-!bindAssoc. normalize_table_loop. rewrite eliminateLift.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intro left. normalize_table_loop.
  rewrite !lookupDifferent by congruence. rewrite eliminateLift.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intro right. normalize_table_loop.
  rewrite lookupSame. rewrite updateSame. unfold koxiaModulus. rewrite eliminateLift,lookupSame. peel_main_bind.
  match goal with response:unit |- _ => destruct response; reflexivity end.
Qed.
Definition halfResidue word := run (eventsFrom word 0) (pathCoefficients [0%nat]) 0 mod koxiaModulus.
Lemma halfResidue_bound word : 0<=halfResidue word<koxiaModulus.
Proof. unfold halfResidue. apply Z.mod_pos_bound. unfold koxiaModulus; lia. Qed.

Theorem mainAnswerAction_execution state a b padding n stage :
  SolverWorkspace state n stage -> length (a++b)=n ->
  memory state arraydef_0__sequence=map bracketByte (a++b)++padding ->
  exists final,
    exec (mainAnswerAction (Z.of_nat (length a)) (Z.of_nat n)) state=
      Some ((halfResidue a*halfResidue (reverseBrackets b)) mod koxiaModulus,final) /\
    SolverWorkspace final n stage /\ stdin final=stdin state /\ stdout final=stdout state /\
    memory final arraydef_0__printBuffer=memory state arraydef_0__printBuffer.
Proof.
  intros workspace totalEq source. pose proof (workspace_input_bound _ _ _ workspace) as inputBound.
  assert (firstInput : prepInput state (solveForwardNums (Z.of_nat (length a))) false (Z.of_nat (length a)) a).
  { apply forward_prepInput with (b:=b) (padding:=padding); [rewrite totalEq; lia|exact source]. }
  destruct (generated_solve_execution (fun _=>false) (solveForwardNums (Z.of_nat (length a))) state a n stage workspace
    ltac:(rewrite length_app in totalEq; lia)
    ltac:(unfold solveForwardNums; rewrite lookupSame,lookupDifferent by congruence; rewrite lookupSame; lia)
    ltac:(unfold solveForwardNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveForwardNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveForwardNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveForwardNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveForwardNums; rewrite !lookupDifferent by congruence; reflexivity)
    firstInput) as [middle [firstExec [firstValue [middleWorkspace [middleInput [middleOutput firstOther]]]]]].
  assert (middleSource : memory middle arraydef_0__sequence=map bracketByte (a++b)++padding).
  { rewrite firstOther by congruence. exact source. }
  assert (secondInput : prepInput middle (solveReverseNums (Z.of_nat (length a)) (Z.of_nat n)) true
    (Z.of_nat (length (reverseBrackets b))) (reverseBrackets b)).
  { rewrite <-totalEq. apply reverse_prepInput with (padding:=padding); [rewrite totalEq; lia|exact middleSource]. }
  destruct (generated_solve_execution (update (fun _=>false) vardef_0__solve_reverse true)
    (solveReverseNums (Z.of_nat (length a)) (Z.of_nat n)) middle (reverseBrackets b) n stage middleWorkspace
    ltac:(rewrite reverseBrackets_length,length_app in *; lia)
    ltac:(unfold solveReverseNums; rewrite lookupSame,lookupDifferent by congruence; rewrite lookupSame;
      rewrite reverseBrackets_length,length_app in *; lia)
    ltac:(unfold solveReverseNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveReverseNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveReverseNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveReverseNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(unfold solveReverseNums; rewrite !lookupDifferent by congruence; reflexivity)
    ltac:(rewrite lookupSame; exact secondInput))
    as [final [secondExec [secondValue [finalWorkspace [finalInput [finalOutput secondOther]]]]]].
  exists final. split.
  - unfold mainAnswerAction. rewrite exec_bind,firstExec. cbn [optionBind fst snd].
    rewrite exec_bind,tableRead_execution with (index:=0%nat) by
      (try congruence; pose proof (workspace_result_room _ _ _ middleWorkspace); lia).
    cbn [optionBind fst snd intValue]. rewrite firstValue.
    rewrite exec_bind,secondExec. cbn [optionBind fst snd].
    rewrite exec_bind,tableRead_execution with (index:=0%nat) by
      (try congruence; pose proof (workspace_result_room _ _ _ finalWorkspace); lia).
    cbn [optionBind fst snd intValue]. rewrite secondValue.
    change (Some (coerceInt (halfResidue a*halfResidue (reverseBrackets b)) 64 mod koxiaModulus,final)=
      Some ((halfResidue a*halfResidue (reverseBrackets b)) mod koxiaModulus,final)).
    rewrite coerce64_small; [reflexivity|].
    pose proof (halfResidue_bound a). pose proof (halfResidue_bound (reverseBrackets b)).
    unfold koxiaModulus in *. change (0<=halfResidue a*halfResidue (reverseBrackets b)<18446744073709551616). nia.
  - split; [exact finalWorkspace|]. split; [rewrite finalInput,middleInput; reflexivity|].
    split; [rewrite finalOutput,middleOutput; reflexivity|]. rewrite secondOther,firstOther by congruence. reflexivity.
Qed.
