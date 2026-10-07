From CoqCP Require Import Options Imperative Execution KoxiaArrays KoxiaInput KoxiaPrinter KoxiaMainProgram KoxiaMainMemory
  KoxiaLiterals KoxiaSolveExecution KoxiaTableLoops KoxiaMainInitialization KoxiaMainSegments KoxiaMainResult KoxiaTables KoxiaModular KoxiaPolynomial KoxiaPaths KoxiaWorkspace.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec Submission.SpecProperties Submission.OptimalSplit Submission.FullCounting
  Submission.MinimumScan Submission.SpecPrinter.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List Arith.PeanoNat Logic.FunctionalExtensionality Lia.
Import ListNotations Trusted.Spec Submission.SpecProperties Submission.OptimalSplit Submission.FullCounting
  Submission.MinimumScan Submission.SpecPrinter.
Local Open Scope Z_scope.
Local Opaque mainWorkspaceBody mainSolveProductBody mainAnswerAction mappedPrinter loop funcdef_0__solve.

Lemma calculated_answer s :
  (halfResidue (firstn (minimumIndex s) s)*halfResidue (reverseBrackets (skipn (minimumIndex s) s))) mod koxiaModulus=
  Z.of_nat(answer s).
Proof.
  unfold halfResidue,reverseBrackets,koxiaModulus.
  rewrite <-Z.mul_mod by lia.
  exact (computed_abstract_solver_correct s).
Qed.

Module Implementation.
Definition program : Program := funcdef_0__main (fun _=>false) (fun _=>0%Z).
Theorem correct : required program.
Proof.
  split; [reflexivity|]. intros s bounds.
  assert (inputBound:1<=Z.of_nat (length s)<=500000).
  { pose proof bounds as [lower upper]. apply Nat2Z.inj_le in lower,upper.
    pose proof capacityLiteral as capacity.
    rewrite capacity in upper. change (1<=Z.of_nat (length s)) in lower. lia. }
  pose (initial := ({| memory:=arrays _ environment1; stdin:=input s; stdout:=[] |}
    : @Machine arrayIndex1 (arrayType _ environment1))).
  pose (loaded:=withArray initial arraydef_0__sequence (repeat 0 500000)).
  destruct (inputAction_globalMinimum s loaded ltac:(lia) eq_refl
    ltac:(cbn [loaded withArray withMemory memory]; apply replaceArray_same))
    as [scanned [scanExec [scanInput [scanOutput [scanSequence scanOther]]]]].
  pose proof (globalMinimum_correct s) as [_ [scanCount [cutBound rest]]].
  assert (scannerN : stateInputNums (globalMinimumState s) 10 vardef_0__main_n=Z.of_nat (length s)).
  { unfold stateInputNums,inputNums. rewrite scanCount. reflexivity. }
  assert (scannerSplit : stateInputNums (globalMinimumState s) 10 vardef_0__main_split=Z.of_nat (minimumIndex s)).
  { reflexivity. }
  assert (emptyWorkspace:workspaceEmpty scanned).
  { unfold workspaceEmpty. repeat split; rewrite scanOther by congruence;
      unfold loaded,initial; cbn [withArray withMemory memory]; rewrite replaceArray_other by congruence; reflexivity. }
  assert (frameRoom:length (memory scanned arraydef_0__frames)=32%nat).
  { rewrite scanOther by congruence. unfold loaded,initial. cbn [withArray withMemory memory].
    rewrite replaceArray_other by congruence. reflexivity. }
  assert (resultRoom:(2<length (memory scanned arraydef_0__result))%nat).
  { rewrite scanOther by congruence. unfold loaded,initial. cbn [withArray withMemory memory].
    rewrite replaceArray_other by congruence. change (2<3)%nat; lia. }
  destruct (generated_workspace_execution scanned (fun _=>false) (stateInputNums (globalMinimumState s) 10)
    (length s) inputBound scannerN emptyWorkspace frameRoom resultRoom)
    as [readyNums [ready [readyExec [workspace [readyInput [readyOutput [readySequence [readyPrint [readyN readySplit]]]]]]]]].
  pose (a:=firstn (minimumIndex s) s). pose (b:=skipn (minimumIndex s) s).
  assert (splitEq:length a=minimumIndex s).
  { unfold a,minimumIndex. rewrite firstn_length,Nat.min_l by exact cutBound. reflexivity. }
  assert (join:a++b=s).
  { unfold a,b. apply firstn_skipn. }
  assert (source:memory ready arraydef_0__sequence=map bracketByte (a++b)++repeat 0 (500000-length s)).
  { rewrite readySequence,scanSequence,join. reflexivity. }
  destruct (mainAnswerAction_execution ready a b (repeat 0 (500000-length s)) (length s) (mainStage (length s))
    workspace ltac:(rewrite join; reflexivity) source)
    as [solved [answerExec [solvedWorkspace [solvedInput [solvedOutput solvedPrint]]]]].
  assert (answerEq:(halfResidue a*halfResidue (reverseBrackets b)) mod koxiaModulus=Z.of_nat(answer s)).
  { exact (calculated_answer s). }
  assert (printRoom:length (memory solved arraydef_0__printBuffer)=20%nat).
  { rewrite solvedPrint,readyPrint,scanOther by congruence. unfold loaded,initial.
    cbn [withArray withMemory memory]. rewrite replaceArray_other by congruence. reflexivity. }
  destruct (generated_spec_printer (answer s) solved ltac:(pose proof (answer_range s); lia) printRoom)
    as [printed [printExec [printOutput printInput]]].
  exists (withOutput printed (stdout printed++[10])). split.
  - unfold program,funcdef_0__main. rewrite <-mainCompact_exact,mainInputNormalized.
    change_exec_state initial.
    rewrite arrayGrow_empty by (unfold initial; reflexivity). change_exec_state loaded.
    rewrite exec_bind,scanExec. cbn [optionBind fst snd].
    rewrite mainWorkspaceCPS_exact,readyExec.
    rewrite mainSolveProductCPS_exact,mainSolveProductNormalized.
    rewrite readyN,readySplit,scannerN,scannerSplit,<-splitEq.
    rewrite exec_bind,answerExec. cbn [optionBind fst snd]. rewrite answerEq.
    rewrite exec_bind,printExec. cbn [optionBind fst snd].
    unfold writeChar. normalize_table_loop. reflexivity.
  - split.
    + change (stdout printed++[10]=output s). rewrite printOutput,solvedOutput,readyOutput,scanOutput.
      change (([]++decimal 10 (answer s))++[10]=output s). reflexivity.
    + change (stdin printed=[]). rewrite printInput,solvedInput,readyInput. exact scanInput.
Qed.
End Implementation.
