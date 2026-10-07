From CoqCP Require Import Options Imperative Execution KoxiaArrays KoxiaArrayLoops KoxiaTables KoxiaConvolution.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Lemma tableStore_execution {R} state name index value
  (continuation : unit -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
  (index<length (memory state name))%nat ->
  exec (tableWrite name (Z.of_nat index) value >>= continuation) state=
  exec (continuation tt) (withArray state name (<[index:=value]>(memory state name))).
Proof.
  intro room. unfold tableWrite. cbn [bind].
  rewrite <-(withArray_self state name) at 1. rewrite execStoreArray by exact room. reflexivity.
Qed.
Definition storedChildFrames (state : @Machine arrayIndex1 (arrayType _ environment1)) depth start span middle base saved :=
  withArray state arraydef_0__frames
    (<[S depth:=(Z.of_nat start,Z.of_nat middle,0,0,0)]>
      (<[depth:=(Z.of_nat start,Z.of_nat (start+span),1,Z.of_nat base,Z.of_nat saved)]>
        (memory state arraydef_0__frames))).
Lemma storeChild_execution {R} state depth start span middle base saved
  (continuation : unit -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
  (S depth<length (memory state arraydef_0__frames))%nat ->
  exec (tableWrite arraydef_0__frames (Z.of_nat depth)
    (Z.of_nat start,Z.of_nat (start+span),1,Z.of_nat base,Z.of_nat saved) >>= fun _ =>
    tableWrite arraydef_0__frames (Z.of_nat (S depth))
      (Z.of_nat start,Z.of_nat middle,0,0,0) >>= continuation) state=
  exec (continuation tt) (storedChildFrames state depth start span middle base saved).
Proof.
  intro room. rewrite tableStore_execution by lia.
  unfold tableWrite. cbn [bind]. rewrite execStoreArray by (rewrite length_insert; exact room). reflexivity.
Qed.
