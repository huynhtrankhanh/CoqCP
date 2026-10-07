From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaArrays KoxiaModular KoxiaTables KoxiaMemoryPreservation KoxiaWorkspace KoxiaRoots KoxiaFourier KoxiaBinomial.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.

Lemma growArrays_replace {I T} `{EqDecision I} (values : forall name:I,list(T name)) name count zero :
  growArrays values name count zero=replaceArray values name (growList (values name) count zero).
Proof.
  apply functional_extensionality_dep. intro other.
  destruct (decide (other=name)) as [->|different].
  - rewrite growArrays_same,replaceArray_same. reflexivity.
  - rewrite growArrays_other,replaceArray_other by assumption. reflexivity.
Qed.
Definition arrayGrow name count zero : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  Dispatch _ _ _ (Grow _ _ name (Z.of_nat count) zero) (fun _=>Done _ _ _ tt).
Lemma arrayGrow_execution state name count zero (continuation:unit->Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) :
  exec (arrayGrow name count zero >>=continuation) state=
  exec (continuation tt) (withArray state name (growList (memory state name) count zero)).
Proof.
  unfold arrayGrow. cbn [bind exec step optionBind]. rewrite Nat2Z.id,growArrays_replace. reflexivity.
Qed.
Lemma arrayGrow_empty state name count zero (continuation:unit->Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) : memory state name=[] ->
  exec (arrayGrow name count zero >>=continuation) state=
  exec (continuation tt) (withArray state name (repeat zero count)).
Proof.
  intro empty. rewrite arrayGrow_execution,empty. unfold growList. cbn [length app]. rewrite Nat.sub_0_r. reflexivity.
Qed.
Lemma zeroCanonical count : tableCanonical (repeat 0 count).
Proof. unfold tableCanonical. induction count; constructor; [unfold koxiaModulus; lia|assumption]. Qed.

Definition earlyAllocated (state:@Machine arrayIndex1 (arrayType _ environment1)) n :=
  withArray (withArray (withArray (withArray (withArray state
    arraydef_0__prefix (repeat 0 (S n)))
    arraydef_0__factorial (repeat 0 (S n)))
    arraydef_0__inverseFactorial (repeat 0 (S n)))
    arraydef_0__poly (repeat 0 (2*n+64)))
    arraydef_0__arena (repeat 0 (4*n+128)).
Definition lateAllocated (state:@Machine arrayIndex1 (arrayType _ environment1)) count :=
  withArray (withArray (withArray state arraydef_0__work (repeat 0 count))
    arraydef_0__other (repeat 0 count)) arraydef_0__roots (repeat 0 count).
Definition workspaceEmpty (state:@Machine arrayIndex1 (arrayType _ environment1)) : Prop :=
  memory state arraydef_0__prefix=[] /\ memory state arraydef_0__factorial=[] /\
  memory state arraydef_0__inverseFactorial=[] /\ memory state arraydef_0__poly=[] /\
  memory state arraydef_0__arena=[] /\ memory state arraydef_0__work=[] /\
  memory state arraydef_0__other=[] /\ memory state arraydef_0__roots=[].
Definition earlyGrow n : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  arrayGrow arraydef_0__prefix (S n) 0 >>=fun _=>arrayGrow arraydef_0__factorial (S n) 0 >>=fun _=>
  arrayGrow arraydef_0__inverseFactorial (S n) 0 >>=fun _=>arrayGrow arraydef_0__poly (2*n+64) 0 >>=fun _=>
  arrayGrow arraydef_0__arena (4*n+128) 0.
Definition lateGrow count : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  arrayGrow arraydef_0__work count 0 >>=fun _=>arrayGrow arraydef_0__other count 0 >>=fun _=>arrayGrow arraydef_0__roots count 0.
Ltac simplify_main_memory :=
  cbn [withArray withMemory memory]; repeat (rewrite replaceArray_same || rewrite replaceArray_other by congruence).
Lemma earlyGrow_execution state n (continuation:unit->Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) : workspaceEmpty state ->
  exec (earlyGrow n >>=continuation) state=exec (continuation tt) (earlyAllocated state n).
Proof.
  intros [prefix [factorial [inverse [poly [arena rest]]]]]. unfold earlyGrow.
  rewrite <-!bindAssoc.
  rewrite arrayGrow_empty by exact prefix.
  rewrite arrayGrow_empty by (simplify_main_memory; exact factorial).
  rewrite arrayGrow_empty by (simplify_main_memory; exact inverse).
  rewrite arrayGrow_empty by (simplify_main_memory; exact poly).
  rewrite arrayGrow_empty by (simplify_main_memory; exact arena).
  reflexivity.
Qed.
Lemma lateGrow_execution state n count (continuation:unit->Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit) : workspaceEmpty state ->
  exec (lateGrow count >>=continuation) (earlyAllocated state n)=
  exec (continuation tt) (lateAllocated (earlyAllocated state n) count).
Proof.
  intros [_ [_ [_ [_ [_ [work [other roots]]]]]]]. unfold lateGrow.
  rewrite <-!bindAssoc.
  rewrite arrayGrow_empty by (unfold earlyAllocated; simplify_main_memory; exact work).
  rewrite arrayGrow_empty by (unfold earlyAllocated; simplify_main_memory; exact other).
  rewrite arrayGrow_empty by (unfold earlyAllocated; simplify_main_memory; exact roots).
  reflexivity.
Qed.
Lemma allocated_io state n count :
  stdin (lateAllocated (earlyAllocated state n) count)=stdin state /\
  stdout (lateAllocated (earlyAllocated state n) count)=stdout state.
Proof. split; reflexivity. Qed.

Lemma allocated_memory state n count name :
  memory (lateAllocated (earlyAllocated state n) count) name=
  match name as selected return list(arrayType _ environment1 selected) with
  | arraydef_0__prefix | arraydef_0__factorial | arraydef_0__inverseFactorial => repeat 0 (S n)
  | arraydef_0__work | arraydef_0__other | arraydef_0__roots => repeat 0 count
  | arraydef_0__poly => repeat 0 (2*n+64)
  | arraydef_0__arena => repeat 0 (4*n+128)
  | arraydef_0__sequence => memory state arraydef_0__sequence
  | arraydef_0__result => memory state arraydef_0__result
  | arraydef_0__frames => memory state arraydef_0__frames
  | arraydef_0__printBuffer => memory state arraydef_0__printBuffer
  end.
Proof. destruct name; unfold lateAllocated,earlyAllocated; simplify_main_memory; reflexivity. Qed.

Lemma builtWorkspace state n stage :
  1<=Z.of_nat n<=500000 -> (stage<=20)%nat -> 2*Z.of_nat n+1<=stageSize stage ->
  memory state arraydef_0__prefix=repeat 0 (S n) ->
  memory state arraydef_0__work=repeat 0 (sizeNat stage) ->
  memory state arraydef_0__other=repeat 0 (sizeNat stage) ->
  memory state arraydef_0__roots=rootTableValues stage (repeat 0 (sizeNat stage)) ->
  memory state arraydef_0__factorial=factorialTableValues n (repeat 0 (S n)) ->
  memory state arraydef_0__inverseFactorial=inverseFactorialTableValues n (repeat 0 (S n)) ->
  memory state arraydef_0__poly=repeat 0 (2*n+64) ->
  memory state arraydef_0__arena=repeat 0 (4*n+128) ->
  length (memory state arraydef_0__frames)=32%nat ->
  (2<length (memory state arraydef_0__result))%nat ->
  SolverWorkspace state n stage.
Proof.
  intros inputBound stageBound capacity prefix work other roots factorial inverse poly arena frames result.
  pose proof (stageSize_bound stage stageBound) as transformBound. rewrite stageSize_nat in transformBound.
  constructor; try assumption.
  all: try rewrite work; try rewrite other; try rewrite roots; try rewrite factorial; try rewrite inverse;
    try rewrite poly; try rewrite arena; try rewrite prefix.
  all: try rewrite rootTableValues_length; try rewrite factorialTableValues_length;
    try rewrite inverseFactorialTableValues_length; try rewrite repeat_length; try lia.
  - intros i bound. apply factorialTableValues_lookup; rewrite ?repeat_length; lia.
  - intros i bound. apply inverseFactorialTableValues_lookup; rewrite ?repeat_length; [lia|unfold koxiaModulus; lia|lia].
  - apply zeroCanonical.
  - apply zeroCanonical.
  - apply rootTableValues_canonical. apply zeroCanonical.
  - apply zeroCanonical.
  - apply zeroCanonical.
  - intros step stepBound offset offsetBound. apply rootTableValues_correct;
      try assumption; rewrite ?repeat_length; lia.
Qed.
