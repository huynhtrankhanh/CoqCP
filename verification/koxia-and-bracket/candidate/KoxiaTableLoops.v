From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaPower KoxiaArrays KoxiaRoots KoxiaFourier KoxiaBinomial KoxiaTables.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque fastPower modularPower stageRoot stageInverse.

Definition mainRootStageBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub 20%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
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
)).

Definition mainRootOffsetBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) binder_1) (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_k)) binder_1) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_z))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__roots) x y)) >>=
    fun _ => Done _ _ _ tt
  )).

Create Rewrite HintDb koxia_table_steps.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Ltac normalize_table_loop := repeat progress
  (autorewrite with advance_program koxia_table_steps; try rewrite <- !bindAssoc;
   try rewrite decide_False by lia; cbn [bind]).

Lemma rootOffsetNormalized b nums half total remaining continuation :
  nums vardef_0__main_k=Z.of_nat half ->
  (remaining<total)%nat -> (total<half)%nat -> Z.of_nat half<=1048576 ->
  eliminateLocalVariables b nums (mainRootOffsetBody (Z.of_nat total) remaining >>= continuation) =
  chainStep arraydef_0__roots half (total-remaining-1) (nums vardef_0__main_z) >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intros halfEq remainingBound totalBound halfBound.
  unfold mainRootOffsetBody,addInt,multInt,modIntUnsigned,numberLocalGet,retrieve,store.
  normalize_table_loop.
  rewrite halfEq.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId.
  assert (leftId : coerceInt (Z.of_nat half+Z.of_nat (total-remaining-1)) 64=
    Z.of_nat (half+(total-remaining-1))).
  { rewrite <-Nat2Z.inj_add. apply coerce64_small. change (0<=Z.of_nat (half+(total-remaining-1))<18446744073709551616). lia. }
  rewrite leftId.
  assert (rightId : coerceInt (Z.of_nat (half+(total-remaining-1))+1) 64=
    Z.of_nat (half+S (total-remaining-1))).
  { replace (Z.of_nat (half+(total-remaining-1))+1) with (Z.of_nat (half+S (total-remaining-1))) by lia.
    apply coerce64_small. change (0<=Z.of_nat (half+S (total-remaining-1))<18446744073709551616). lia. }
  rewrite rightId. unfold chainStep,tableRead,tableWrite,intValue,fromIntArray,machineProduct.
  cbn [bind]. reflexivity.
Qed.

Lemma rootOffsetsNormalized b nums half fuel total continuation :
  nums vardef_0__main_k=Z.of_nat half ->
  (fuel<=total<half)%nat -> Z.of_nat half<=1048576 ->
  eliminateLocalVariables b nums (loop fuel (mainRootOffsetBody (Z.of_nat total)) >>= continuation) =
  chainAction fuel total arraydef_0__roots half (fun _ => nums vardef_0__main_z) >>= fun _ =>
    eliminateLocalVariables b nums (continuation tt).
Proof.
  intros halfEq bounds halfBound. induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,rootOffsetNormalized with (half:=half) by lia.
  cbn [chainAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros [].
  apply IH. lia.
Qed.

Definition mainRootStageCompact : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
  fun _ => dropWithinLoop
    (liftToWithinLoop
      (numberLocalGet _ _ _ vardef_0__main_k >>= fun half =>
       numberLocalGet _ _ _ vardef_0__main_size >>= fun size =>
       Done _ _ _ (negb (bool_decide (half<size)))) >>= fun finished =>
     (if finished then break _ _ _ >>= fun _ => Done _ _ _ tt else Done _ _ _ tt) >>= fun _ =>
     liftToWithinLoop
      (divIntUnsigned (Done _ _ _ 998244352) (multInt 64 (Done _ _ _ 2) (numberLocalGet _ _ _ vardef_0__main_k)) >>= fun exponent =>
       liftToWithLocalVariables (funcdef_0__power (fun _ => false)
         (update (update (fun _ => 0) vardef_0__power_base 3) vardef_0__power_exponent exponent))) >>= fun _ =>
     liftToWithinLoop
      (retrieve _ _ _ arraydef_0__result 2 >>= fun root => numberLocalSet _ _ _ vardef_0__main_z root) >>= fun _ =>
     liftToWithinLoop
      (numberLocalGet _ _ _ vardef_0__main_k >>= fun half => store _ _ _ arraydef_0__roots half 1) >>= fun _ =>
     liftToWithinLoop
      (subInt 64 (numberLocalGet _ _ _ vardef_0__main_k) (Done _ _ _ 1) >>= fun count =>
       loop (Z.to_nat count) (mainRootOffsetBody count)) >>= fun _ =>
     liftToWithinLoop
      (multInt 64 (numberLocalGet _ _ _ vardef_0__main_k) (Done _ _ _ 2) >>= fun doubled =>
       numberLocalSet _ _ _ vardef_0__main_k doubled) >>= fun _ => Done _ _ _ tt).
Lemma mainRootStageCompact_exact : mainRootStageBody=mainRootStageCompact.
Proof. reflexivity. Qed.

Definition rootStageAction half : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue Z :=
  funcdef_0__power (fun _ => false)
    (update (update (fun _ => 0) vardef_0__power_base 3) vardef_0__power_exponent
      (998244352/(2*Z.of_nat half))) >>= fun _ =>
  tableRead arraydef_0__result 2 >>= fun root =>
  tableWrite arraydef_0__roots (Z.of_nat half) 1 >>= fun _ =>
  chainAction (half-1) (half-1) arraydef_0__roots half (fun _ => root) >>= fun _ =>
  Done _ _ _ root.

Lemma rootStageNormalized b nums half remaining continuation :
  nums vardef_0__main_k=Z.of_nat half -> 0<Z.of_nat half<=1048576 ->
  eliminateLocalVariables b nums (mainRootStageBody remaining >>= continuation) =
  if bool_decide (Z.of_nat half<nums vardef_0__main_size) then
    rootStageAction half >>= fun root =>
    eliminateLocalVariables b (update (update nums vardef_0__main_z root) vardef_0__main_k (2*Z.of_nat half))
      (continuation KeepGoing)
  else eliminateLocalVariables b nums (continuation Stop).
Proof.
  intros halfEq halfBound. rewrite mainRootStageCompact_exact.
  unfold mainRootStageCompact,numberLocalGet,numberLocalSet,divIntUnsigned,multInt,subInt,retrieve,store.
  normalize_table_loop. rewrite halfEq.
  destruct (bool_decide (Z.of_nat half<nums vardef_0__main_size)) eqn:continuing.
  - cbn [negb]. normalize_table_loop.
    assert (double : coerceInt (2*Z.of_nat half) 64=2*Z.of_nat half).
    { apply coerce64_small. change (0<=2*Z.of_nat half<18446744073709551616). lia. }
    rewrite halfEq,double,decide_False by lia. normalize_table_loop. rewrite eliminateLift.
    unfold rootStageAction,tableRead,tableWrite. cbn [bind]. rewrite <-!bindAssoc.
    apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
    apply f_equal. apply functional_extensionality. intro root. normalize_table_loop.
    rewrite lookupDifferent by congruence. rewrite halfEq.
    assert (countId : coerceInt (Z.of_nat half-1) 64=Z.of_nat (half-1)).
    { replace (Z.of_nat half-1) with (Z.of_nat (half-1)) by lia.
      apply coerce64_small. change (0<=Z.of_nat (half-1)<18446744073709551616). lia. }
    rewrite countId,Nat2Z.id.
    rewrite rootOffsetsNormalized with (half:=half) by (rewrite ?lookupDifferent; try congruence; lia).
    rewrite lookupSame.
    apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
    rewrite lookupDifferent by congruence. rewrite halfEq.
    replace (Z.of_nat half*2) with (2*Z.of_nat half) by ring. rewrite double. reflexivity.
  - cbn [negb]. normalize_table_loop. reflexivity.
Qed.

Definition withResult (state : @Machine arrayIndex1 (arrayType _ environment1)) (value : Z) :=
  withMemory state (modifyArray (memory state) arraydef_0__result 2 value).
Lemma withResult_memory state value : memory (withResult state value) arraydef_0__result=
  <[(2%nat):=value]>(memory state arraydef_0__result).
Proof. unfold withResult. cbn [withMemory memory]. apply modifyArray_same. Qed.
Lemma withResult_roots state value : memory (withResult state value) arraydef_0__roots=memory state arraydef_0__roots.
Proof. unfold withResult. cbn [withMemory memory]. apply modifyArray_other. congruence. Qed.

Theorem rootStageAction_execution stage state values :
  (stage<20)%nat -> (sizeNat stage+sizeNat stage<=length values)%nat -> tableCanonical values ->
  (2<length (memory state arraydef_0__result))%nat ->
  exec (rootStageAction (sizeNat stage)) (withArray state arraydef_0__roots values)=
  Some (stageRoot (S stage),withArray (withResult state (stageRoot (S stage))) arraydef_0__roots (rootBlock stage values)).
Proof.
  intros bound room canonical resultRoom.
  pose proof (stageSize_positive stage) as positive. rewrite stageSize_nat in positive.
  assert (exponentRange : 0<=998244352/(2*Z.of_nat (sizeNat stage))<2^64).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; [lia|change (998244352<(2*Z.of_nat (sizeNat stage))*18446744073709551616); nia]]. }
  assert (answerEq : 3^(998244352/(2*Z.of_nat (sizeNat stage))) mod koxiaModulus=stageRoot (S stage)).
  { unfold stageRoot at 1. rewrite stageSize_succ,stageSize_nat.
    unfold koxiaModulus at 2. change (3^(998244352/(2*Z.of_nat (sizeNat stage))) mod koxiaModulus=
      modularPower 3 (998244352/(2*Z.of_nat (sizeNat stage)))).
    rewrite modularPower_correct by exact exponentRange. reflexivity. }
  unfold rootStageAction. rewrite exec_bind,generated_power_execution.
  2: rewrite lookupDifferent by congruence; rewrite lookupSame; unfold koxiaModulus; lia.
  2: rewrite lookupSame; exact exponentRange.
  2: cbn [withArray withMemory memory]; rewrite replaceArray_other by congruence; exact resultRoom.
  cbn [optionBind fst snd]. rewrite lookupSame,lookupDifferent by congruence. rewrite lookupSame,answerEq.
  rewrite withArray_store_other by congruence.
  set (powered := withResult state (stageRoot (S stage))).
  assert (resultArray : memory (withArray powered arraydef_0__roots values) arraydef_0__result=
    <[(2%nat):=stageRoot (S stage)]>(memory state arraydef_0__result)).
  { cbn [withArray withMemory memory]. rewrite replaceArray_other by congruence.
    unfold powered. apply withResult_memory. }
  unfold tableRead. cbn [bind].
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    (withArray powered arraydef_0__roots values) arraydef_0__result 2 0)
    by (rewrite resultArray,length_insert; exact resultRoom).
  rewrite resultArray,nthUpdate by exact resultRoom.
  rewrite <-stageSize_nat.
  change (exec
    ((tableWrite arraydef_0__roots (stageSize stage) 1 >>= fun _ =>
      chainAction (sizeNat stage-1) (sizeNat stage-1) arraydef_0__roots (sizeNat stage)
        (fun _ => stageRoot (S stage))) >>= fun _ => Done _ _ _ (stageRoot (S stage)))
    (withArray powered arraydef_0__roots values)=
    Some (stageRoot (S stage),withArray powered arraydef_0__roots (rootBlock stage values))).
  rewrite exec_bind,rootBlock_execution by assumption. reflexivity.
Qed.

Fixpoint rootInitAction fuel stage total nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__main -> Z) :=
  match fuel with
  | O => Done _ _ _ nums
  | S fuel => if bool_decide ((stage<total)%nat) then
    rootStageAction (sizeNat stage) >>= fun root =>
    rootInitAction fuel (S stage) total
      (update (update nums vardef_0__main_z root) vardef_0__main_k (stageSize (S stage)))
    else Done _ _ _ nums
  end.

Lemma rootInitNormalized fuel stage total b nums continuation :
  (stage<=total<=20)%nat -> nums vardef_0__main_k=stageSize stage ->
  nums vardef_0__main_size=stageSize total ->
  eliminateLocalVariables b nums (loop fuel mainRootStageBody >>= continuation) =
  rootInitAction fuel stage total nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in stage,nums |- *; [reflexivity|].
  intros bound halfEq sizeEq.
  rewrite loop_S,<-bindAssoc,rootStageNormalized with (half:=sizeNat stage).
  2: rewrite <-stageSize_nat; exact halfEq.
  2: { rewrite <-stageSize_nat. split; [apply stageSize_positive|apply stageSize_bound; lia]. }
  rewrite <-stageSize_nat,sizeEq. cbn [rootInitAction].
  destruct (Nat.eq_dec stage total) as [finished|unfinished].
  - subst stage. rewrite !bool_decide_false by lia. reflexivity.
  - assert (stageLess : (stage<total)%nat) by lia.
    assert (sizeLess : stageSize stage<stageSize total).
    { unfold stageSize. apply Z.pow_lt_mono_r; lia. }
    rewrite !bool_decide_true by assumption. rewrite <-bindAssoc.
    apply f_equal. apply functional_extensionality. intro root.
    rewrite <-stageSize_succ. apply IH; [lia|apply lookupSame|].
    rewrite !lookupDifferent by congruence. exact sizeEq.
Qed.

Lemma withResult_other state value name : name<>arraydef_0__result ->
  memory (withResult state value) name=memory state name.
Proof. intros different. unfold withResult. cbn [withMemory memory]. apply modifyArray_other. exact different. Qed.

Theorem rootInitAction_execution fuel stage total state values nums :
  (stage<=total<=20)%nat -> (total-stage<=fuel)%nat ->
  (sizeNat total<=length values)%nat -> tableCanonical values ->
  (2<length (memory state arraydef_0__result))%nat -> nums vardef_0__main_k=stageSize stage ->
  exists final finalState,
    exec (rootInitAction fuel stage total nums)
      (withArray state arraydef_0__roots (rootTableValues stage values))=Some (final,finalState) /\
    memory finalState arraydef_0__roots=rootTableValues total values /\
    (2<length (memory finalState arraydef_0__result))%nat /\
    stdin finalState=stdin state /\ stdout finalState=stdout state /\
    final vardef_0__main_k=stageSize total /\
    (forall name, name<>arraydef_0__roots -> name<>arraydef_0__result -> memory finalState name=memory state name) /\
    (forall name, name<>vardef_0__main_k -> name<>vardef_0__main_z -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in stage,state,nums |- *.
  - intros bound enough room canonical resultRoom halfEq.
    assert (stage=total) by lia. subst stage.
    exists nums,(withArray state arraydef_0__roots (rootTableValues total values)).
    split; [reflexivity|]. split; [cbn [withArray withMemory memory]; apply replaceArray_same|].
    split; [cbn [withArray withMemory memory]; rewrite replaceArray_other by congruence; exact resultRoom|].
    split; [reflexivity|]. split; [reflexivity|]. split; [exact halfEq|].
    split; [intros name notRoots notResult; cbn [withArray withMemory memory]; apply replaceArray_other; exact notRoots|].
    intros; reflexivity.
  - intros bound enough room canonical resultRoom halfEq.
    cbn [rootInitAction].
    destruct (Nat.eq_dec stage total) as [finished|unfinished].
    + subst stage. rewrite bool_decide_false by lia.
      exists nums,(withArray state arraydef_0__roots (rootTableValues total values)).
      split; [reflexivity|]. split; [cbn [withArray withMemory memory]; apply replaceArray_same|].
      split; [cbn [withArray withMemory memory]; rewrite replaceArray_other by congruence; exact resultRoom|].
      split; [reflexivity|]. split; [reflexivity|]. split; [exact halfEq|].
      split; [intros name notRoots notResult; cbn [withArray withMemory memory]; apply replaceArray_other; exact notRoots|].
      intros; reflexivity.
    + assert (stageLess : (stage<total)%nat) by lia.
      rewrite bool_decide_true by exact stageLess. rewrite exec_bind,rootStageAction_execution.
      2: lia.
      2: { rewrite rootTableValues_length,<-sizeNat_succ.
         pose proof (sizeNat_mono (S stage) total ltac:(lia)); lia. }
      2: { apply rootTableValues_canonical. exact canonical. }
      2: exact resultRoom.
      cbn [optionBind fst snd].
      set (nextNums := update (update nums vardef_0__main_z (stageRoot (S stage))) vardef_0__main_k (stageSize (S stage))).
      destruct (IH (S stage) (withResult state (stageRoot (S stage))) nextNums ltac:(lia) ltac:(lia)
        room canonical ltac:(rewrite withResult_memory,length_insert; exact resultRoom)
        ltac:(unfold nextNums; apply lookupSame))
        as [final [finalState [executed [roots [finalResult [input [output [finalHalf [otherArrays otherNums]]]]]]]]].
      exists final,finalState. split; [exact executed|]. split; [exact roots|]. split; [exact finalResult|].
      split; [exact input|]. split; [exact output|]. split; [exact finalHalf|]. split.
      * intros name notRoots notResult. rewrite otherArrays by assumption. apply withResult_other. exact notResult.
      * intros name notK notZ. rewrite otherNums by assumption. unfold nextNums. rewrite !lookupDifferent by congruence. reflexivity.
Qed.

Theorem root_initializer_execution total state b nums :
  (total<=20)%nat -> nums vardef_0__main_k=1 -> nums vardef_0__main_size=stageSize total ->
  (sizeNat total<=length (memory state arraydef_0__roots))%nat ->
  tableCanonical (memory state arraydef_0__roots) -> (2<length (memory state arraydef_0__result))%nat ->
  exists final finalState,
    (forall continuation, exec (eliminateLocalVariables b nums
      (loop 20 mainRootStageBody >>= continuation)) state=
      exec (eliminateLocalVariables b final (continuation tt)) finalState) /\
    memory finalState arraydef_0__roots=rootTableValues total (memory state arraydef_0__roots) /\
    tableCanonical (memory finalState arraydef_0__roots) /\
    (forall step offset, (step<total)%nat -> (offset<sizeNat step)%nat ->
      congruent (nth (sizeNat step+offset) (memory finalState arraydef_0__roots) 0)
        (rootPower (S step) (Z.of_nat offset))) /\
    (2<length (memory finalState arraydef_0__result))%nat /\
    stdin finalState=stdin state /\ stdout finalState=stdout state /\
    (forall name, name<>arraydef_0__roots -> name<>arraydef_0__result -> memory finalState name=memory state name) /\
    (forall name, name<>vardef_0__main_k -> name<>vardef_0__main_z -> final name=nums name).
Proof.
  intros bound halfEq sizeEq room canonical resultRoom.
  destruct (rootInitAction_execution 20 0 total state (memory state arraydef_0__roots) nums
    ltac:(lia) ltac:(lia) room canonical resultRoom halfEq)
    as [final [finalState [executed [roots [finalResult [input [output [finalHalf [otherArrays otherNums]]]]]]]]].
  cbn [rootTableValues] in executed. rewrite withArray_self in executed.
  exists final,finalState. split.
  - intro continuation. rewrite rootInitNormalized with (stage:=0%nat) (total:=total) by (try assumption; lia).
    rewrite exec_bind,executed. reflexivity.
  - split; [exact roots|]. split.
    + rewrite roots. apply rootTableValues_canonical. exact canonical.
    + split.
      * intros step offset stepBound offsetBound. rewrite roots.
        apply rootTableValues_correct; assumption.
      * split; [exact finalResult|]. split; [exact input|]. split; [exact output|].
        split; assumption.
Qed.

Definition mainFactorialBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x) (addInt 64 binder_0 (Done _ _ _ 1%Z))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__factorial) x y)) >>=
  fun _ => Done _ _ _ tt
)).

Definition mainInverseFactorialBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => ((modIntUnsigned (multInt 64 ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x) (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) binder_0)) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__inverseFactorial) x y)) >>=
  fun _ => Done _ _ _ tt
)).

Lemma factorialOffsetNormalized b nums total remaining continuation :
  (remaining<total)%nat -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (mainFactorialBody (Z.of_nat total) remaining >>= continuation) =
  chainStep arraydef_0__factorial 0 (total-remaining-1) (Z.of_nat (S (total-remaining-1))) >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intros remainingBound totalBound. unfold koxiaModulus in totalBound.
  unfold mainFactorialBody,addInt,multInt,modIntUnsigned,retrieve,store. normalize_table_loop.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId.
  assert (nextId : coerceInt (Z.of_nat (total-remaining-1)+1) 64=Z.of_nat (S (total-remaining-1))).
  { replace (Z.of_nat (total-remaining-1)+1) with (Z.of_nat (S (total-remaining-1))) by lia.
    apply coerce64_small. change (0<=Z.of_nat (S (total-remaining-1))<18446744073709551616). lia. }
  rewrite nextId. unfold chainStep,tableRead,tableWrite,intValue,fromIntArray,machineProduct. cbn [bind]. reflexivity.
Qed.
Lemma factorialLoopNormalized b nums fuel total continuation :
  (fuel<=total)%nat -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (loop fuel (mainFactorialBody (Z.of_nat total)) >>= continuation) =
  chainAction fuel total arraydef_0__factorial 0 (fun index => Z.of_nat (S index)) >>= fun _ =>
    eliminateLocalVariables b nums (continuation tt).
Proof.
  intros bounds totalBound. induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,factorialOffsetNormalized by (try exact totalBound; lia).
  cbn [chainAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros [].
  apply IH. lia.
Qed.

Lemma inverseFactorialOffsetNormalized b nums total remaining continuation :
  nums vardef_0__main_n=Z.of_nat total -> (remaining<total)%nat -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (mainInverseFactorialBody (Z.of_nat total) remaining >>= continuation) =
  backwardStep arraydef_0__inverseFactorial remaining >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intros totalEq remainingBound totalBound. unfold koxiaModulus in totalBound.
  unfold mainInverseFactorialBody,subInt,multInt,modIntUnsigned,numberLocalGet,retrieve,store.
  normalize_table_loop. rewrite totalEq.
  assert (readId : coerceInt (Z.of_nat total-(Z.of_nat total-Z.of_nat remaining-1)) 64=Z.of_nat (S remaining)).
  { replace (Z.of_nat total-(Z.of_nat total-Z.of_nat remaining-1)) with (Z.of_nat (S remaining)) by lia.
    apply coerce64_small. change (0<=Z.of_nat (S remaining)<18446744073709551616). lia. }
  rewrite readId.
  assert (writeId : coerceInt (Z.of_nat (S remaining)-1) 64=Z.of_nat remaining).
  { replace (Z.of_nat (S remaining)-1) with (Z.of_nat remaining) by lia.
    apply coerce64_small. change (0<=Z.of_nat remaining<18446744073709551616). lia. }
  rewrite writeId. unfold backwardStep,tableRead,tableWrite,intValue,fromIntArray,machineProduct.
  cbn [bind]. apply f_equal. apply functional_extensionality. intro value. normalize_table_loop.
  rewrite totalEq,readId. reflexivity.
Qed.
Lemma inverseFactorialLoopNormalized b nums fuel total continuation :
  nums vardef_0__main_n=Z.of_nat total -> (fuel<=total)%nat -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (loop fuel (mainInverseFactorialBody (Z.of_nat total)) >>= continuation) =
  backwardAction fuel arraydef_0__inverseFactorial >>= fun _ =>
    eliminateLocalVariables b nums (continuation tt).
Proof.
  intros totalEq bounds totalBound. induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,inverseFactorialOffsetNormalized by (try assumption; lia).
  cbn [backwardAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros [].
  apply IH. lia.
Qed.

Lemma factorial_initializer_normalized b nums total continuation : Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums
    (store _ _ _ arraydef_0__factorial 0 1 >>= fun _ =>
      loop total (mainFactorialBody (Z.of_nat total)) >>= continuation)=
  factorialTableAction total >>= fun _ => eliminateLocalVariables b nums (continuation tt).
Proof.
  intro small. unfold store,factorialTableAction,tableWrite. normalize_table_loop.
  rewrite factorialLoopNormalized by (try exact small; lia). reflexivity.
Qed.
Theorem factorial_initializer_execution b nums total state continuation :
  (total<length (memory state arraydef_0__factorial))%nat -> Z.of_nat total<koxiaModulus ->
  tableCanonical (memory state arraydef_0__factorial) ->
  exec (eliminateLocalVariables b nums
    (store _ _ _ arraydef_0__factorial 0 1 >>= fun _ =>
      loop total (mainFactorialBody (Z.of_nat total)) >>= continuation)) state=
  exec (eliminateLocalVariables b nums (continuation tt))
    (withArray state arraydef_0__factorial (factorialTableValues total (memory state arraydef_0__factorial))).
Proof.
  intros room small canonical. rewrite factorial_initializer_normalized by exact small.
  rewrite exec_bind.
  pose proof (factorialTableAction_execution total state (memory state arraydef_0__factorial) room small canonical) as executed.
  rewrite withArray_self in executed. rewrite executed. reflexivity.
Qed.

Definition mainInverseInitializer total : Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue unit :=
  retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__factorial (Z.of_nat total) >>= fun base =>
  liftToWithLocalVariables (funcdef_0__power (fun _ => false)
    (update (update (fun _ => 0) vardef_0__power_base base) vardef_0__power_exponent 998244351)) >>= fun _ =>
  retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__result 2 >>= fun inverse =>
  store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main arraydef_0__inverseFactorial (Z.of_nat total) inverse >>= fun _ =>
  loop total (mainInverseFactorialBody (Z.of_nat total)).
Definition inverseBuildAction total :=
  tableRead arraydef_0__factorial (Z.of_nat total) >>= fun base =>
  funcdef_0__power (fun _ => false)
    (update (update (fun _ => 0) vardef_0__power_base base) vardef_0__power_exponent 998244351) >>= fun _ =>
  tableRead arraydef_0__result 2 >>= fun inverse =>
  tableWrite arraydef_0__inverseFactorial (Z.of_nat total) inverse >>= fun _ =>
  backwardAction total arraydef_0__inverseFactorial.
Lemma inverse_initializer_normalized b nums total continuation :
  nums vardef_0__main_n=Z.of_nat total -> Z.of_nat total<koxiaModulus ->
  eliminateLocalVariables b nums (mainInverseInitializer total >>= continuation)=
  inverseBuildAction total >>= fun _ => eliminateLocalVariables b nums (continuation tt).
Proof.
  intros totalEq small. unfold mainInverseInitializer,inverseBuildAction,retrieve,store,tableRead,tableWrite.
  rewrite <-!bindAssoc. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intro base. normalize_table_loop. rewrite eliminateLift.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intro inverse. normalize_table_loop.
  rewrite inverseFactorialLoopNormalized with (total:=total) by (try assumption; lia). reflexivity.
Qed.

Theorem inverseBuildAction_execution total state values :
  (total<length values)%nat -> Z.of_nat total<koxiaModulus -> tableCanonical values ->
  (total<length (memory state arraydef_0__factorial))%nat ->
  nth total (memory state arraydef_0__factorial) 0=factorialMod total ->
  (2<length (memory state arraydef_0__result))%nat ->
  exec (inverseBuildAction total) (withArray state arraydef_0__inverseFactorial values)=
  Some (tt,withArray (withResult state (inverseFactorialMod total)) arraydef_0__inverseFactorial
    (inverseFactorialTableValues total values)).
Proof.
  intros room small canonical facRoom facCorrect resultRoom.
  unfold inverseBuildAction,tableRead. cbn [bind].
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    (withArray state arraydef_0__inverseFactorial values) arraydef_0__factorial total 0)
    by (cbn [withArray withMemory memory]; rewrite replaceArray_other by congruence; exact facRoom).
  cbn [withArray withMemory memory]. rewrite replaceArray_other by congruence. rewrite facCorrect.
  rewrite exec_bind,generated_power_execution.
  2: { rewrite lookupDifferent by congruence; rewrite lookupSame. pose proof (factorialMod_positive total small); lia. }
  2: { rewrite lookupSame. change (0<=998244351<18446744073709551616). lia. }
  2: cbn [memory]; try rewrite replaceArray_other by congruence; exact resultRoom.
  cbn [optionBind fst snd]. rewrite lookupSame,lookupDifferent by congruence. rewrite lookupSame.
  assert (inverseEq : factorialMod total^998244351 mod koxiaModulus=inverseFactorialMod total).
  { unfold inverseFactorialMod. rewrite modularPower_correct.
    - reflexivity.
    - unfold koxiaModulus. change (0<=998244351<18446744073709551616). lia. }
  rewrite inverseEq.
  change (exec
    (Dispatch _ _ _ (Retrieve _ _ arraydef_0__result 2) (fun inverse =>
      tableWrite arraydef_0__inverseFactorial (Z.of_nat total) inverse >>= fun _ =>
      backwardAction total arraydef_0__inverseFactorial))
    (withMemory (withArray state arraydef_0__inverseFactorial values)
      (modifyArray (memory (withArray state arraydef_0__inverseFactorial values)) arraydef_0__result 2 (inverseFactorialMod total)))=
    Some (tt,withArray (withResult state (inverseFactorialMod total)) arraydef_0__inverseFactorial
      (inverseFactorialTableValues total values))).
  rewrite withArray_store_other by congruence.
  set (powered := withResult state (inverseFactorialMod total)).
  assert (resultArray : memory (withArray powered arraydef_0__inverseFactorial values) arraydef_0__result=
    <[(2%nat):=inverseFactorialMod total]>(memory state arraydef_0__result)).
  { cbn [withArray withMemory memory]. rewrite replaceArray_other by congruence. unfold powered. apply withResult_memory. }
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    (withArray powered arraydef_0__inverseFactorial values) arraydef_0__result 2 0)
    by (rewrite resultArray,length_insert; exact resultRoom).
  rewrite resultArray,nthUpdate by exact resultRoom.
  change (exec (inverseFactorialTableAction total) (withArray powered arraydef_0__inverseFactorial values)=
    Some (tt,withArray powered arraydef_0__inverseFactorial (inverseFactorialTableValues total values))).
  apply inverseFactorialTableAction_execution; assumption.
Qed.

Theorem inverse_initializer_execution b nums total state continuation :
  nums vardef_0__main_n=Z.of_nat total -> Z.of_nat total<koxiaModulus ->
  (total<length (memory state arraydef_0__inverseFactorial))%nat ->
  tableCanonical (memory state arraydef_0__inverseFactorial) ->
  (total<length (memory state arraydef_0__factorial))%nat ->
  nth total (memory state arraydef_0__factorial) 0=factorialMod total ->
  (2<length (memory state arraydef_0__result))%nat ->
  exec (eliminateLocalVariables b nums (mainInverseInitializer total >>= continuation)) state=
  exec (eliminateLocalVariables b nums (continuation tt))
    (withArray (withResult state (inverseFactorialMod total)) arraydef_0__inverseFactorial
      (inverseFactorialTableValues total (memory state arraydef_0__inverseFactorial))).
Proof.
  intros totalEq small room canonical facRoom facCorrect resultRoom.
  rewrite inverse_initializer_normalized by assumption. rewrite exec_bind.
  pose proof (inverseBuildAction_execution total state (memory state arraydef_0__inverseFactorial)
    room small canonical facRoom facCorrect resultRoom) as executed.
  rewrite withArray_self in executed. rewrite executed. reflexivity.
Qed.
