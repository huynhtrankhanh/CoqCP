From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaPower KoxiaArrays KoxiaRoots KoxiaFourier KoxiaRadix KoxiaNTT KoxiaNTTButterflies KoxiaNTTCorrect KoxiaBinomial KoxiaTables KoxiaTableLoops KoxiaArrayLoops KoxiaSizes KoxiaNegation.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque fastPower modularPower stageRoot stageInverse.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.

Definition convolveSizeBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub 20%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_count)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size) x)) >>=
  fun _ => Done _ _ _ tt
)).

Definition convolveInputBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => ((liftToWithinLoop (binder_0 >>= fun a => (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_length)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_skip))) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop (binder_0 >>= fun x => (((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_skip)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__poly) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)).

Definition convolveKernelBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__other) x y)) >>=
  fun _ => (liftToWithinLoop (binder_0 >>= fun x => ((Done _ _ _ 0%Z) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => ((liftToWithinLoop (binder_0 >>= fun a => (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span)) (Done _ _ _ 1%Z)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop (binder_0 >>= fun x => ((modIntUnsigned (multInt 64 (modIntUnsigned (multInt 64 ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__factorial) x) (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__inverseFactorial) x)) (Done _ _ _ 998244353%Z)) ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_span)) binder_0) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__inverseFactorial) x)) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
)).

Definition convolveProductBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (binder_0 >>= fun x => ((modIntUnsigned (multInt 64 (modIntUnsigned (multInt 64 (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) (binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__other) x)) (Done _ _ _ 998244353%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_scale))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => Done _ _ _ tt
)).

Definition convolveNegateBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop (((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_tmp) x)) >>=
  fun _ => (liftToWithinLoop ((addInt 64 binder_0 (Done _ _ _ 1%Z)) >>= fun x => (((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => (liftToWithinLoop ((subInt 64 (subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_size)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_tmp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x y)) >>=
  fun _ => Done _ _ _ tt
)).

Definition convolveSaveBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve)
  withLocalVariablesReturnValue LoopOutcome :=
fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue _ (Z.sub (Z.sub total (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (vardef_0__convolve_base)) binder_0) >>= fun x => ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve (arraydef_0__arena) x y)) >>=
  fun _ => Done _ _ _ tt
)).

Lemma convolveSizeBody_exact : convolveSizeBody=
  @doublingBody arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve
    vardef_0__convolve_size vardef_0__convolve_count.
Proof. reflexivity. Qed.

Lemma convolve_size_normalized b nums target continuation : nums vardef_0__convolve_size=1 ->
  nums vardef_0__convolve_count=target ->
  eliminateLocalVariables b nums (loop 20 convolveSizeBody >>= continuation)=
  eliminateLocalVariables b (update nums vardef_0__convolve_size (stageSize (ceilingStage 20 target 0))) (continuation tt).
Proof.
  intros sizeEq targetEq. rewrite convolveSizeBody_exact. apply doublingLoopNormalized;
    [congruence|lia|exact sizeEq|exact targetEq].
Qed.

Lemma bool_decide_nat_z i j : bool_decide ((i<j)%nat)=bool_decide (Z.of_nat i<Z.of_nat j).
Proof. apply bool_decide_ext. lia. Qed.
Definition copyStep index target source offset count :=
  tableWrite target (Z.of_nat index) (intValue target 0) >>= fun _ =>
  if bool_decide ((index<count)%nat) then
    tableRead source (Z.of_nat (offset+index)) >>= fun value =>
    tableWrite target (Z.of_nat index) (intValue target (fromIntArray source value))
  else Done _ _ _ tt.

Lemma convolveInputNormalized b nums total remaining len skip continuation :
  nums vardef_0__convolve_length=Z.of_nat len -> nums vardef_0__convolve_skip=Z.of_nat skip ->
  (remaining<total)%nat -> (skip<=len)%nat -> Z.of_nat len<koxiaModulus -> Z.of_nat total<=1048576 ->
  eliminateLocalVariables b nums (convolveInputBody (Z.of_nat total) remaining >>= continuation)=
  copyStep (total-remaining-1) arraydef_0__work arraydef_0__poly skip (len-skip) >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intros lengthEq skipEq remainingBound skipBound lengthBound totalBound. unfold koxiaModulus in lengthBound.
  unfold convolveInputBody,addInt,subInt,numberLocalGet,retrieve,store. normalize_table_loop.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId. unfold copyStep,tableRead,tableWrite,intValue,fromIntArray. cbn [bind].
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  rewrite lengthEq,skipEq.
  assert (tailId : coerceInt (Z.of_nat len-Z.of_nat skip) 64=Z.of_nat (len-skip)).
  { replace (Z.of_nat len-Z.of_nat skip) with (Z.of_nat (len-skip)) by lia.
    apply coerce64_small. change (0<=Z.of_nat (len-skip)<18446744073709551616). lia. }
  rewrite tailId,<-bool_decide_nat_z.
  destruct (bool_decide (((total-remaining-1)<len-skip)%nat)); normalize_table_loop; [|reflexivity].
  rewrite skipEq.
  assert (sourceId : coerceInt (Z.of_nat skip+Z.of_nat (total-remaining-1)) 64=Z.of_nat (skip+(total-remaining-1))).
  { rewrite <-Nat2Z.inj_add. apply coerce64_small. change (0<=Z.of_nat (skip+(total-remaining-1))<18446744073709551616). lia. }
  rewrite sourceId. apply f_equal. apply functional_extensionality. intro value. normalize_table_loop. reflexivity.
Qed.

Lemma convolveInputLoopNormalized b nums fuel total len skip continuation :
  nums vardef_0__convolve_length=Z.of_nat len -> nums vardef_0__convolve_skip=Z.of_nat skip ->
  (fuel<=total)%nat -> (skip<=len)%nat -> Z.of_nat len<koxiaModulus -> Z.of_nat total<=1048576 ->
  eliminateLocalVariables b nums (loop fuel (convolveInputBody (Z.of_nat total)) >>= continuation)=
  copyAction fuel total arraydef_0__work arraydef_0__poly skip (len-skip) >>= fun _ =>
    eliminateLocalVariables b nums (continuation tt).
Proof.
  intros lengthEq skipEq fuelBound skipBound lengthBound totalBound.
  induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,convolveInputNormalized with (len:=len) (skip:=skip) by (try assumption; lia).
  change ((copyStep (total-fuel-1) arraydef_0__work arraydef_0__poly skip (len-skip) >>= fun _ =>
    eliminateLocalVariables b nums (loop fuel (convolveInputBody (Z.of_nat total)) >>= continuation))=
    (copyStep (total-fuel-1) arraydef_0__work arraydef_0__poly skip (len-skip) >>=
      fun _ => copyAction fuel total arraydef_0__work arraydef_0__poly skip (len-skip)) >>=
      fun _ => eliminateLocalVariables b nums (continuation tt)).
  rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros []. apply IH. lia.
Qed.

Lemma withArray_work state values : withArray state arraydef_0__work values=withWork state values.
Proof.
  unfold withArray,withWork. apply f_equal.
  apply functional_extensionality_dep. intro name. destruct name.
  all: cbn [workMemory]; first [rewrite replaceArray_same|rewrite replaceArray_other by congruence]; reflexivity.
Qed.

Definition productStep index scale :=
  tableRead arraydef_0__work (Z.of_nat index) >>= fun left =>
  tableRead arraydef_0__other (Z.of_nat index) >>= fun right =>
  tableWrite arraydef_0__work (Z.of_nat index) (machineProduct (machineProduct left right) scale).
Fixpoint productAction fuel total scale : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with O => Done _ _ _ tt | S fuel =>
    productStep (total-fuel-1) scale >>= fun _ => productAction fuel total scale end.
Definition productValue values other scale index :=
  ((nth index values 0*nth index other 0) mod koxiaModulus*scale) mod koxiaModulus.

Lemma convolveProductNormalized b nums total remaining continuation : (remaining<total)%nat ->
  eliminateLocalVariables b nums (convolveProductBody (Z.of_nat total) remaining >>= continuation)=
  productStep (total-remaining-1) (nums vardef_0__convolve_scale) >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intro remainingBound. unfold convolveProductBody,multInt,modIntUnsigned,numberLocalGet,retrieve,store.
  normalize_table_loop.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId. unfold productStep,tableRead,tableWrite,machineProduct. cbn [bind].
  apply f_equal. apply functional_extensionality. intro left. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intro right. normalize_table_loop. reflexivity.
Qed.
Lemma convolveProductLoopNormalized b nums fuel total continuation : (fuel<=total)%nat ->
  eliminateLocalVariables b nums (loop fuel (convolveProductBody (Z.of_nat total)) >>= continuation)=
  productAction fuel total (nums vardef_0__convolve_scale) >>= fun _ =>
    eliminateLocalVariables b nums (continuation tt).
Proof.
  intro fuelBound. induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,convolveProductNormalized by lia. cbn [productAction].
  rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros []. apply IH. lia.
Qed.
Lemma productStep_execution state values index scale :
  (index<length values)%nat -> (index<length (memory state arraydef_0__other))%nat ->
  0<=nth index values 0<koxiaModulus -> 0<=nth index (memory state arraydef_0__other) 0<koxiaModulus ->
  0<=scale<koxiaModulus ->
  exec (productStep index scale) (withWork state values)=
  Some (tt,withWork state (<[index:=productValue values (memory state arraydef_0__other) scale index]>values)).
Proof.
  intros room otherRoom leftRange rightRange scaleRange.
  unfold productStep,tableRead,tableWrite. cbn [bind]. rewrite execReadWork by exact room.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _
    (withWork state values) arraydef_0__other index 0) by exact otherRoom.
  change (exec
    (Dispatch _ _ _ (Store _ _ arraydef_0__work (Z.of_nat index)
      (machineProduct (machineProduct (nth index values 0) (nth index (memory state arraydef_0__other) 0)) scale))
      (fun _ => Done _ _ _ tt)) (withWork state values)=
    Some (tt,withWork state (<[index:=productValue values (memory state arraydef_0__other) scale index]>values))).
  unfold machineProduct.
  rewrite (residue_product_coerce (nth index values 0) (nth index (memory state arraydef_0__other) 0) leftRange rightRange).
  rewrite residue_product_coerce by (try exact scaleRange; apply residue_bounds).
  rewrite execStoreWork by exact room. reflexivity.
Qed.
Theorem productAction_execution fuel count total state values scale : (count+fuel=total)%nat ->
  (total<=length values)%nat -> (total<=length (memory state arraydef_0__other))%nat ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__other) -> 0<=scale<koxiaModulus ->
  exec (productAction fuel total scale)
    (withWork state (fillValues count values 0 (productValue values (memory state arraydef_0__other) scale)))=
  Some (tt,withWork state (fillValues total values 0 (productValue values (memory state arraydef_0__other) scale))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros countFuel room otherRoom canonical otherCanonical scaleRange.
    assert (count=total) by lia. subst count. reflexivity.
  - intros countFuel room otherRoom canonical otherCanonical scaleRange.
    cbn [productAction]. replace (total-fuel-1)%nat with count by lia.
    assert (otherIndex : (count<length (memory state arraydef_0__other))%nat) by lia.
    rewrite exec_bind,productStep_execution.
    2: rewrite fillValues_length; lia.
    2: lia.
    2: rewrite fillValues_lookup,bool_decide_false by lia; apply tableCanonical_nth; [exact canonical|lia].
    2: apply tableCanonical_nth; [exact otherCanonical|exact otherIndex].
    2: exact scaleRange.
    cbn [optionBind fst snd]. unfold productValue at 1.
    rewrite fillValues_lookup,bool_decide_false by lia.
    pose proof (IH (S count) ltac:(lia) room otherRoom canonical otherCanonical scaleRange) as finish.
    cbn [fillValues Nat.add] in finish. exact finish.
Qed.

Lemma convolveNegateNormalized b nums total remaining size continuation :
  nums vardef_0__convolve_size=Z.of_nat size -> (remaining<total)%nat -> (2*total<size)%nat ->
  Z.of_nat size<=1048576 ->
  eliminateLocalVariables b nums (convolveNegateBody (Z.of_nat total) remaining >>= continuation)=
  nttSwap (Z.of_nat (S (total-remaining-1))) (Z.of_nat (size-S (total-remaining-1))) (nums vardef_0__convolve_tmp) >>= fun saved =>
    eliminateLocalVariables b (update nums vardef_0__convolve_tmp saved) (continuation KeepGoing).
Proof.
  intros sizeEq remainingBound pairsBound sizeBound.
  unfold convolveNegateBody,addInt,subInt,numberLocalGet,numberLocalSet,retrieve,store.
  normalize_table_loop.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId.
  assert (leftId : coerceInt (Z.of_nat (total-remaining-1)+1) 64=Z.of_nat (S (total-remaining-1))).
  { replace (Z.of_nat (total-remaining-1)+1) with (Z.of_nat (S (total-remaining-1))) by lia.
    apply coerce64_small. change (0<=Z.of_nat (S (total-remaining-1))<18446744073709551616). lia. }
  rewrite leftId. unfold nttSwap. rewrite bool_decide_true by lia. cbn [bind].
  apply f_equal. apply functional_extensionality. intro saved. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite sizeEq.
  assert (subtractId : coerceInt (Z.of_nat size-Z.of_nat (total-remaining-1)) 64=
    Z.of_nat (size-(total-remaining-1))).
  { replace (Z.of_nat size-Z.of_nat (total-remaining-1)) with (Z.of_nat (size-(total-remaining-1))) by lia.
    apply coerce64_small. change (0<=Z.of_nat (size-(total-remaining-1))<18446744073709551616). lia. }
  rewrite subtractId.
  assert (rightId : coerceInt (Z.of_nat (size-(total-remaining-1))-1) 64=
    Z.of_nat (size-S (total-remaining-1))).
  { replace (Z.of_nat (size-(total-remaining-1))-1) with (Z.of_nat (size-S (total-remaining-1))) by lia.
    apply coerce64_small. change (0<=Z.of_nat (size-S (total-remaining-1))<18446744073709551616). lia. }
  rewrite rightId.
  apply f_equal. apply functional_extensionality. intro other. normalize_table_loop.
  rewrite lookupDifferent by congruence. rewrite sizeEq,subtractId,rightId,lookupSame. reflexivity.
Qed.
Lemma convolveNegateLoopNormalized b nums fuel total size continuation :
  nums vardef_0__convolve_size=Z.of_nat size -> (fuel<=total)%nat -> (2*total<size)%nat ->
  Z.of_nat size<=1048576 ->
  eliminateLocalVariables b nums (loop fuel (convolveNegateBody (Z.of_nat total)) >>= continuation)=
  negateAction fuel total size (nums vardef_0__convolve_tmp) >>= fun saved =>
    eliminateLocalVariables b (update nums vardef_0__convolve_tmp saved) (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *.
  - intros. cbn [negateAction bind]. rewrite update_own. reflexivity.
  - intros sizeEq fuelBound pairsBound sizeBound.
    rewrite loop_S,<-bindAssoc,convolveNegateNormalized with (size:=size) by (try assumption; lia).
    cbn [negateAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intro saved.
    rewrite IH by (try rewrite lookupDifferent by congruence; try assumption; lia).
    rewrite lookupSame. apply f_equal. apply functional_extensionality. intro last.
    rewrite updateSame. reflexivity.
Qed.

Lemma convolveSaveNormalized b nums total remaining base continuation :
  nums vardef_0__convolve_base=Z.of_nat base -> (remaining<total)%nat ->
  Z.of_nat (base+total)<18446744073709551616 ->
  eliminateLocalVariables b nums (convolveSaveBody (Z.of_nat total) remaining >>= continuation)=
  copyIntoStep (total-remaining-1) arraydef_0__arena arraydef_0__work base 0 >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intros baseEq remainingBound room.
  unfold convolveSaveBody,addInt,numberLocalGet,retrieve,store. normalize_table_loop. rewrite baseEq.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId.
  assert (addressId : coerceInt (Z.of_nat base+Z.of_nat (total-remaining-1)) 64=
    Z.of_nat (base+(total-remaining-1))).
  { rewrite <-Nat2Z.inj_add. apply coerce64_small. change (0<=Z.of_nat (base+(total-remaining-1))<18446744073709551616). lia. }
  rewrite addressId. unfold copyIntoStep,tableRead,tableWrite,intValue,fromIntArray. cbn [bind].
  apply f_equal. apply functional_extensionality. intro value. normalize_table_loop. reflexivity.
Qed.
Lemma convolveSaveLoopNormalized b nums fuel total base continuation :
  nums vardef_0__convolve_base=Z.of_nat base -> (fuel<=total)%nat ->
  Z.of_nat (base+total)<18446744073709551616 ->
  eliminateLocalVariables b nums (loop fuel (convolveSaveBody (Z.of_nat total)) >>= continuation)=
  copyIntoAction fuel total arraydef_0__arena arraydef_0__work base 0 >>= fun _ =>
    eliminateLocalVariables b nums (continuation tt).
Proof.
  intros baseEq fuelBound room. induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,convolveSaveNormalized with (base:=base) by (try assumption; lia).
  cbn [copyIntoAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros []. apply IH. lia.
Qed.

Lemma convolveInputLoop_execution b nums total len skip state values continuation :
  nums vardef_0__convolve_length=Z.of_nat len -> nums vardef_0__convolve_skip=Z.of_nat skip ->
  (skip<=len<=length (memory state arraydef_0__poly))%nat ->
  Z.of_nat len<koxiaModulus -> Z.of_nat total<=1048576 -> (total<=length values)%nat ->
  exec (eliminateLocalVariables b nums (loop total (convolveInputBody (Z.of_nat total)) >>= continuation))
    (withWork state values)=
  exec (eliminateLocalVariables b nums (continuation tt))
    (withWork state (fillValues total values 0 (copyValue (memory state arraydef_0__poly) skip (len-skip)))).
Proof.
  intros lengthEq skipEq polyRoom lengthBound totalBound workRoom.
  assert (sourceRoom : (skip+(len-skip)<=length (memory state arraydef_0__poly))%nat) by lia.
  rewrite convolveInputLoopNormalized with (len:=len) (skip:=skip) by (try assumption; lia).
  rewrite exec_bind. rewrite <-withArray_work.
  pose proof (copyAction_execution total 0 total arraydef_0__work arraydef_0__poly state values
    (memory state arraydef_0__poly) skip (len-skip) ltac:(congruence) ltac:(congruence) ltac:(congruence)
    eq_refl eq_refl workRoom sourceRoom) as execution.
  cbn [fillValues intValues] in execution. rewrite execution. cbn [optionBind fst snd]. rewrite withArray_work. reflexivity.
Qed.

Definition kernelStep index span :=
  tableRead arraydef_0__work (Z.of_nat index) >>= fun value =>
  tableWrite arraydef_0__other (Z.of_nat index) value >>= fun _ =>
  tableWrite arraydef_0__work (Z.of_nat index) 0 >>= fun _ =>
  if bool_decide ((index<S span)%nat) then
    tableRead arraydef_0__factorial (Z.of_nat span) >>= fun fact =>
    tableRead arraydef_0__inverseFactorial (Z.of_nat index) >>= fun inverse =>
    tableRead arraydef_0__inverseFactorial (Z.of_nat (span-index)) >>= fun complement =>
    tableWrite arraydef_0__work (Z.of_nat index)
      (machineProduct (machineProduct fact inverse) complement)
  else Done _ _ _ tt.
Fixpoint kernelAction fuel total span : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with O => Done _ _ _ tt | S fuel =>
    kernelStep (total-fuel-1) span >>= fun _ => kernelAction fuel total span end.
Definition kernelValue span index :=
  if bool_decide ((index<S span)%nat) then choose span index mod koxiaModulus else 0.

Lemma convolveKernelNormalized b nums total remaining span continuation :
  nums vardef_0__convolve_span=Z.of_nat span -> (remaining<total)%nat -> Z.of_nat span<koxiaModulus ->
  eliminateLocalVariables b nums (convolveKernelBody (Z.of_nat total) remaining >>= continuation)=
  kernelStep (total-remaining-1) span >>= fun _ =>
    eliminateLocalVariables b nums (continuation KeepGoing).
Proof.
  intros spanEq remainingBound spanBound. unfold koxiaModulus in spanBound.
  unfold convolveKernelBody,addInt,subInt,multInt,modIntUnsigned,numberLocalGet,retrieve,store.
  normalize_table_loop.
  assert (offsetId : Z.of_nat total-Z.of_nat remaining-1=Z.of_nat (total-remaining-1)) by lia.
  rewrite offsetId. unfold kernelStep,tableRead,tableWrite,machineProduct. cbn [bind].
  apply f_equal. apply functional_extensionality. intro value. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop.
  apply f_equal. apply functional_extensionality. intros []. normalize_table_loop. rewrite spanEq.
  rewrite coerce64_small by lia.
  replace (Z.of_nat span+1) with (Z.of_nat (S span)) by lia.
  rewrite <-bool_decide_nat_z.
  destruct (bool_decide ((total-remaining-1<S span)%nat)) eqn:inside.
  - apply bool_decide_eq_true in inside. normalize_table_loop. rewrite spanEq.
    apply f_equal. apply functional_extensionality. intro fact. normalize_table_loop.
    apply f_equal. apply functional_extensionality. intro inverse. normalize_table_loop. rewrite spanEq.
    rewrite coerce64_small by lia.
    assert (subtractId : Z.of_nat span-Z.of_nat (total-remaining-1)=Z.of_nat (span-(total-remaining-1))) by lia.
    rewrite subtractId. apply f_equal. apply functional_extensionality. intro complement.
    normalize_table_loop. reflexivity.
  - normalize_table_loop. reflexivity.
Qed.
Lemma convolveKernelLoopNormalized b nums fuel total span continuation :
  nums vardef_0__convolve_span=Z.of_nat span -> (fuel<=total)%nat -> Z.of_nat span<koxiaModulus ->
  eliminateLocalVariables b nums (loop fuel (convolveKernelBody (Z.of_nat total)) >>= continuation)=
  kernelAction fuel total span >>= fun _ => eliminateLocalVariables b nums (continuation tt).
Proof.
  intros spanEq fuelBound spanBound. induction fuel as [|fuel IH]; [reflexivity|].
  rewrite loop_S,<-bindAssoc,convolveKernelNormalized with (span:=span) by (try assumption; lia).
  cbn [kernelAction]. rewrite <-bindAssoc. apply f_equal. apply functional_extensionality. intros []. apply IH. lia.
Qed.

Lemma tableRead_execution name state index : name<>arraydef_0__frames ->
  (index<length (memory state name))%nat ->
  exec (tableRead name (Z.of_nat index)) state=Some (nth index (memory state name) (intValue name 0),state).
Proof. intros different room. unfold tableRead.
  rewrite (@execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 _ state name index (intValue name 0)) by exact room. reflexivity. Qed.
Lemma workRead_execution state values index : (index<length values)%nat ->
  exec (tableRead arraydef_0__work (Z.of_nat index)) (withWork state values)=
  Some (nth index values 0,withWork state values).
Proof. intro room. unfold tableRead. rewrite execReadWork by exact room. reflexivity. Qed.
Lemma workWrite_execution state values index value : (index<length values)%nat ->
  exec (tableWrite arraydef_0__work (Z.of_nat index) value) (withWork state values)=
  Some (tt,withWork state (<[index:=value]>values)).
Proof. intro room. unfold tableWrite. rewrite execStoreWork by exact room. reflexivity. Qed.

Lemma withArray_preserve_same (state : @Machine arrayIndex1 (arrayType _ environment1)) name values : memory (withArray state name values) name=values.
Proof. cbn [withArray withMemory memory]. apply replaceArray_same. Qed.
Lemma kernelStep_execution state values other index span :
  (index<length values)%nat -> (index<length other)%nat ->
  (span<length (memory state arraydef_0__factorial))%nat ->
  (span<length (memory state arraydef_0__inverseFactorial))%nat -> Z.of_nat span<koxiaModulus ->
  nth span (memory state arraydef_0__factorial) 0=factorialMod span ->
  (forall i, (i<=span)%nat -> nth i (memory state arraydef_0__inverseFactorial) 0=inverseFactorialMod i) ->
  exec (kernelStep index span) (withArray (withWork state values) arraydef_0__other other)=
  Some (tt,withArray (withWork state (<[index:=kernelValue span index]>values))
    arraydef_0__other (<[index:=nth index values 0%Z]>other)).
Proof.
  intros room otherRoom factRoom inverseRoom spanBound factCorrect inverseCorrect.
  unfold kernelStep. rewrite <-withArray_work. rewrite withArray_commute by congruence. rewrite withArray_work.
  rewrite exec_bind,workRead_execution by exact room. cbn [optionBind fst snd].
  rewrite <-withArray_work,withArray_commute by congruence.
  rewrite exec_bind.
  pose proof (integerWrite_execution arraydef_0__other (withArray state arraydef_0__work values) other index (nth index values 0) ltac:(congruence) otherRoom) as writeOther.
  cbn [intValues intValue] in writeOther. rewrite writeOther.
  cbn [optionBind fst snd]. rewrite withArray_commute by congruence. rewrite withArray_work.
  rewrite exec_bind,workWrite_execution by exact room. cbn [optionBind fst snd].
  destruct (bool_decide ((index<S span)%nat)) eqn:inside.
  - apply bool_decide_eq_true in inside.
    assert (factMemory : memory (withWork (withArray state arraydef_0__other (<[index:=nth index values 0%Z]>other))
      (<[index:=0%Z]>values)) arraydef_0__factorial=memory state arraydef_0__factorial).
    { rewrite <-withArray_work. rewrite !withArray_preserve_other by congruence. reflexivity. }
    assert (inverseMemory : memory (withWork (withArray state arraydef_0__other (<[index:=nth index values 0%Z]>other))
      (<[index:=0%Z]>values)) arraydef_0__inverseFactorial=memory state arraydef_0__inverseFactorial).
    { rewrite <-withArray_work. rewrite !withArray_preserve_other by congruence. reflexivity. }
    assert (factIndex : (span<length (memory (withWork (withArray state arraydef_0__other (<[index:=nth index values 0%Z]>other)) (<[index:=0%Z]>values)) arraydef_0__factorial))%nat) by (rewrite factMemory; exact factRoom).
    assert (inverseIndex : (index<length (memory (withWork (withArray state arraydef_0__other (<[index:=nth index values 0%Z]>other)) (<[index:=0%Z]>values)) arraydef_0__inverseFactorial))%nat) by (rewrite inverseMemory; lia).
    assert (complementIndex : ((span-index)<length (memory (withWork (withArray state arraydef_0__other (<[index:=nth index values 0%Z]>other)) (<[index:=0%Z]>values)) arraydef_0__inverseFactorial))%nat) by (rewrite inverseMemory; lia).
    rewrite exec_bind,tableRead_execution by (first [congruence|exact factIndex]).
    cbn [optionBind fst snd intValue].

    rewrite exec_bind,tableRead_execution by (first [congruence|exact inverseIndex|exact complementIndex]).
    cbn [optionBind fst snd intValue].
    rewrite exec_bind,tableRead_execution by (first [congruence|exact inverseIndex|exact complementIndex]).
    cbn [optionBind fst snd intValue].
    cbn [arrayType environment1] in *.
    rewrite factMemory,inverseMemory,factCorrect. rewrite !inverseCorrect by lia.
    unfold machineProduct. rewrite !residue_product_coerce.
    2: pose proof (factorialMod_positive span spanBound); lia.
    2: unfold inverseFactorialMod; apply modularPower_bounds.
    2: apply residue_bounds.
    2: unfold inverseFactorialMod; apply modularPower_bounds.
    rewrite factorial_binomial by (try assumption; lia).
    rewrite workWrite_execution by (rewrite length_insert; exact room).
    rewrite list_insert_insert,decide_True by reflexivity.
    unfold kernelValue. rewrite bool_decide_true by exact inside.
    rewrite <-withArray_work,withArray_commute by congruence. rewrite withArray_work. reflexivity.
  - unfold kernelValue. rewrite inside. cbn [exec].
    rewrite <-withArray_work,withArray_commute by congruence. rewrite withArray_work. reflexivity.
Qed.

Theorem kernelAction_execution fuel count total state values other span :
  (count+fuel=total)%nat -> (total<=length values)%nat -> (total<=length other)%nat ->
  (span<length (memory state arraydef_0__factorial))%nat ->
  (span<length (memory state arraydef_0__inverseFactorial))%nat -> Z.of_nat span<koxiaModulus ->
  nth span (memory state arraydef_0__factorial) 0=factorialMod span ->
  (forall i, (i<=span)%nat -> nth i (memory state arraydef_0__inverseFactorial) 0=inverseFactorialMod i) ->
  exec (kernelAction fuel total span)
    (withArray (withWork state (fillValues count values 0 (kernelValue span))) arraydef_0__other
      (fillValues count other 0 (fun i => nth i values 0)))=
  Some (tt,withArray (withWork state (fillValues total values 0 (kernelValue span))) arraydef_0__other
      (fillValues total other 0 (fun i => nth i values 0))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros countFuel room otherRoom factRoom inverseRoom spanBound factCorrect inverseCorrect.
    assert (count=total) by lia. subst count. reflexivity.
  - intros countFuel room otherRoom factRoom inverseRoom spanBound factCorrect inverseCorrect.
    cbn [kernelAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,kernelStep_execution.
    2: rewrite fillValues_length; lia.
    2: rewrite fillValues_length; lia.
    2: exact factRoom.
    2: exact inverseRoom.
    2: exact spanBound.
    2: exact factCorrect.
    2: exact inverseCorrect.
    cbn [optionBind fst snd]. rewrite fillValues_lookup,bool_decide_false by lia.
    pose proof (IH (S count) ltac:(lia) room otherRoom factRoom inverseRoom spanBound factCorrect inverseCorrect) as finish.
    cbn [fillValues Nat.add] in finish. exact finish.
Qed.

Lemma kernelValue_canonical span index : 0<=kernelValue span index<koxiaModulus.
Proof. unfold kernelValue. destruct bool_decide; [apply residue_bounds|pose proof modulus_positive; lia]. Qed.
