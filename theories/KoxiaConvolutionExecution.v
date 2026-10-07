From CoqCP Require Import Options Imperative Execution KoxiaModular KoxiaIntegers
  KoxiaPower KoxiaArrays KoxiaRoots KoxiaFourier KoxiaRadix KoxiaNTT KoxiaNTTButterflies
  KoxiaNTTCorrect KoxiaBinomial KoxiaTables KoxiaTableLoops KoxiaArrayLoops KoxiaSizes
  KoxiaNegation KoxiaConvolution KoxiaConvolutionProgram KoxiaConvolutionMath SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque fastPower modularPower stageRoot stageInverse funcdef_0__ntt funcdef_0__power.
Definition transformValues stage roots values :=
  transformStages stage stage (reverseWork stage (sizeNat stage) values) roots.
Lemma transformValues_length stage roots values : length (transformValues stage roots values)=length values.
Proof. unfold transformValues. rewrite transformStages_length,reverseWork_length. reflexivity. Qed.
Lemma transformValues_canonical stage roots values : (sizeNat stage<=length values)%nat ->
  tableCanonical values -> tableCanonical (transformValues stage roots values).
Proof. intros room canonical. unfold transformValues. apply transformStages_canonical,reverseWork_canonical_full; assumption. Qed.
Lemma transformCall_execution stage state values :
  (stage<=20)%nat -> (sizeNat stage<=length values)%nat -> Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__roots) ->
  exec (transformCall stage) (withWork state values)=
    Some (tt,withWork state (transformValues stage (memory state arraydef_0__roots) values)).
Proof.
  intros bound room fit rootRoom rootFit canonical rootCanonical. unfold transformCall,transformValues.
  apply generated_ntt_execution; try assumption.
  - apply lookupSame.
  - rewrite lookupDifferent by congruence. reflexivity.
Qed.
Local Transparent stageInverse modularPower fastPower.
Lemma inverseSizeCall_execution stage state : (stage<=20)%nat ->
  (2<length (memory state arraydef_0__result))%nat ->
  exec (inverseSizeCall stage) state=Some (tt,withResult state (stageInverse stage)).
Proof.
  intros bound room. unfold inverseSizeCall. rewrite generated_power_execution.
  - rewrite lookupDifferent by congruence. rewrite !lookupSame.
    unfold withResult,stageInverse,modularPower. rewrite fastPower_correct.
    + rewrite Z.mul_1_l. reflexivity.
    + pose proof modulus_positive. unfold koxiaModulus; change (0<=998244351<18446744073709551616); lia.
    + unfold koxiaModulus; lia.
  - rewrite lookupDifferent by congruence. rewrite lookupSame.
    pose proof (stageSize_positive stage) as positive. pose proof (stageSize_bound stage bound) as sizeBound. unfold koxiaModulus; lia.
  - rewrite lookupSame. change (0<=998244351<18446744073709551616); lia.
  - exact room.
Qed.

Local Opaque fastPower modularPower stageInverse.

Local Transparent stageInverse.
Lemma stageInverse_canonical stage : 0<=stageInverse stage<koxiaModulus.
Proof. unfold stageInverse. apply modularPower_bounds. Qed.
Local Opaque stageInverse.
Lemma withResult_withArray (state : @Machine arrayIndex1 (arrayType _ environment1)) name values value :
  name<>arraydef_0__result ->
  withResult (withArray state name values) value=withArray (withResult state value) name values.
Proof. intro different. unfold withResult. apply withArray_store_other. exact different. Qed.
Lemma withResult_withWork state values value : withResult (withWork state values) value=withWork (withResult state value) values.
Proof. rewrite <-!withArray_work. apply withResult_withArray. congruence. Qed.
Lemma withWork_memory state values : memory (withWork state values) arraydef_0__work=values.
Proof. reflexivity. Qed.
Lemma withWork_other state values name : name<>arraydef_0__work ->
  memory (withWork state values) name=memory state name.
Proof. intro different. rewrite <-withArray_work. apply withArray_preserve_other. exact different. Qed.
Lemma withArray_other_self state values name : name<>arraydef_0__work ->
  withArray (withWork state values) name (memory state name)=withWork state values.
Proof. intro different. pose proof (withArray_self (withWork state values) name) as self.
  rewrite withWork_other in self by exact different. exact self. Qed.
Definition convolutionInput stage (state : @Machine arrayIndex1 (arrayType _ environment1)) len skip :=
  fillValues (sizeNat stage) (memory state arraydef_0__work) 0 (copyValue (memory state arraydef_0__poly) skip (len-skip)).
Definition convolutionFirst stage state len skip :=
  transformValues stage (memory state arraydef_0__roots) (convolutionInput stage state len skip).
Definition convolutionOther stage state len skip :=
  fillValues (sizeNat stage) (memory state arraydef_0__other) 0 (fun i => nth i (convolutionFirst stage state len skip) 0).
Definition convolutionKernel stage state len skip span :=
  fillValues (sizeNat stage) (convolutionFirst stage state len skip) 0 (kernelValue span).
Definition convolutionSecond stage state len skip span :=
  transformValues stage (memory state arraydef_0__roots) (convolutionKernel stage state len skip span).
Definition convolutionProduct stage state len skip span :=
  fillValues (sizeNat stage) (convolutionSecond stage state len skip span) 0
    (productValue (convolutionSecond stage state len skip span) (convolutionOther stage state len skip) (stageInverse stage)).
Definition convolutionNegated stage state len skip span :=
  negatedValues ((sizeNat stage-1)/2) (convolutionProduct stage state len skip span) (sizeNat stage).
Definition convolutionOutput stage state len skip span :=
  transformValues stage (memory state arraydef_0__roots) (convolutionNegated stage state len skip span).
Definition convolutionFinal stage count state len skip span base :=
  withArray (withWork
    (withArray (withResult state (stageInverse stage)) arraydef_0__other (convolutionOther stage state len skip))
    (convolutionOutput stage state len skip span)) arraydef_0__arena
    (fillValues count (memory state arraydef_0__arena) base (fun i => nth i (convolutionOutput stage state len skip span) 0)).
Lemma convolutionInput_length stage state len skip : length (convolutionInput stage state len skip)=length (memory state arraydef_0__work).
Proof. unfold convolutionInput. apply fillValues_length. Qed.
Lemma convolutionFirst_length stage state len skip : length (convolutionFirst stage state len skip)=length (memory state arraydef_0__work).
Proof. unfold convolutionFirst. rewrite transformValues_length,convolutionInput_length. reflexivity. Qed.
Lemma convolutionOther_length stage state len skip : length (convolutionOther stage state len skip)=length (memory state arraydef_0__other).
Proof. unfold convolutionOther. apply fillValues_length. Qed.
Lemma convolutionKernel_length stage state len skip span : length (convolutionKernel stage state len skip span)=length (memory state arraydef_0__work).
Proof. unfold convolutionKernel. rewrite fillValues_length,convolutionFirst_length. reflexivity. Qed.
Lemma convolutionSecond_length stage state len skip span : length (convolutionSecond stage state len skip span)=length (memory state arraydef_0__work).
Proof. unfold convolutionSecond. rewrite transformValues_length,convolutionKernel_length. reflexivity. Qed.
Lemma convolutionProduct_length stage state len skip span : length (convolutionProduct stage state len skip span)=length (memory state arraydef_0__work).
Proof. unfold convolutionProduct. rewrite fillValues_length,convolutionSecond_length. reflexivity. Qed.
Lemma convolutionNegated_length stage state len skip span : length (convolutionNegated stage state len skip span)=length (memory state arraydef_0__work).
Proof. unfold convolutionNegated. rewrite negatedValues_length,convolutionProduct_length. reflexivity. Qed.
Lemma convolutionOutput_length stage state len skip span : length (convolutionOutput stage state len skip span)=length (memory state arraydef_0__work).
Proof. unfold convolutionOutput. rewrite transformValues_length,convolutionNegated_length. reflexivity. Qed.

Theorem convolutionAction_execution stage count state len skip span base tmp :
  (stage<=20)%nat -> (skip<=len<=length (memory state arraydef_0__poly))%nat ->
  (count<=sizeNat stage)%nat -> (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__other))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__work))<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  (span<length (memory state arraydef_0__factorial))%nat ->
  (span<length (memory state arraydef_0__inverseFactorial))%nat -> Z.of_nat span<koxiaModulus ->
  nth span (memory state arraydef_0__factorial) 0=factorialMod span ->
  (forall i, (i<=span)%nat -> nth i (memory state arraydef_0__inverseFactorial) 0=inverseFactorialMod i) ->
  tableCanonical (memory state arraydef_0__work) -> tableCanonical (memory state arraydef_0__other) ->
  tableCanonical (memory state arraydef_0__roots) -> tableCanonical (memory state arraydef_0__poly) ->
  (2<length (memory state arraydef_0__result))%nat -> (base+count<=length (memory state arraydef_0__arena))%nat ->
  exec (convolutionAction stage count len skip span base tmp) state=
  Some (tt,convolutionFinal stage count state len skip span base).
Proof.
  intros stageBound polyRoom countBound workRoom otherRoom rootRoom workFit rootFit factRoom inverseRoom spanBound
    factCorrect inverseCorrect workCanonical otherCanonical rootCanonical polyCanonical resultRoom arenaRoom.
  assert (sourceRoom : (skip+(len-skip)<=length (memory state arraydef_0__poly))%nat) by lia.
  assert (inputCanonical : tableCanonical (convolutionInput stage state len skip)).
  { unfold convolutionInput. apply fillValues_canonical; [exact workCanonical|]. intros i indexBound.
    apply copyValue_canonical; assumption. }
  assert (firstCanonical : tableCanonical (convolutionFirst stage state len skip)).
  { unfold convolutionFirst. apply transformValues_canonical; [rewrite convolutionInput_length; exact workRoom|exact inputCanonical]. }
  assert (kernelCanonical : tableCanonical (convolutionKernel stage state len skip span)).
  { unfold convolutionKernel. apply fillValues_canonical; [exact firstCanonical|intros; apply kernelValue_canonical]. }
  assert (secondCanonical : tableCanonical (convolutionSecond stage state len skip span)).
  { unfold convolutionSecond. apply transformValues_canonical; [rewrite convolutionKernel_length; exact workRoom|exact kernelCanonical]. }
  assert (copiedCanonical : tableCanonical (convolutionOther stage state len skip)).
  { unfold convolutionOther. apply fillValues_canonical; [exact otherCanonical|]. intros i indexBound.
    apply tableCanonical_nth; [exact firstCanonical|rewrite convolutionFirst_length; lia]. }
  assert (productCanonical : tableCanonical (convolutionProduct stage state len skip span)).
  { unfold convolutionProduct. apply fillValues_canonical; [exact secondCanonical|intros; unfold productValue; apply residue_bounds]. }
  assert (sizePositive : (0<sizeNat stage)%nat).
  { pose proof (stageSize_positive stage) as positive. rewrite stageSize_nat in positive. lia. }
  assert (pairsBound : (2*((sizeNat stage-1)/2)<sizeNat stage)%nat).
  { pose proof (Nat.div_mod (sizeNat stage-1) 2 ltac:(lia)) as division.
    pose proof (Nat.mod_upper_bound (sizeNat stage-1) 2 ltac:(lia)) as remainder. lia. }
  assert (negatedCanonical : tableCanonical (convolutionNegated stage state len skip span)).
  { unfold convolutionNegated. apply negatedValues_canonical; [rewrite convolutionProduct_length; lia|exact productCanonical]. }
  unfold convolutionAction. rewrite exec_bind.
  pose proof (copyAction_execution (sizeNat stage) 0 (sizeNat stage) arraydef_0__work arraydef_0__poly state
    (memory state arraydef_0__work) (memory state arraydef_0__poly) skip (len-skip)
    ltac:(congruence) ltac:(congruence) ltac:(congruence) eq_refl eq_refl workRoom sourceRoom) as copied.
  cbn [intValues fillValues] in copied. rewrite withArray_self in copied.
  rewrite copied. cbn [optionBind fst snd]. rewrite withArray_work. fold (convolutionInput stage state len skip).
  rewrite exec_bind,transformCall_execution.
  2: exact stageBound.
  2: rewrite convolutionInput_length; exact workRoom.
  2: rewrite convolutionInput_length; exact workFit.
  2: exact rootRoom.
  2: exact rootFit.
  2: exact inputCanonical.
  2: exact rootCanonical.
  cbn [optionBind fst snd]. fold (convolutionFirst stage state len skip).
  rewrite exec_bind.
  pose proof (kernelAction_execution (sizeNat stage) 0 (sizeNat stage) state
    (convolutionFirst stage state len skip) (memory state arraydef_0__other) span eq_refl
    ltac:(rewrite convolutionFirst_length; exact workRoom) otherRoom factRoom inverseRoom spanBound factCorrect inverseCorrect) as kernelExecution.
  cbn [fillValues] in kernelExecution. rewrite withArray_other_self in kernelExecution by congruence.
  rewrite kernelExecution. cbn [optionBind fst snd].
  fold (convolutionKernel stage state len skip span) (convolutionOther stage state len skip).
  rewrite <-withArray_work,withArray_commute by congruence. rewrite withArray_work.
  rewrite exec_bind,transformCall_execution.
  2: exact stageBound.
  2: rewrite convolutionKernel_length; exact workRoom.
  2: rewrite convolutionKernel_length; exact workFit.
  2: rewrite withArray_preserve_other by congruence; exact rootRoom.
  2: rewrite withArray_preserve_other by congruence; exact rootFit.
  2: exact kernelCanonical.
  2: rewrite withArray_preserve_other by congruence; exact rootCanonical.
  cbn [optionBind fst snd]. rewrite withArray_preserve_other by congruence.
  fold (convolutionSecond stage state len skip span).
  rewrite exec_bind,inverseSizeCall_execution.
  2: exact stageBound.
  2: rewrite withWork_other,withArray_preserve_other by congruence; exact resultRoom.
  cbn [optionBind fst snd]. rewrite withResult_withWork,withResult_withArray by congruence.
  replace (tableRead arraydef_0__result 2) with (tableRead arraydef_0__result (Z.of_nat 2)) by reflexivity.
  rewrite exec_bind,tableRead_execution.
  2: congruence.
  2: rewrite withWork_other,withArray_preserve_other by congruence; rewrite withResult_memory,length_insert; exact resultRoom.
  cbn [optionBind fst snd intValue].
  rewrite withWork_other,withArray_preserve_other by congruence.
  rewrite withResult_memory,nthUpdate by exact resultRoom.
  rewrite exec_bind.
  pose proof (productAction_execution (sizeNat stage) 0 (sizeNat stage)
    (withArray (withResult state (stageInverse stage)) arraydef_0__other (convolutionOther stage state len skip))
    (convolutionSecond stage state len skip span) (stageInverse stage) eq_refl
    ltac:(rewrite convolutionSecond_length; exact workRoom)
    ltac:(rewrite withArray_preserve_same,convolutionOther_length; exact otherRoom)
    secondCanonical ltac:(rewrite withArray_preserve_same; exact copiedCanonical)
    ltac:(apply stageInverse_canonical)) as multiplied.
  cbn [fillValues] in multiplied. rewrite withArray_preserve_same in multiplied.
  rewrite multiplied. cbn [optionBind fst snd]. fold (convolutionProduct stage state len skip span).
  rewrite exec_bind.
  destruct (negateAction_execution ((sizeNat stage-1)/2) 0 ((sizeNat stage-1)/2) (sizeNat stage) tmp
    (withArray (withResult state (stageInverse stage)) arraydef_0__other (convolutionOther stage state len skip))
    (convolutionProduct stage state len skip span) eq_refl
    ltac:(rewrite convolutionProduct_length; lia)) as [saved negated].
  cbn [negatedValues] in negated. rewrite negated. cbn [optionBind fst snd].
  fold (convolutionNegated stage state len skip span).
  rewrite exec_bind,transformCall_execution.
  2: exact stageBound.
  2: rewrite convolutionNegated_length; exact workRoom.
  2: rewrite convolutionNegated_length; exact workFit.
  2: rewrite withArray_preserve_other by congruence; rewrite withResult_other by congruence; exact rootRoom.
  2: rewrite withArray_preserve_other by congruence; rewrite withResult_other by congruence; exact rootFit.
  2: exact negatedCanonical.
  2: rewrite withArray_preserve_other by congruence; rewrite withResult_other by congruence; exact rootCanonical.
  cbn [optionBind fst snd]. rewrite withArray_preserve_other by congruence. rewrite withResult_other by congruence.
  fold (convolutionOutput stage state len skip span).
  pose proof (copyIntoAction_execution count 0 count arraydef_0__arena arraydef_0__work
    (withWork (withArray (withResult state (stageInverse stage)) arraydef_0__other (convolutionOther stage state len skip))
      (convolutionOutput stage state len skip span))
    (memory state arraydef_0__arena) (convolutionOutput stage state len skip span) base 0
    ltac:(congruence) ltac:(congruence) ltac:(congruence) eq_refl eq_refl arenaRoom
    ltac:(rewrite convolutionOutput_length; lia)) as savedOutput.
  cbn [fillValues intValues Nat.add] in savedOutput.
  assert (arenaMemory : memory
    (withWork (withArray (withResult state (stageInverse stage)) arraydef_0__other (convolutionOther stage state len skip))
      (convolutionOutput stage state len skip span)) arraydef_0__arena=memory state arraydef_0__arena).
  { rewrite withWork_other,withArray_preserve_other,withResult_other by congruence. reflexivity. }
  rewrite <-arenaMemory,withArray_self in savedOutput. rewrite arenaMemory in savedOutput.
  exact savedOutput.
Qed.

Theorem transformValues_lookup stage (state : @Machine arrayIndex1 (arrayType _ environment1)) values index :
  (stage<=20)%nat -> (sizeNat stage<=length values)%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__roots) ->
  (forall step, (step<stage)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  (index<length values)%nat ->
  nth index (transformValues stage (memory state arraydef_0__roots) values) 0=
    if bool_decide ((index<sizeNat stage)%nat) then
      fourier stage (fun i => nth (Z.to_nat i) values 0) (Z.of_nat index) mod koxiaModulus
    else nth index values 0.
Proof.
  intros bound room fit rootRoom rootFit canonical rootCanonical rootsCorrect indexBound.
  destruct (generated_ntt_complete stage state values (fun _ => false)
    (update (fun _ => 0) vardef_0__ntt_size (stageSize stage)) bound room fit rootRoom rootFit canonical rootCanonical rootsCorrect
    ltac:(apply lookupSame) ltac:(rewrite lookupDifferent by congruence; reflexivity))
    as [transformed [execution [lengthEq [outputCanonical lookup]]]].
  pose proof (transformCall_execution stage state values bound room fit rootRoom rootFit canonical rootCanonical) as actual.
  unfold transformCall in actual. rewrite actual in execution.
  injection execution as same. apply (f_equal (fun m => m arraydef_0__work)) in same.
  cbn [workMemory] in same. cbn [arrayType environment1] in *. rewrite same. apply lookup. exact indexBound.
Qed.

Lemma convolutionFinal_preserves stage count state len skip span base name :
  name<>arraydef_0__work -> name<>arraydef_0__other -> name<>arraydef_0__result -> name<>arraydef_0__arena ->
  memory (convolutionFinal stage count state len skip span base) name=memory state name.
Proof.
  intros notWork notOther notResult notArena. unfold convolutionFinal.
  rewrite withArray_preserve_other by exact notArena. rewrite withWork_other by exact notWork.
  rewrite withArray_preserve_other by exact notOther. apply withResult_other. exact notResult.
Qed.
Lemma convolutionFinal_stdout stage count state len skip span base :
  stdout (convolutionFinal stage count state len skip span base)=stdout state.
Proof. reflexivity. Qed.
Lemma convolutionFinal_stdin stage count state len skip span base :
  stdin (convolutionFinal stage count state len skip span base)=stdin state.
Proof. reflexivity. Qed.

Theorem generated_convolve_execution b nums state len skip span base :
  nums vardef_0__convolve_length=Z.of_nat len -> nums vardef_0__convolve_skip=Z.of_nat skip ->
  nums vardef_0__convolve_span=Z.of_nat span -> nums vardef_0__convolve_base=Z.of_nat base ->
  (skip<len<=length (memory state arraydef_0__poly))%nat -> Z.of_nat len<koxiaModulus ->
  0<Z.of_nat (len-skip+span)<=1048576 -> Z.of_nat (base+(len-skip+span))<18446744073709551616 ->
  (sizeNat (ceilingStage 20 (Z.of_nat (len-skip+span)) 0)<=length (memory state arraydef_0__work))%nat ->
  (sizeNat (ceilingStage 20 (Z.of_nat (len-skip+span)) 0)<=length (memory state arraydef_0__other))%nat ->
  (sizeNat (ceilingStage 20 (Z.of_nat (len-skip+span)) 0)<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__work))<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  (span<length (memory state arraydef_0__factorial))%nat ->
  (span<length (memory state arraydef_0__inverseFactorial))%nat ->
  nth span (memory state arraydef_0__factorial) 0=factorialMod span ->
  (forall i, (i<=span)%nat -> nth i (memory state arraydef_0__inverseFactorial) 0=inverseFactorialMod i) ->
  tableCanonical (memory state arraydef_0__work) -> tableCanonical (memory state arraydef_0__other) ->
  tableCanonical (memory state arraydef_0__roots) -> tableCanonical (memory state arraydef_0__poly) ->
  (2<length (memory state arraydef_0__result))%nat ->
  (base+(len-skip+span)<=length (memory state arraydef_0__arena))%nat ->
  exec (funcdef_0__convolve b nums) state=
  Some (tt,convolutionFinal (ceilingStage 20 (Z.of_nat (len-skip+span)) 0) (len-skip+span) state len skip span base).
Proof.
  intros lenEq skipEq spanEq baseEq polyRoom lenBound countBound arenaFit workRoom otherRoom rootRoom workFit rootFit
    factRoom inverseRoom factCorrect inverseCorrect workCanonical otherCanonical rootCanonical polyCanonical resultRoom arenaRoom.
  rewrite generated_convolve_normalized with (len:=len) (skip:=skip) (span:=span) (base:=base) by (try assumption; lia).
  pose proof (ceilingStage_correct (Z.of_nat (len-skip+span)) ltac:(lia)) as [stageBound sizes].
  apply convolutionAction_execution; try assumption.
  - lia.
  - rewrite stageSize_nat in sizes. lia.
  - unfold koxiaModulus. lia.
Qed.
