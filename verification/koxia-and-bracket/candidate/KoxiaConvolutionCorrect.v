From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaPolynomial KoxiaModular KoxiaArrays KoxiaRoots KoxiaFourier KoxiaBinomial KoxiaSizes KoxiaNTT KoxiaNTTCorrect KoxiaTables KoxiaArrayLoops KoxiaNegation KoxiaConvolution KoxiaConvolutionProgram KoxiaConvolutionMath KoxiaConvolutionSums KoxiaConvolutionExecution.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Opaque fastPower modularPower stageRoot stageInverse.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Local Existing Instance congruent_mul.
Definition arrayCoefficient (values : list Z) i := nth (Z.to_nat i) values 0.
Definition transformAgreement stage input output :=
  forall i, 0<=i<stageSize stage ->
    congruent (arrayCoefficient output i) (fourier stage (arrayCoefficient input) i).

Lemma transformValues_agreement stage (state : @Machine arrayIndex1 (arrayType _ environment1)) values :
  (stage<=20)%nat -> (sizeNat stage<=length values)%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  tableCanonical values -> tableCanonical (memory state arraydef_0__roots) ->
  (forall step, (step<stage)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  transformAgreement stage values (transformValues stage (memory state arraydef_0__roots) values).
Proof.
  intros bound room fit rootRoom rootFit canonical rootCanonical rootsCorrect i range.
  unfold arrayCoefficient. rewrite (transformValues_lookup stage state values (Z.to_nat i)) by
    (try assumption; rewrite stageSize_nat in range; lia).
  rewrite bool_decide_true by (rewrite stageSize_nat in range; lia).
  rewrite Z2Nat.id by lia. apply congruent_modulo.
Qed.
Lemma reflected_index size i : (0<size)%nat -> 0<=i<Z.of_nat size ->
  Z.of_nat ((size-Z.to_nat i) mod size)=(-i) mod Z.of_nat size.
Proof.
  intros positive range. rewrite Nat2Z.inj_mod,Nat2Z.inj_sub,Z2Nat.id by lia.
  replace (Z.of_nat size-i) with ((-i)+1*Z.of_nat size) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma congruent_productValue values other scale i :
  congruent (productValue values other scale (Z.to_nat i))
    (scale*(arrayCoefficient other i*arrayCoefficient values i)).
Proof.
  unfold productValue,arrayCoefficient.
  transitivity ((nth (Z.to_nat i) values 0*nth (Z.to_nat i) other 0) mod koxiaModulus*scale).
  - apply congruent_modulo.
  - transitivity (nth (Z.to_nat i) values 0*nth (Z.to_nat i) other 0*scale).
    + apply congruent_mul; [apply congruent_modulo|reflexivity].
    + apply congruent_equal. ring.
Qed.

Theorem three_transform_convolution stage left right first second output :
  (stage<=20)%nat -> (sizeNat stage<=length second)%nat ->
  transformAgreement stage left first -> transformAgreement stage right second ->
  transformAgreement stage
    (negatedValues ((sizeNat stage-1)/2)
      (fillValues (sizeNat stage) second 0 (productValue second first (stageInverse stage))) (sizeNat stage)) output ->
  forall index, 0<=index<stageSize stage ->
  congruent (arrayCoefficient output index)
    (cyclicConvolution stage (arrayCoefficient left) (arrayCoefficient right) index).
Proof.
  intros bound room firstCorrect secondCorrect outputCorrect index range.
  set (product := fillValues (sizeNat stage) second 0 (productValue second first (stageInverse stage))).
  set (negated := negatedValues ((sizeNat stage-1)/2) product (sizeNat stage)).
  assert (positive : (0<sizeNat stage)%nat).
  { pose proof (stageSize_positive stage) as positive. rewrite stageSize_nat in positive. lia. }
  transitivity (fourier stage (arrayCoefficient negated) index); [apply outputCorrect; exact range|].
  transitivity (fourier stage (fun i => stageInverse stage*
    (fourier stage (arrayCoefficient left) ((-i) mod stageSize stage)*
     fourier stage (arrayCoefficient right) ((-i) mod stageSize stage))) index).
  - apply fourier_congruent. intros i irange. unfold arrayCoefficient at 1. unfold negated.
    rewrite negatedValues_complete by (unfold product; rewrite ?fillValues_length; rewrite stageSize_nat in irange; lia).
    assert (negatedRange : (((sizeNat stage-Z.to_nat i) mod sizeNat stage)<sizeNat stage)%nat).
    { apply Nat.mod_upper_bound. lia. }
    unfold product. rewrite fillValues_lookup,bool_decide_true by lia.
    assert (indexId : Z.to_nat ((-i) mod stageSize stage)=((sizeNat stage-Z.to_nat i) mod sizeNat stage)%nat).
    { rewrite stageSize_nat. rewrite <-(reflected_index (sizeNat stage) i positive ltac:(rewrite <-stageSize_nat; exact irange)),Nat2Z.id. reflexivity. }
    replace (((sizeNat stage-Z.to_nat i) mod sizeNat stage)-0)%nat with
      ((sizeNat stage-Z.to_nat i) mod sizeNat stage)%nat by lia.
    rewrite <-indexId. transitivity (stageInverse stage*
      (arrayCoefficient first ((-i) mod stageSize stage)*arrayCoefficient second ((-i) mod stageSize stage))).
    + apply congruent_productValue.
    + apply congruent_mul; [reflexivity|]. apply congruent_mul.
      * apply firstCorrect,Z.mod_pos_bound,stageSize_positive.
      * apply secondCorrect,Z.mod_pos_bound,stageSize_positive.
  - rewrite fourier_scale.
    rewrite (fourier_reflect stage (fun i => fourier stage (arrayCoefficient left) i*fourier stage (arrayCoefficient right) i) index). change
      (congruent (inverseFourier stage (fun i => fourier stage (arrayCoefficient left) i*fourier stage (arrayCoefficient right) i) index)
        (cyclicConvolution stage (arrayCoefficient left) (arrayCoefficient right) index)).
    apply fourier_convolution; assumption.
Qed.

Lemma convolution_models_canonical stage state len skip span :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  (skip<=len<=length (memory state arraydef_0__poly))%nat ->
  tableCanonical (memory state arraydef_0__work) -> tableCanonical (memory state arraydef_0__other) ->
  tableCanonical (memory state arraydef_0__poly) ->
  tableCanonical (convolutionInput stage state len skip) /\
  tableCanonical (convolutionFirst stage state len skip) /\
  tableCanonical (convolutionOther stage state len skip) /\
  tableCanonical (convolutionKernel stage state len skip span) /\
  tableCanonical (convolutionSecond stage state len skip span) /\
  tableCanonical (convolutionProduct stage state len skip span) /\
  tableCanonical (convolutionNegated stage state len skip span) /\
  tableCanonical (convolutionOutput stage state len skip span).
Proof.
  intros workRoom polyRoom workCanonical otherCanonical polyCanonical.
  assert (sourceRoom : (skip+(len-skip)<=length (memory state arraydef_0__poly))%nat) by lia.
  assert (inputCanonical : tableCanonical (convolutionInput stage state len skip)).
  { unfold convolutionInput. apply fillValues_canonical; [exact workCanonical|intros; apply copyValue_canonical; assumption]. }
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
  assert (positive : (0<sizeNat stage)%nat).
  { pose proof (stageSize_positive stage) as positive. rewrite stageSize_nat in positive. lia. }
  assert (pairsBound : (2*((sizeNat stage-1)/2)<sizeNat stage)%nat).
  { pose proof (Nat.div_mod (sizeNat stage-1) 2 ltac:(lia)) as division.
    pose proof (Nat.mod_upper_bound (sizeNat stage-1) 2 ltac:(lia)) as remainder. lia. }
  assert (negatedCanonical : tableCanonical (convolutionNegated stage state len skip span)).
  { unfold convolutionNegated. apply negatedValues_canonical; [rewrite convolutionProduct_length; lia|exact productCanonical]. }
  assert (outputCanonical : tableCanonical (convolutionOutput stage state len skip span)).
  { unfold convolutionOutput. apply transformValues_canonical; [rewrite convolutionNegated_length; exact workRoom|exact negatedCanonical]. }
  repeat split; assumption.
Qed.

Theorem convolutionOutput_cyclic stage state len skip span index :
  (stage<=20)%nat -> (skip<=len<=length (memory state arraydef_0__poly))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__other))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__work))<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  tableCanonical (memory state arraydef_0__work) -> tableCanonical (memory state arraydef_0__other) ->
  tableCanonical (memory state arraydef_0__roots) -> tableCanonical (memory state arraydef_0__poly) ->
  (forall step, (step<stage)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  0<=index<stageSize stage ->
  congruent (arrayCoefficient (convolutionOutput stage state len skip span) index)
    (cyclicConvolution stage (arrayCoefficient (convolutionInput stage state len skip))
      (arrayCoefficient (convolutionKernel stage state len skip span)) index).
Proof.
  intros bound polyRoom workRoom otherRoom rootRoom workFit rootFit workCanonical otherCanonical rootCanonical polyCanonical
    rootsCorrect indexRange.
  destruct (convolution_models_canonical stage state len skip span workRoom polyRoom workCanonical otherCanonical polyCanonical)
    as [inputCanonical [firstCanonical [copiedCanonical [kernelCanonical [secondCanonical [productCanonical [negatedCanonical outputCanonical]]]]]]].
  apply (three_transform_convolution stage (convolutionInput stage state len skip)
    (convolutionKernel stage state len skip span) (convolutionOther stage state len skip)
    (convolutionSecond stage state len skip span) (convolutionOutput stage state len skip span)).
  - exact bound.
  - rewrite convolutionSecond_length. exact workRoom.
  - intros i range. unfold arrayCoefficient at 1,convolutionOther.
    assert (copyRoom : (0+sizeNat stage<=length (memory state arraydef_0__other))%nat) by lia.
    assert (iBound : (0<=Z.to_nat i<0+sizeNat stage)%nat) by (rewrite stageSize_nat in range; lia).
    rewrite fillValues_lookup by exact copyRoom. rewrite bool_decide_true by exact iBound.
    replace (Z.to_nat i-0)%nat with (Z.to_nat i) by lia.
    apply (transformValues_agreement stage state (convolutionInput stage state len skip));
      try assumption; rewrite ?convolutionInput_length; assumption.
  - unfold convolutionSecond. apply transformValues_agreement; try assumption;
      rewrite ?convolutionKernel_length; assumption.
  - change (transformAgreement stage (convolutionNegated stage state len skip span) (convolutionOutput stage state len skip span)).
    unfold convolutionOutput. apply transformValues_agreement; try assumption;
      rewrite ?convolutionNegated_length; assumption.
  - exact indexRange.
Qed.

Lemma convolutionInput_lookup stage state len skip i :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat -> 0<=i<stageSize stage ->
  arrayCoefficient (convolutionInput stage state len skip) i=
  copyValue (memory state arraydef_0__poly) skip (len-skip) (Z.to_nat i).
Proof.
  intros room range. assert (iBound : (0<=Z.to_nat i<0+sizeNat stage)%nat) by (rewrite stageSize_nat in range; lia).
  assert (fillRoom : (0+sizeNat stage<=length (memory state arraydef_0__work))%nat) by lia.
  unfold arrayCoefficient,convolutionInput. rewrite fillValues_lookup by exact fillRoom.
  rewrite bool_decide_true by exact iBound. replace (Z.to_nat i-0)%nat with (Z.to_nat i) by lia. reflexivity.
Qed.
Lemma convolutionKernel_lookup stage state len skip span i :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat -> 0<=i<stageSize stage ->
  arrayCoefficient (convolutionKernel stage state len skip span) i=kernelValue span (Z.to_nat i).
Proof.
  intros room range. assert (iBound : (0<=Z.to_nat i<0+sizeNat stage)%nat) by (rewrite stageSize_nat in range; lia).
  assert (fillRoom : (0+sizeNat stage<=length (convolutionFirst stage state len skip))%nat)
    by (rewrite convolutionFirst_length; lia).
  unfold arrayCoefficient,convolutionKernel. rewrite fillValues_lookup by exact fillRoom.
  rewrite bool_decide_true by exact iBound. replace (Z.to_nat i-0)%nat with (Z.to_nat i) by lia. reflexivity.
Qed.
Lemma convolutionInput_padding stage state len skip i :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  Z.of_nat (len-skip)<=i<stageSize stage -> arrayCoefficient (convolutionInput stage state len skip) i=0.
Proof.
  intros room range. rewrite convolutionInput_lookup by (try assumption; lia).
  unfold copyValue. rewrite bool_decide_false by lia. reflexivity.
Qed.
Lemma convolutionKernel_padding stage state len skip span i :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  Z.of_nat (S span)<=i<stageSize stage -> arrayCoefficient (convolutionKernel stage state len skip span) i=0.
Proof.
  intros room range. rewrite convolutionKernel_lookup by (try assumption; lia).
  unfold kernelValue. rewrite bool_decide_false by lia. reflexivity.
Qed.

Theorem convolutionOutput_linear stage state len skip span index :
  (stage<=20)%nat -> (skip<len<=length (memory state arraydef_0__poly))%nat ->
  (len-skip+span<=sizeNat stage)%nat ->
  (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__other))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__work))<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  tableCanonical (memory state arraydef_0__work) -> tableCanonical (memory state arraydef_0__other) ->
  tableCanonical (memory state arraydef_0__roots) -> tableCanonical (memory state arraydef_0__poly) ->
  (forall step, (step<stage)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  0<=index<stageSize stage ->
  arrayCoefficient (convolutionOutput stage state len skip span) index=
    linearConvolution (sizeNat stage) (sizeNat stage)
      (arrayCoefficient (convolutionInput stage state len skip))
      (arrayCoefficient (convolutionKernel stage state len skip span)) index mod koxiaModulus.
Proof.
  intros bound polyRoom countBound workRoom otherRoom rootRoom workFit rootFit workCanonical otherCanonical rootCanonical polyCanonical
    rootsCorrect indexRange.
  pose proof (convolutionOutput_cyclic stage state len skip span index bound ltac:(lia) workRoom otherRoom rootRoom workFit rootFit
    workCanonical otherCanonical rootCanonical polyCanonical rootsCorrect indexRange) as correctness.
  rewrite (zero_padded_convolution stage (arrayCoefficient (convolutionInput stage state len skip))
    (arrayCoefficient (convolutionKernel stage state len skip span)) (len-skip) (S span) index
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(intros; apply convolutionInput_padding; assumption)
    ltac:(intros; apply convolutionKernel_padding; assumption) indexRange) in correctness.
  unfold congruent in correctness. rewrite Z.mod_small in correctness.
  - exact correctness.
  - unfold arrayCoefficient. apply tableCanonical_nth.
    + destruct (convolution_models_canonical stage state len skip span workRoom ltac:(lia) workCanonical otherCanonical polyCanonical)
        as [_ [_ [_ [_ [_ [_ [_ outputCanonical]]]]]]]. exact outputCanonical.
    + rewrite convolutionOutput_length. rewrite stageSize_nat in indexRange. lia.
Qed.

Definition tailCoefficient (state : @Machine arrayIndex1 (arrayType _ environment1)) len skip i :=
  if bool_decide (0<=i<Z.of_nat (len-skip)) then nth (skip+Z.to_nat i) (memory state arraydef_0__poly) 0 else 0.
Lemma convolutionInput_tail stage state len skip i :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat -> 0<=i<stageSize stage ->
  arrayCoefficient (convolutionInput stage state len skip) i=tailCoefficient state len skip i.
Proof.
  intros room range. rewrite convolutionInput_lookup by assumption. unfold copyValue,tailCoefficient.
  destruct (bool_decide ((Z.to_nat i<len-skip)%nat)) eqn:inside.
  - apply bool_decide_eq_true in inside. rewrite bool_decide_true by lia. reflexivity.
  - apply bool_decide_eq_false in inside. rewrite bool_decide_false by lia. reflexivity.
Qed.
Lemma convolutionKernel_choose stage state len skip span i :
  (sizeNat stage<=length (memory state arraydef_0__work))%nat -> 0<=i<stageSize stage ->
  congruent (arrayCoefficient (convolutionKernel stage state len skip span) i) (choose span (Z.to_nat i)).
Proof.
  intros room range. rewrite convolutionKernel_lookup by assumption. unfold kernelValue.
  destruct (bool_decide ((Z.to_nat i<S span)%nat)) eqn:inside.
  - apply congruent_modulo.
  - apply bool_decide_eq_false in inside. rewrite choose_outside by lia. reflexivity.
Qed.
Lemma tailCoefficient_support state len skip width i : (len-skip<=width)%nat ->
  i<0 \/ Z.of_nat width<=i -> tailCoefficient state len skip i=0.
Proof. intros bound outside. unfold tailCoefficient. rewrite bool_decide_false by lia. reflexivity. Qed.

Theorem convolutionOutput_binomial stage state len skip span index :
  (stage<=20)%nat -> (skip<len<=length (memory state arraydef_0__poly))%nat ->
  (len-skip+span<=sizeNat stage)%nat ->
  (sizeNat stage<=length (memory state arraydef_0__work))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__other))%nat ->
  (sizeNat stage<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__work))<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  tableCanonical (memory state arraydef_0__work) -> tableCanonical (memory state arraydef_0__other) ->
  tableCanonical (memory state arraydef_0__roots) -> tableCanonical (memory state arraydef_0__poly) ->
  (forall step, (step<stage)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  0<=index<stageSize stage ->
  arrayCoefficient (convolutionOutput stage state len skip span) index=
    binomialTransform span (tailCoefficient state len skip) index mod koxiaModulus.
Proof.
  intros bound polyRoom countBound workRoom otherRoom rootRoom workFit rootFit workCanonical otherCanonical rootCanonical polyCanonical
    rootsCorrect indexRange.
  pose proof (convolutionOutput_linear stage state len skip span index bound polyRoom countBound workRoom otherRoom rootRoom workFit rootFit
    workCanonical otherCanonical rootCanonical polyCanonical rootsCorrect indexRange) as actual.
  pose proof (linearConvolution_congruent (sizeNat stage) (sizeNat stage)
    (arrayCoefficient (convolutionInput stage state len skip)) (arrayCoefficient (convolutionKernel stage state len skip span))
    (tailCoefficient state len skip) (fun j => nth (Z.to_nat j) (binomialRow span) 0) index
    ltac:(intros i range; apply congruent_equal,convolutionInput_tail; [exact workRoom|rewrite stageSize_nat; exact range])
    ltac:(intros j range; apply convolutionKernel_choose; [exact workRoom|rewrite stageSize_nat; exact range])) as related.
  rewrite finite_linear_convolution in related.
  2: rewrite binomialRow_length; lia.
  2: intros; apply tailCoefficient_support with (width:=sizeNat stage); [lia|assumption].
  rewrite <-binomialTransform_convolution in related. unfold congruent in related. rewrite actual. exact related.
Qed.

Theorem generated_convolve_correct b nums state len skip span base :
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
  (forall step, (step<ceilingStage 20 (Z.of_nat (len-skip+span)) 0)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  exists final, exec (funcdef_0__convolve b nums) state=Some (tt,final) /\
    (forall index, (index<len-skip+span)%nat ->
      nth (base+index) (memory final arraydef_0__arena) 0=
        binomialTransform span (tailCoefficient state len skip) (Z.of_nat index) mod koxiaModulus) /\
    stdin final=stdin state /\ stdout final=stdout state.
Proof.
  intros lenEq skipEq spanEq baseEq polyRoom lenBound countBound arenaFit workRoom otherRoom rootRoom workFit rootFit
    factRoom inverseRoom factCorrect inverseCorrect workCanonical otherCanonical rootCanonical polyCanonical resultRoom arenaRoom rootsCorrect.
  set (stage := ceilingStage 20 (Z.of_nat (len-skip+span)) 0).
  exists (convolutionFinal stage (len-skip+span) state len skip span base). split.
  - apply generated_convolve_execution; assumption.
  - split.
    + intros index indexBound. unfold convolutionFinal. rewrite withArray_preserve_same.
      assert (fillRoom : (base+(len-skip+span)<=length (memory state arraydef_0__arena))%nat) by exact arenaRoom.
      assert (addressRange : (base<=base+index<base+(len-skip+span))%nat) by lia.
      rewrite fillValues_lookup by exact fillRoom. rewrite bool_decide_true by exact addressRange.
      replace (base+index-base)%nat with index by lia.
      rewrite <-(Nat2Z.id index) at 1.
      change (arrayCoefficient (convolutionOutput stage state len skip span) (Z.of_nat index)=
        binomialTransform span (tailCoefficient state len skip) (Z.of_nat index) mod koxiaModulus).
      pose proof (ceilingStage_correct (Z.of_nat (len-skip+span)) ltac:(lia)) as [stageBound sizes].
      fold stage in stageBound,sizes.
      apply convolutionOutput_binomial; try assumption.
      * rewrite stageSize_nat in sizes. lia.
      * rewrite stageSize_nat. rewrite stageSize_nat in sizes. lia.
    + split; reflexivity.
Qed.
