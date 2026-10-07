From CoqCP Require Import Options Imperative Execution KoxiaArrays KoxiaPolynomial KoxiaArrayLoops KoxiaModular KoxiaRoots KoxiaFourier KoxiaBinomial KoxiaSizes
  KoxiaTables KoxiaConvolution KoxiaNTTCorrect KoxiaConvolutionExecution KoxiaConvolutionCorrect.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Lia.
Local Open Scope Z_scope.
Local Opaque funcdef_0__convolve funcdef_0__ntt funcdef_0__power modularPower stageRoot stageInverse convolutionOutput.
(* A memory invariant, containing no assumption about executing a program. *)
Record ConvolutionReady (state : @Machine arrayIndex1 (arrayType _ environment1)) len cut span base : Prop := {
  ready_poly_room : (cut<len<=length (memory state arraydef_0__poly))%nat;
  ready_length_bound : Z.of_nat len<koxiaModulus;
  ready_count_bound : 0<Z.of_nat (len-cut+span)<=1048576;
  ready_arena_fit : Z.of_nat (base+(len-cut+span))<18446744073709551616;
  ready_work_room : (sizeNat (ceilingStage 20 (Z.of_nat (len-cut+span)) 0)<=length (memory state arraydef_0__work))%nat;
  ready_other_room : (sizeNat (ceilingStage 20 (Z.of_nat (len-cut+span)) 0)<=length (memory state arraydef_0__other))%nat;
  ready_roots_room : (sizeNat (ceilingStage 20 (Z.of_nat (len-cut+span)) 0)<=length (memory state arraydef_0__roots))%nat;
  ready_work_fit : Z.of_nat (length (memory state arraydef_0__work))<18446744073709551616;
  ready_roots_fit : Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616;
  ready_factorial_room : (span<length (memory state arraydef_0__factorial))%nat;
  ready_inverse_room : (span<length (memory state arraydef_0__inverseFactorial))%nat;
  ready_factorial : nth span (memory state arraydef_0__factorial) 0=factorialMod span;
  ready_inverse : forall i, (i<=span)%nat -> nth i (memory state arraydef_0__inverseFactorial) 0=inverseFactorialMod i;
  ready_work_canonical : tableCanonical (memory state arraydef_0__work);
  ready_other_canonical : tableCanonical (memory state arraydef_0__other);
  ready_roots_canonical : tableCanonical (memory state arraydef_0__roots);
  ready_poly_canonical : tableCanonical (memory state arraydef_0__poly);
  ready_result_room : (2<length (memory state arraydef_0__result))%nat;
  ready_arena_room : (base+(len-cut+span)<=length (memory state arraydef_0__arena))%nat;
  ready_roots : forall step, (step<ceilingStage 20 (Z.of_nat (len-cut+span)) 0)%nat ->
    rootTableCorrect (memory state arraydef_0__roots) step
}.
Definition readyConvolutionFinal state len cut span base :=
  convolutionFinal (ceilingStage 20 (Z.of_nat (len-cut+span)) 0) (len-cut+span) state len cut span base.
Theorem ready_convolution_execution state len cut span base b nums :
  ConvolutionReady state len cut span base ->
  nums vardef_0__convolve_length=Z.of_nat len -> nums vardef_0__convolve_skip=Z.of_nat cut ->
  nums vardef_0__convolve_span=Z.of_nat span -> nums vardef_0__convolve_base=Z.of_nat base ->
  exec (funcdef_0__convolve b nums) state=Some (tt,readyConvolutionFinal state len cut span base).
Proof. intros ready lenEq cutEq spanEq baseEq. destruct ready. unfold readyConvolutionFinal. apply generated_convolve_execution with (len:=len) (skip:=cut) (span:=span) (base:=base); assumption. Qed.
Theorem ready_convolution_coefficients state len cut span base :
  ConvolutionReady state len cut span base -> forall index, (index<len-cut+span)%nat ->
  nth (base+index) (memory (readyConvolutionFinal state len cut span base) arraydef_0__arena) 0=
    binomialTransform span (tailCoefficient state len cut) (Z.of_nat index) mod koxiaModulus.
Proof.
  intros ready index indexBound. unfold readyConvolutionFinal,convolutionFinal. rewrite withArray_preserve_same.
  destruct ready as [polyRoom lengthBound countBound arenaFit workRoom otherRoom rootsRoom workFit rootsFit factRoom inverseRoom factorial inverse workCanonical otherCanonical rootsCanonical polyCanonical resultRoom arenaRoom rootsCorrect].
  rewrite fillValues_lookup by exact arenaRoom.
  rewrite bool_decide_true by lia. replace (base+index-base)%nat with index by lia.
  rewrite <-(Nat2Z.id index) at 1.
  change (arrayCoefficient (convolutionOutput (ceilingStage 20 (Z.of_nat (len-cut+span)) 0) state len cut span) (Z.of_nat index)=
    binomialTransform span (tailCoefficient state len cut) (Z.of_nat index) mod koxiaModulus).
  apply convolutionOutput_binomial; try assumption.
  - apply (proj1 (ceilingStage_correct (Z.of_nat (len-cut+span)) ltac:(lia))).
  - pose proof (ceilingStage_correct (Z.of_nat (len-cut+span)) ltac:(lia)) as [bound sizes]. rewrite stageSize_nat in sizes. lia.
  - pose proof (ceilingStage_correct (Z.of_nat (len-cut+span)) ltac:(lia)) as [bound sizes]. rewrite stageSize_nat in sizes |- *. lia.
Qed.
