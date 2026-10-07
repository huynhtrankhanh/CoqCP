From CoqCP Require Import Options Imperative Execution KoxiaModular KoxiaIntegers
  KoxiaPower KoxiaArrays KoxiaRoots KoxiaFourier KoxiaRadix KoxiaNTT KoxiaNTTButterflies
  KoxiaNTTCorrect KoxiaBinomial KoxiaTables KoxiaTableLoops KoxiaArrayLoops KoxiaSizes
  KoxiaNegation KoxiaConvolution SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_table_steps.
Definition convolveGet := numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve.
Definition convolveSet := numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve.
Definition convolveNtt :=
  convolveGet vardef_0__convolve_size >>= fun size =>
  liftToWithLocalVariables (funcdef_0__ntt (fun _ => false) (update (fun _ => 0) vardef_0__ntt_size size)).
Definition convolvePower :=
  convolveGet vardef_0__convolve_size >>= fun size =>
  liftToWithLocalVariables (funcdef_0__power (fun _ => false)
    (update (update (fun _ => 0) vardef_0__power_base size) vardef_0__power_exponent 998244351)).
Definition convolveCompact : Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve) withLocalVariablesReturnValue unit :=
  addInt 64 (subInt 64 (convolveGet vardef_0__convolve_length) (convolveGet vardef_0__convolve_skip))
    (convolveGet vardef_0__convolve_span) >>= fun count =>
  convolveSet vardef_0__convolve_count count >>= fun _ =>
  convolveSet vardef_0__convolve_size 1 >>= fun _ =>
  loop 20 convolveSizeBody >>= fun _ =>
  convolveGet vardef_0__convolve_size >>= fun size => loop (Z.to_nat size) (convolveInputBody size) >>= fun _ =>
  convolveNtt >>= fun _ =>
  convolveGet vardef_0__convolve_size >>= fun size => loop (Z.to_nat size) (convolveKernelBody size) >>= fun _ =>
  convolveNtt >>= fun _ => convolvePower >>= fun _ =>
  retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__convolve arraydef_0__result 2 >>= fun scale =>
  convolveSet vardef_0__convolve_scale scale >>= fun _ =>
  convolveGet vardef_0__convolve_size >>= fun size => loop (Z.to_nat size) (convolveProductBody size) >>= fun _ =>
  divIntUnsigned (subInt 64 (convolveGet vardef_0__convolve_size) (Done _ _ _ 1)) (Done _ _ _ 2) >>= fun pairs =>
  loop (Z.to_nat pairs) (convolveNegateBody pairs) >>= fun _ =>
  convolveNtt >>= fun _ =>
  convolveGet vardef_0__convolve_count >>= fun count => loop (Z.to_nat count) (convolveSaveBody count) >>= fun _ =>
  Done _ _ _ tt.
Lemma convolveCompact_exact : funcdef_0__convolve_body=convolveCompact.
Proof. reflexivity. Qed.
Local Opaque funcdef_0__power funcdef_0__ntt.

Definition transformCall stage := funcdef_0__ntt (fun _ => false)
  (update (fun _ => 0) vardef_0__ntt_size (stageSize stage)).
Definition inverseSizeCall stage := funcdef_0__power (fun _ => false)
  (update (update (fun _ => 0) vardef_0__power_base (stageSize stage)) vardef_0__power_exponent 998244351).
Definition convolutionAction stage count len skip span base tmp :=
  let size := sizeNat stage in
  let pairs := ((size-1)/2)%nat in
  copyAction size size arraydef_0__work arraydef_0__poly skip (len-skip) >>= fun _ =>
  transformCall stage >>= fun _ => kernelAction size size span >>= fun _ =>
  transformCall stage >>= fun _ => inverseSizeCall stage >>= fun _ =>
  tableRead arraydef_0__result 2 >>= fun scale =>
  productAction size size scale >>= fun _ => negateAction pairs pairs size tmp >>= fun _ =>
  transformCall stage >>= fun _ => copyIntoAction count count arraydef_0__arena arraydef_0__work base 0.

Ltac normalize_convolve := try unfold numberLocalGet,numberLocalSet,retrieve; normalize_table_loop.

Theorem generated_convolve_normalized b nums len skip span base :
  nums vardef_0__convolve_length=Z.of_nat len -> nums vardef_0__convolve_skip=Z.of_nat skip ->
  nums vardef_0__convolve_span=Z.of_nat span -> nums vardef_0__convolve_base=Z.of_nat base ->
  (skip<len)%nat -> Z.of_nat len<koxiaModulus -> 0<Z.of_nat (len-skip+span)<=1048576 ->
  Z.of_nat (base+(len-skip+span))<18446744073709551616 ->
  funcdef_0__convolve b nums=
  convolutionAction (ceilingStage 20 (Z.of_nat (len-skip+span)) 0) (len-skip+span) len skip span base
    (nums vardef_0__convolve_tmp).
Proof.
  intros lenEq skipEq spanEq baseEq skipBound lenBound countBound arenaBound.
  set (count := (len-skip+span)%nat).
  set (stage := ceilingStage 20 (Z.of_nat count) 0).
  pose proof (ceilingStage_correct (Z.of_nat count) ltac:(unfold count; lia)) as [stageBound sizeBounds].
  change (Z.of_nat count<=stageSize stage<2*Z.of_nat count) in sizeBounds.
  assert (sizeBound : stageSize stage<=1048576) by (apply stageSize_bound; exact stageBound).
  assert (spanBound : Z.of_nat span<koxiaModulus) by (unfold count in sizeBounds; unfold koxiaModulus; lia).
  unfold funcdef_0__convolve. rewrite convolveCompact_exact.
  unfold convolveCompact,convolveGet,convolveSet,addInt,subInt. normalize_convolve.
  rewrite lenEq,skipEq.
  rewrite (coerce64_small (Z.of_nat len-Z.of_nat skip)) by (unfold koxiaModulus in lenBound; lia).
  normalize_convolve. rewrite spanEq.
  assert (countEq : coerceInt (Z.of_nat len-Z.of_nat skip+Z.of_nat span) 64=Z.of_nat count).
  { rewrite coerce64_small by (unfold count; lia). unfold count; lia. }
  rewrite countEq. normalize_convolve.
  rewrite convolve_size_normalized with (target:=Z.of_nat count) by (rewrite ?lookupSame,?lookupDifferent by congruence; reflexivity).
  fold stage. normalize_convolve. rewrite lookupSame.
  replace (Z.to_nat (stageSize stage)) with (sizeNat stage) by (rewrite stageSize_nat,Nat2Z.id; reflexivity).
  replace (convolveInputBody (stageSize stage)) with (convolveInputBody (Z.of_nat (sizeNat stage))) by (f_equal; symmetry; apply stageSize_nat).
  rewrite convolveInputLoopNormalized with (len:=len) (skip:=skip)
    by (try rewrite !lookupDifferent by congruence; try rewrite <-stageSize_nat; try assumption; lia).
  unfold convolutionAction. fold count stage.
  apply f_equal. apply functional_extensionality. intros [].
  unfold convolveNtt,convolveGet. normalize_convolve.
  rewrite lookupSame. rewrite eliminateLift. fold (transformCall stage).
  apply f_equal. apply functional_extensionality. intros [].
  normalize_convolve. rewrite lookupSame. replace (Z.to_nat (stageSize stage)) with (sizeNat stage) by (rewrite stageSize_nat,Nat2Z.id; reflexivity).
  replace (convolveKernelBody (stageSize stage)) with (convolveKernelBody (Z.of_nat (sizeNat stage))) by (f_equal; symmetry; apply stageSize_nat).
  rewrite convolveKernelLoopNormalized with (span:=span)
    by (try rewrite !lookupDifferent by congruence; try rewrite <-stageSize_nat; try assumption; lia).
  apply f_equal. apply functional_extensionality. intros [].
  unfold convolveNtt,convolvePower,convolveGet. normalize_convolve.
  rewrite lookupSame,eliminateLift. fold (transformCall stage).
  apply f_equal. apply functional_extensionality. intros [].
  normalize_convolve. rewrite lookupSame,eliminateLift. fold (inverseSizeCall stage).
  apply f_equal. apply functional_extensionality. intros [].
  unfold retrieve. normalize_convolve. unfold tableRead. cbn [bind].
  apply f_equal. apply functional_extensionality. intro scale. normalize_convolve.
  rewrite lookupDifferent by congruence. rewrite lookupSame. replace (Z.to_nat (stageSize stage)) with (sizeNat stage) by (rewrite stageSize_nat,Nat2Z.id; reflexivity).
  replace (convolveProductBody (stageSize stage)) with (convolveProductBody (Z.of_nat (sizeNat stage))) by (f_equal; symmetry; apply stageSize_nat).
  rewrite convolveProductLoopNormalized by lia. rewrite lookupSame.
  apply f_equal. apply functional_extensionality. intros [].
  unfold divIntUnsigned,subInt,numberLocalGet. normalize_convolve.
  rewrite lookupDifferent by congruence. rewrite lookupSame.
  rewrite coerce64_small by (pose proof (stageSize_positive stage); lia).
  normalize_convolve.
  assert (pairsEq : Z.to_nat ((stageSize stage-1)/2)=((sizeNat stage-1)/2)%nat).
  { rewrite stageSize_nat.
    change (Z.to_nat ((Z.of_nat (sizeNat stage)-Z.of_nat 1)/Z.of_nat 2)=((sizeNat stage-1)/2)%nat).
    rewrite <-Nat2Z.inj_sub by (pose proof (stageSize_positive stage) as positive; rewrite stageSize_nat in positive; lia).
    rewrite <-Nat2Z.inj_div,Nat2Z.id. reflexivity. }
  rewrite pairsEq.
  assert (pairsZ : (stageSize stage-1)/2=Z.of_nat ((sizeNat stage-1)/2)).
  { rewrite <-pairsEq. rewrite Z2Nat.id by (apply Z.div_pos; pose proof (stageSize_positive stage); lia). reflexivity. }
  rewrite pairsZ.
  rewrite convolveNegateLoopNormalized with (size:=sizeNat stage).
  2: rewrite lookupDifferent by congruence; rewrite lookupSame; apply stageSize_nat.
  2: lia.
  2: pose proof (stageSize_positive stage) as positive; rewrite stageSize_nat in positive; pose proof (Nat.div_mod (sizeNat stage-1) 2 ltac:(lia)); pose proof (Nat.mod_upper_bound (sizeNat stage-1) 2 ltac:(lia)); lia.
  2: rewrite <-stageSize_nat; exact sizeBound.
  rewrite !lookupDifferent by congruence.
  apply f_equal. apply functional_extensionality. intro saved.
  unfold convolveNtt,convolveGet. normalize_convolve.
  rewrite lookupDifferent by congruence. rewrite lookupDifferent by congruence. rewrite lookupSame,eliminateLift. fold (transformCall stage).
  apply f_equal. apply functional_extensionality. intros [].
  normalize_convolve. rewrite !lookupDifferent by congruence. rewrite lookupSame,Nat2Z.id.
  rewrite convolveSaveLoopNormalized with (base:=base)
    by (try rewrite !lookupDifferent by congruence; try rewrite <-stageSize_nat; try assumption; lia).
  normalize_convolve. cbn [eliminateLocalVariables]. apply bind_unit_identity.
Qed.
