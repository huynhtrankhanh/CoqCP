From CoqCP Require Import Options Imperative Execution KoxiaModular KoxiaIntegers
  KoxiaPower KoxiaRadix KoxiaArrays KoxiaRoots KoxiaFourier KoxiaNTT KoxiaNTTButterflies SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Local Existing Instance congruent_mul.
Local Existing Instance congruent_opp.
Local Opaque fastPower modularPower stageRoot stageInverse.

Definition rootTableCorrect roots stage :=
  forall offset, (offset<sizeNat stage)%nat ->
    congruent (nth (sizeNat stage+offset) roots 0) (rootPower (S stage) (Z.of_nat offset)).

Lemma blockValue_butterfly stage values roots block offset :
  (stage<20)%nat -> rootTableCorrect roots stage -> (offset<2*sizeNat stage)%nat ->
  congruent
    (blockValue values roots (block*(sizeNat stage+sizeNat stage)) (sizeNat stage)
      (block*(sizeNat stage+sizeNat stage)+offset))
    (butterfly stage (fun i => nth (Z.to_nat i) values 0)
      (Z.of_nat (block*(sizeNat stage+sizeNat stage)+offset))).
Proof.
  intros bound rootCorrect offsetRange.
  pose proof (stageSize_positive stage) as positive.
  unfold butterfly. rewrite Nat2Z.inj_add, Nat2Z.inj_mul,Nat2Z.inj_add,<-stageSize_nat.
  replace (stageSize stage+stageSize stage) with (2*stageSize stage) by ring.
  pose proof (block_offset (2*stageSize stage) (Z.of_nat block) (Z.of_nat offset)
    ltac:(lia) ltac:(rewrite stageSize_nat; lia)) as [quotient remainder].
  rewrite quotient,remainder.
  assert (halfRemainder :
    (Z.of_nat block*(2*stageSize stage)+Z.of_nat offset) mod stageSize stage=Z.of_nat offset mod stageSize stage).
  { replace (Z.of_nat block*(2*stageSize stage)+Z.of_nat offset) with
      (Z.of_nat offset+(2*Z.of_nat block)*stageSize stage) by ring.
    rewrite Z.mod_add by lia. reflexivity. }
  rewrite halfRemainder. unfold blockValue.
  destruct (lt_dec offset (sizeNat stage)) as [lower|upper].
  - rewrite bool_decide_true by lia.
    assert (comparison : (Z.of_nat offset <? stageSize stage)=true) by (apply Z.ltb_lt; rewrite stageSize_nat; lia).
    rewrite comparison,(Z.mod_small (Z.of_nat offset) (stageSize stage) ltac:(rewrite stageSize_nat; lia)).
    rewrite stageSize_nat.
    replace (2*Z.of_nat (sizeNat stage)) with (Z.of_nat (sizeNat stage+sizeNat stage)) by (rewrite Nat2Z.inj_add; ring).
    repeat rewrite <-Nat2Z.inj_mul. repeat rewrite <-Nat2Z.inj_add. rewrite !Nat2Z.id.
    replace (block*(sizeNat stage+sizeNat stage)+offset-block*(sizeNat stage+sizeNat stage))%nat
      with offset by lia.
    pose proof (rootCorrect offset lower) as root.
    transitivity (nth (block*(sizeNat stage+sizeNat stage)+offset)%nat values 0+
      nth (sizeNat stage+offset)%nat roots 0*
      nth (block*(sizeNat stage+sizeNat stage)+offset+sizeNat stage)%nat values 0).
    + transitivity (nth (block*(sizeNat stage+sizeNat stage)+offset)%nat values 0+
        (nth (sizeNat stage+offset)%nat roots 0*
         nth (block*(sizeNat stage+sizeNat stage)+offset+sizeNat stage)%nat values 0) mod koxiaModulus).
      * apply congruent_modulo.
      * apply congruent_add; [reflexivity|apply congruent_modulo].
    + setoid_rewrite root. symmetry. apply congruent_modulo.
  - rewrite bool_decide_false by lia. rewrite bool_decide_true by lia.
    assert (comparison : (Z.of_nat offset <? stageSize stage)=false) by (apply Z.ltb_ge; rewrite stageSize_nat; lia).
    rewrite comparison.
    assert (offsetId : Z.of_nat offset mod stageSize stage=Z.of_nat (offset-sizeNat stage)).
    { replace (Z.of_nat offset) with (Z.of_nat (offset-sizeNat stage)+1*stageSize stage) at 1
        by (rewrite stageSize_nat; lia).
      rewrite Z.mod_add by lia. apply Z.mod_small. rewrite stageSize_nat; lia. }
    rewrite offsetId,stageSize_nat.
    replace (2*Z.of_nat (sizeNat stage)) with (Z.of_nat (sizeNat stage+sizeNat stage)) by (rewrite Nat2Z.inj_add; ring).
    repeat rewrite <-Nat2Z.inj_mul. repeat rewrite <-Nat2Z.inj_add. rewrite !Nat2Z.id.
    replace (block*(sizeNat stage+sizeNat stage)+offset-block*(sizeNat stage+sizeNat stage)-sizeNat stage)%nat
      with (offset-sizeNat stage)%nat by lia.
    replace (block*(sizeNat stage+sizeNat stage)+offset-sizeNat stage)%nat
      with (block*(sizeNat stage+sizeNat stage)+(offset-sizeNat stage))%nat by lia.
    replace (block*(sizeNat stage+sizeNat stage)+(offset-sizeNat stage)+sizeNat stage)%nat
      with (block*(sizeNat stage+sizeNat stage)+offset)%nat by lia.
    replace (block*(sizeNat stage+sizeNat stage)+offset-block*(sizeNat stage+sizeNat stage))%nat
      with (sizeNat stage+(offset-sizeNat stage))%nat by lia.
    pose proof (rootCorrect (offset-sizeNat stage)%nat ltac:(lia)) as root.
    transitivity (nth (block*(sizeNat stage+sizeNat stage)+(offset-sizeNat stage))%nat values 0-
      nth (sizeNat stage+(offset-sizeNat stage))%nat roots 0*
      nth (block*(sizeNat stage+sizeNat stage)+offset)%nat values 0).
    + transitivity (nth (block*(sizeNat stage+sizeNat stage)+(offset-sizeNat stage))%nat values 0-
        (nth (sizeNat stage+(offset-sizeNat stage))%nat roots 0*
         nth (block*(sizeNat stage+sizeNat stage)+offset)%nat values 0) mod koxiaModulus).
      * apply congruent_modulo.
      * unfold Z.sub. apply congruent_add; [reflexivity|apply congruent_opp; apply congruent_modulo].
    + unfold Z.sub. setoid_rewrite root. symmetry. apply congruent_modulo.
Qed.

Theorem stageWork_correct stage count values roots index :
  (stage<20)%nat -> rootTableCorrect roots stage ->
  (count*(sizeNat stage+sizeNat stage)<=length values)%nat ->
  0<=index<Z.of_nat (count*(sizeNat stage+sizeNat stage)) ->
  congruent (nth (Z.to_nat index) (stageWork count values roots (sizeNat stage)) 0)
    (butterfly stage (fun i => nth (Z.to_nat i) values 0) index).
Proof.
  intros bound rootCorrect lengthEq indexRange.
  pose proof (stageSize_positive stage) as positive. rewrite stageSize_nat in positive.
  rewrite stageWork_lookup by lia. unfold partialStageValue. rewrite bool_decide_true by lia.
  set (width := (sizeNat stage+sizeNat stage)%nat).
  set (block := (Z.to_nat index / width)%nat).
  set (offset := (Z.to_nat index mod width)%nat).
  assert (offsetRange : (offset<width)%nat).
  { unfold offset. apply Nat.mod_upper_bound. unfold width. lia. }
  assert (decompose : Z.to_nat index=(block*width+offset)%nat).
  { unfold block,offset. pose proof (Nat.div_mod (Z.to_nat index) width ltac:(unfold width; lia)). nia. }
  change (congruent (blockValue values roots (block*width) (sizeNat stage) (Z.to_nat index))
    (butterfly stage (fun i => nth (Z.to_nat i) values 0) index)).
  rewrite decompose.
  replace index with (Z.of_nat (block*width+offset)) by (rewrite <-decompose,Z2Nat.id by lia; reflexivity).
  unfold width. apply blockValue_butterfly; [exact bound|exact rootCorrect|unfold width in offsetRange; lia].
Qed.

Fixpoint transformStages total stage values roots :=
  match stage with
  | O => values
  | S stage => stageWork (sizeNat (total-S stage))
      (transformStages total stage values roots) roots (sizeNat stage)
  end.
Lemma transformStages_length total stage values roots :
  length (transformStages total stage values roots)=length values.
Proof. induction stage as [|stage IH]; cbn [transformStages]; rewrite ?stageWork_length,?IH; reflexivity. Qed.
Lemma transformStages_canonical total stage values roots :
  canonicalValues values -> canonicalValues (transformStages total stage values roots).
Proof. intro canonical. induction stage as [|stage IH]; cbn [transformStages]; [exact canonical|apply stageWork_canonical; exact IH]. Qed.
Lemma stageSize_factor total stage : (stage<total)%nat ->
  stageSize total=stageSize (total-S stage)*(2*stageSize stage).
Proof.
  intro bound. replace total with ((total-S stage)+S stage)%nat at 1 by lia.
  rewrite stageSize_add,stageSize_succ. reflexivity.
Qed.
Lemma sizeNat_factor total stage : (stage<total)%nat ->
  sizeNat total=(sizeNat (total-S stage)*(sizeNat stage+sizeNat stage))%nat.
Proof.
  intro bound. apply Nat2Z.inj. rewrite Nat2Z.inj_mul,Nat2Z.inj_add,<-!stageSize_nat.
  rewrite (stageSize_factor total stage bound). ring.
Qed.

Theorem stagesAction_execution fuel stage total state values nums :
  (stage<=total<=20)%nat -> (total-stage<=fuel)%nat ->
  (sizeNat total<=length values)%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat total<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  canonicalValues values -> canonicalValues (memory state arraydef_0__roots) ->
  nums vardef_0__ntt_size=stageSize total -> nums vardef_0__ntt_k=stageSize stage ->
  exists final,
    exec (stagesAction fuel nums)
      (withWork state (transformStages total stage values (memory state arraydef_0__roots))) =
      Some (final,withWork state (transformStages total total values (memory state arraydef_0__roots))) /\
    final vardef_0__ntt_k=stageSize total /\ final vardef_0__ntt_size=stageSize total /\
    (forall name, name<>vardef_0__ntt_start -> name<>vardef_0__ntt_left ->
      name<>vardef_0__ntt_right -> name<>vardef_0__ntt_k -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in stage,nums |- *.
  - intros bound enough lengthEq valuesFit rootRoom rootsFit canonical rootCanonical sizeEq halfEq.
    assert (stage=total) by lia. subst stage. cbn [stagesAction exec].
    exists nums. split; [reflexivity|]. split; [exact halfEq|]. split; [exact sizeEq|]. intros; reflexivity.
  - intros bound enough lengthEq valuesFit rootRoom rootsFit canonical rootCanonical sizeEq halfEq.
    cbn [stagesAction].
    destruct (Nat.eq_dec stage total) as [finished|unfinished].
    + subst stage. rewrite halfEq,sizeEq,bool_decide_false by lia. cbn [exec].
      exists nums. split; [reflexivity|]. split; [exact halfEq|]. split; [exact sizeEq|]. intros; reflexivity.
    + assert (stageBound : (stage<total)%nat) by lia.
      pose proof (stageSize_positive stage) as positive.
      pose proof (stageSize_positive (total-S stage)) as factorPositive.
      pose proof (stageSize_factor total stage stageBound) as factor.
      pose proof (stageSize_bound total ltac:(lia)) as sizeBound.
      assert (continuing : stageSize stage<stageSize total).
      { assert (1<=stageSize (total-S stage)) by lia. nia. }
      rewrite halfEq,sizeEq,bool_decide_true by exact continuing.
      assert (double : coerceInt (2*stageSize stage) 64=2*stageSize stage).
      { apply coerce64_small. change (0<=2*stageSize stage<18446744073709551616). nia. }
      rewrite double,decide_False by lia.
      assert (quotient : stageSize total/(2*stageSize stage)=stageSize (total-S stage)).
      { rewrite factor,Z.div_mul by lia. reflexivity. }
      rewrite quotient,stageSize_nat,Nat2Z.id,exec_bind.
      set (current := transformStages total stage values (memory state arraydef_0__roots)).
      assert (currentLength : length current=length values).
      { unfold current. apply transformStages_length. }
      pose proof (sizeNat_factor total stage stageBound) as factorNat.
      assert (workFit : Z.of_nat (length current)<18446744073709551616).
      { rewrite currentLength. exact valuesFit. }
      destruct (blocksAction_execution (sizeNat (total-S stage)) 0 (sizeNat (total-S stage))
        state current nums (sizeNat stage)
        ltac:(rewrite stageSize_nat in positive; lia) ltac:(lia)
        ltac:(rewrite <-stageSize_nat; exact halfEq)
        ltac:(rewrite currentLength; lia)
        ltac:(rewrite stageSize_nat in positive,factorPositive; nia)
        workFit rootsFit ltac:(unfold current; apply transformStages_canonical; exact canonical) rootCanonical)
        as [next [executed nextOthers]].
      cbn [stageWork] in executed. rewrite executed. cbn [optionBind fst snd].
      assert (nextHalf : next vardef_0__ntt_k=stageSize stage) by (rewrite nextOthers by congruence; exact halfEq).
      assert (nextSize : next vardef_0__ntt_size=stageSize total) by (rewrite nextOthers by congruence; exact sizeEq).
      rewrite nextHalf. replace (stageSize stage*2) with (2*stageSize stage) by ring. rewrite double.
      set (doubled := update next vardef_0__ntt_k (2*stageSize stage)).
      destruct (IH (S stage) doubled ltac:(lia) ltac:(lia) lengthEq valuesFit rootRoom rootsFit canonical rootCanonical
        ltac:(unfold doubled,update; exact nextSize)
        ltac:(unfold doubled,update; rewrite stageSize_succ; reflexivity))
        as [final [executedFinal [finalHalf [finalSize finalOthers]]]].
      exists final. split; [exact executedFinal|]. split; [exact finalHalf|]. split; [exact finalSize|].
      intros name notStart notLeft notRight notK. rewrite finalOthers by assumption.
      unfold doubled,update. destruct (decide (name=vardef_0__ntt_k)); [congruence|].
      rewrite nextOthers by assumption. reflexivity.
Qed.

Lemma butterfly_congruent stage total p q index :
  (stage<total)%nat -> 0<=index<stageSize total ->
  (forall i, 0<=i<stageSize total -> congruent (p i) (q i)) ->
  congruent (butterfly stage p index) (butterfly stage q index).
Proof.
  intros bound range agree. unfold butterfly.
  pose proof (stageSize_positive stage) as positive.
  pose proof (stageSize_positive (total-S stage)) as factorPositive.
  pose proof (stageSize_factor total stage bound) as factor.
  pose proof (Z.mod_pos_bound index (stageSize stage) positive) as offsetRange.
  assert (blockRange : 0<=index/(2*stageSize stage)<stageSize (total-S stage)).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; nia]. }
  assert (leftRange : 0<=index/(2*stageSize stage)*(2*stageSize stage)+index mod stageSize stage<stageSize total) by nia.
  assert (rightRange : 0<=index/(2*stageSize stage)*(2*stageSize stage)+index mod stageSize stage+stageSize stage<stageSize total) by nia.
  pose proof (agree _ leftRange) as left. pose proof (agree _ rightRange) as right.
  destruct (index mod (2*stageSize stage) <? stageSize stage).
  - unfold congruent. rewrite !Z.mod_mod by (pose proof modulus_positive; lia).
    fold congruent. apply congruent_add; [exact left|apply congruent_mul; [reflexivity|exact right]].
  - unfold congruent. rewrite !Z.mod_mod by (pose proof modulus_positive; lia).
    fold congruent. unfold Z.sub. apply congruent_add; [exact left|apply congruent_opp; apply congruent_mul; [reflexivity|exact right]].
Qed.

Theorem transformStages_correct total stage values roots index :
  (stage<=total<=20)%nat -> (sizeNat total<=length values)%nat ->
  (forall step, (step<total)%nat -> rootTableCorrect roots step) ->
  0<=index<stageSize total ->
  congruent (nth (Z.to_nat index) (transformStages total stage values roots) 0)
    (iterativeStages stage (fun i => nth (Z.to_nat i) values 0) index).
Proof.
  induction stage as [|stage IH] in index |- *.
  - intros. reflexivity.
  - intros bound lengthEq rootsCorrect range. cbn [transformStages iterativeStages].
    transitivity (butterfly stage
      (fun i => nth (Z.to_nat i) (transformStages total stage values roots) 0) index).
    + apply stageWork_correct.
      * lia.
      * apply rootsCorrect. lia.
      * rewrite transformStages_length. rewrite <-(sizeNat_factor total stage ltac:(lia)). exact lengthEq.
      * rewrite <-(sizeNat_factor total stage ltac:(lia)),<-stageSize_nat. exact range.
    + apply butterfly_congruent with (total:=total); [lia|exact range|].
      intros i iRange. apply IH; [lia|exact lengthEq|exact rootsCorrect|exact iRange].
Qed.

Lemma reverseWork_outside stage count values index :
  (count<=sizeNat stage<=length values)%nat -> (sizeNat stage<=index)%nat ->
  nth index (reverseWork stage count values) 0=nth index values 0.
Proof.
  induction count as [|count IH]; [reflexivity|]. intros bound outside.
  cbn [reverseWork]. pose proof (bitReverse_bounds stage (Z.of_nat count)
    ltac:(rewrite stageSize_nat; lia)) as reversedRange.
  rewrite stageSize_nat in reversedRange.
  destruct (bool_decide ((count<Z.to_nat (bitReverse stage (Z.of_nat count)))%nat)).
  - rewrite nth_swappedWork by (rewrite reverseWork_length; lia).
    rewrite (proj2 (Nat.eqb_neq index count) ltac:(lia)),
      (proj2 (Nat.eqb_neq index (Z.to_nat (bitReverse stage (Z.of_nat count)))) ltac:(lia)).
    apply IH; lia.
  - apply IH; lia.
Qed.
Lemma reverseWork_canonical_full stage values : (sizeNat stage<=length values)%nat ->
  canonicalValues values -> canonicalValues (reverseWork stage (sizeNat stage) values).
Proof.
  intros lengthEq canonical. unfold canonicalValues.
  apply (proj2 (Forall_nth (fun value => 0<=value<koxiaModulus) 0 _)).
  intros index indexBound. rewrite reverseWork_length in indexBound.
  destruct (lt_dec index (sizeNat stage)) as [inside|outside].
  - pose proof (reverseWork_correct stage values (Z.of_nat index)
      ltac:(rewrite stageSize_nat; lia) ltac:(rewrite stageSize_nat; lia)) as reversedLookup.
    rewrite Nat2Z.id in reversedLookup. rewrite reversedLookup.
    apply canonical_nth; [exact canonical|].
    pose proof (bitReverse_bounds stage (Z.of_nat index) ltac:(rewrite stageSize_nat; lia)) as reversedRange.
    rewrite stageSize_nat in reversedRange. lia.
  - rewrite reverseWork_outside by lia. apply canonical_nth; assumption.
Qed.

Lemma generated_ntt_normalized b nums :
  funcdef_0__ntt b nums =
  reverseAction (Z.to_nat (nums vardef_0__ntt_size)) (nums vardef_0__ntt_size) nums
    (nums vardef_0__ntt_j) (nums vardef_0__ntt_bit) >>= fun reversed =>
  stagesAction 20 (update reversed vardef_0__ntt_k 1) >>= fun _ => Done _ _ _ tt.
Proof.
  rewrite generated_ntt_reverse_normalized.
  apply f_equal. apply functional_extensionality. intro reversed.
  unfold numberLocalSet. autorewrite with advance_program.
  rewrite nttStagesNormalized. reflexivity.
Qed.

Theorem generated_ntt_execution total state values b nums :
  (total<=20)%nat -> (sizeNat total<=length values)%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat total<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  canonicalValues values -> canonicalValues (memory state arraydef_0__roots) ->
  nums vardef_0__ntt_size=stageSize total -> nums vardef_0__ntt_j=0 ->
  exec (funcdef_0__ntt b nums) (withWork state values) =
    Some (tt,withWork state
      (transformStages total total (reverseWork total (sizeNat total) values) (memory state arraydef_0__roots))).
Proof.
  intros bound lengthEq valuesFit rootRoom rootsFit canonical rootCanonical sizeEq jEq.
  rewrite generated_ntt_normalized,exec_bind,sizeEq.
  replace (Z.to_nat (stageSize total)) with (sizeNat total) by (rewrite stageSize_nat,Nat2Z.id; reflexivity).
  rewrite jEq.
  pose proof (stageSize_positive total) as positive.
  destruct (reverseAction_execution total (sizeNat total) 0 state values nums
    (nums vardef_0__ntt_bit) bound ltac:(lia)
    ltac:(rewrite stageSize_nat; lia) sizeEq)
    as [reversed [executed [finalJ [finalSize others]]]].
  cbn [reverseWork] in executed.
  rewrite Z.mod_0_l in executed by lia. rewrite bitReverse_zero in executed.
  rewrite executed. cbn [optionBind fst snd].
  destruct (stagesAction_execution 20 0 total state (reverseWork total (sizeNat total) values)
    (update reversed vardef_0__ntt_k 1) ltac:(lia) ltac:(lia)
    ltac:(rewrite reverseWork_length; exact lengthEq)
    ltac:(rewrite reverseWork_length; exact valuesFit) rootRoom rootsFit
    ltac:(apply reverseWork_canonical_full; assumption) rootCanonical
    ltac:(unfold update; exact finalSize) ltac:(unfold update; reflexivity))
    as [final [stagesExecuted finalProperties]].
  cbn [transformStages] in stagesExecuted. rewrite exec_bind,stagesExecuted. reflexivity.
Qed.

Lemma iterativeStages_congruent steps total p q index : (steps<=total)%nat ->
  (forall i, 0<=i<stageSize total -> congruent (p i) (q i)) ->
  0<=index<stageSize total ->
  congruent (iterativeStages steps p index) (iterativeStages steps q index).
Proof.
  induction steps as [|steps IH] in index |- *.
  - intros bound agree range. apply agree. exact range.
  - intros bound agree range. cbn [iterativeStages].
    apply butterfly_congruent with (total:=total); [lia|exact range|].
    intros i iRange. apply IH; [lia|exact agree|exact iRange].
Qed.

Theorem generated_ntt_fourier total state values b nums :
  (total<=20)%nat -> (sizeNat total<=length values)%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat total<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  canonicalValues values -> canonicalValues (memory state arraydef_0__roots) ->
  (forall step, (step<total)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  nums vardef_0__ntt_size=stageSize total -> nums vardef_0__ntt_j=0 ->
  exists transformed,
    exec (funcdef_0__ntt b nums) (withWork state values)=Some (tt,withWork state transformed) /\
    length transformed=length values /\ canonicalValues transformed /\
    (forall index, 0<=index<stageSize total ->
      congruent (nth (Z.to_nat index) transformed 0)
        (fourier total (fun i => nth (Z.to_nat i) values 0) index)).
Proof.
  intros bound lengthEq valuesFit rootRoom rootsFit canonical rootCanonical rootsCorrect sizeEq jEq.
  eexists. split; [apply generated_ntt_execution; eassumption|].
  split; [rewrite transformStages_length,reverseWork_length; reflexivity|].
  split; [apply transformStages_canonical; apply reverseWork_canonical_full; assumption|].
  intros index range.
  transitivity (iterativeStages total
    (fun i => nth (Z.to_nat i) (reverseWork total (sizeNat total) values) 0) index).
  - apply transformStages_correct; [lia|rewrite reverseWork_length; exact lengthEq|exact rootsCorrect|exact range].
  - transitivity (iterativeTransform total (fun i => nth (Z.to_nat i) values 0) index).
    + unfold iterativeTransform.
      assert (agree : forall i, 0<=i<stageSize total ->
        congruent (nth (Z.to_nat i) (reverseWork total (sizeNat total) values) 0)
          (nth (Z.to_nat (bitReverse total i)) values 0)).
      { intros i iRange. rewrite (reverseWork_correct total values i
          ltac:(rewrite stageSize_nat; lia) iRange). reflexivity. }
      apply iterativeStages_congruent with (total:=total); [lia|exact agree|exact range].
    + apply iterativeTransform_correct; assumption.
Qed.

Lemma transformStages_outside total stage values roots index :
  (stage<=total)%nat -> (sizeNat total<=length values)%nat -> (sizeNat total<=index)%nat ->
  nth index (transformStages total stage values roots) 0=nth index values 0.
Proof.
  induction stage as [|stage IH]; [reflexivity|]. intros bound room outside.
  cbn [transformStages]. rewrite stageWork_future.
  - apply IH; [lia|exact room|exact outside].
  - rewrite transformStages_length,<-(sizeNat_factor total stage ltac:(lia)). exact room.
  - rewrite <-(sizeNat_factor total stage ltac:(lia)). exact outside.
Qed.

Theorem generated_ntt_complete total state values b nums :
  (total<=20)%nat -> (sizeNat total<=length values)%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  (sizeNat total<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  canonicalValues values -> canonicalValues (memory state arraydef_0__roots) ->
  (forall step, (step<total)%nat -> rootTableCorrect (memory state arraydef_0__roots) step) ->
  nums vardef_0__ntt_size=stageSize total -> nums vardef_0__ntt_j=0 ->
  exists transformed,
    exec (funcdef_0__ntt b nums) (withWork state values)=Some (tt,withWork state transformed) /\
    length transformed=length values /\ canonicalValues transformed /\
    (forall index, (index<length values)%nat -> nth index transformed 0=
      if bool_decide ((index<sizeNat total)%nat) then
        fourier total (fun i => nth (Z.to_nat i) values 0) (Z.of_nat index) mod koxiaModulus
      else nth index values 0).
Proof.
  intros bound room valuesFit rootRoom rootsFit canonical rootCanonical rootsCorrect sizeEq jEq.
  destruct (generated_ntt_fourier total state values b nums bound room valuesFit rootRoom rootsFit canonical rootCanonical rootsCorrect sizeEq jEq)
    as [transformed [execution [lengthEq [outputCanonical outputFourier]]]].
  exists transformed. split; [exact execution|]. split; [exact lengthEq|]. split; [exact outputCanonical|].
  intros index indexBound.
  destruct (lt_dec index (sizeNat total)) as [inside|outside].
  - rewrite bool_decide_true by exact inside.
    pose proof (outputFourier (Z.of_nat index) ltac:(rewrite stageSize_nat; lia)) as value.
    rewrite Nat2Z.id in value. unfold congruent in value.
    rewrite Z.mod_small in value by (apply canonical_nth; [exact outputCanonical|rewrite lengthEq; exact indexBound]). exact value.
  - rewrite bool_decide_false by exact outside.
    rewrite generated_ntt_execution with (total:=total) in execution by assumption.
    pose proof (f_equal (fun result => match result with
      | Some (_,s) => memory s arraydef_0__work
      | None => []
      end) execution) as arraysEqual.
    change (transformStages total total (reverseWork total (sizeNat total) values) (memory state arraydef_0__roots)=transformed) in arraysEqual.
    rewrite <-arraysEqual. rewrite transformStages_outside with (total:=total) by (rewrite ?reverseWork_length; lia).
    apply reverseWork_outside; [split; [lia|exact room]|lia].
Qed.
