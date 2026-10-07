From CoqCP Require Import Options.
From Submission Require Import KoxiaFourier KoxiaRoots KoxiaModular.
From Stdlib Require Import ZArith.ZArith Arith.PeanoNat Bool.Bool Lia Logic.FunctionalExtensionality
  Classes.RelationClasses Classes.Morphisms Setoid.
Local Open Scope Z_scope.
Local Opaque fastPower modularPower stageRoot stageInverse.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Local Existing Instance congruent_mul.
Local Existing Instance congruent_opp.

Fixpoint bitReverse stage index : Z :=
  match stage with
  | O => 0
  | S stage => (index mod 2)*stageSize stage + bitReverse stage (index/2)
  end.
Lemma bitReverse_bounds stage index : 0 <= index < stageSize stage ->
  0 <= bitReverse stage index < stageSize stage.
Proof.
  induction stage as [|stage IH] in index |- *.
  - intros range. change (0<=0<1). lia.
  - intro range. cbn [bitReverse]. rewrite stageSize_succ in range |- *.
    pose proof (stageSize_positive stage) as hn.
    pose proof (Z.mod_pos_bound index 2 ltac:(lia)) as remainder.
    assert (quotient : 0 <= index/2 < stageSize stage).
    { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
    pose proof (IH _ quotient). nia.
Qed.
Lemma bitReverse_shift stage index bit : 0 <= index < stageSize stage -> 0 <= bit <= 1 ->
  bitReverse (S stage) (index+bit*stageSize stage) = 2*bitReverse stage index+bit.
Proof.
  induction stage as [|stage IH] in index |- *.
  - intros range bits. change (0<=index<1) in range. assert (index=0) by lia. subst index.
    cbn [bitReverse].
    change ((0+bit*1) mod 2*1+0 = 2*0+bit).
    replace (0+bit*1) with bit by ring.
    rewrite Z.mod_small by lia. ring.
  - intros range bits.
    change (((index+bit*stageSize (S stage)) mod 2)*stageSize (S stage)+
      bitReverse (S stage) ((index+bit*stageSize (S stage))/2) =
      2*((index mod 2)*stageSize stage+bitReverse stage (index/2))+bit).
    rewrite stageSize_succ.
    replace (index+bit*(2*stageSize stage)) with (index+(bit*stageSize stage)*2) by ring.
    rewrite Z.mod_add, Z.div_add by lia.
    rewrite IH.
    + ring.
    + rewrite stageSize_succ in range. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
    + exact bits.
Qed.
Theorem bitReverse_involution stage index : 0 <= index < stageSize stage ->
  bitReverse stage (bitReverse stage index) = index.
Proof.
  induction stage as [|stage IH] in index |- *.
  - intro range. change (0<=index<1) in range. cbn [bitReverse]. lia.
  - intro range.
    change (bitReverse (S stage) ((index mod 2)*stageSize stage+bitReverse stage (index/2)) = index).
    pose proof (Z.mod_pos_bound index 2 ltac:(lia)) as remainder.
    assert (quotient : 0 <= index/2 < stageSize stage).
    { rewrite stageSize_succ in range. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
    replace (index mod 2*stageSize stage+bitReverse stage (index/2)) with
      (bitReverse stage (index/2)+index mod 2*stageSize stage) by ring.
    rewrite bitReverse_shift by (try apply bitReverse_bounds; lia).
    rewrite IH by exact quotient. pose proof (Z.div_mod index 2 ltac:(lia)). lia.
Qed.
Lemma bitReverse_pair stage index bit : 0 <= bit <= 1 ->
  bitReverse (S stage) (2*index+bit) = bit*stageSize stage+bitReverse stage index.
Proof.
  intro bits. cbn [bitReverse].
  replace (2*index+bit) with (bit+index*2) by ring.
  rewrite Z.mod_add, Z.div_add by lia.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia.
  rewrite Z.add_0_l. reflexivity.
Qed.

Definition strided p suffix block : Z -> Z :=
  fun i => p (bitReverse suffix block+stageSize suffix*i).
Lemma strided_even p suffix block :
  strided p (S suffix) (2*block) = (fun i => strided p suffix block (2*i)).
Proof.
  apply functional_extensionality. intro i. unfold strided.
  replace (2*block) with (2*block+0) by ring.
  rewrite bitReverse_pair by lia. rewrite stageSize_succ. f_equal. ring.
Qed.
Lemma strided_odd p suffix block :
  strided p (S suffix) (2*block+1) = (fun i => strided p suffix block (2*i+1)).
Proof.
  apply functional_extensionality. intro i. unfold strided.
  rewrite bitReverse_pair by lia. rewrite stageSize_succ. f_equal. ring.
Qed.

Definition butterfly stage (values : Z -> Z) index :=
  let half := stageSize stage in
  let width := 2*half in
  let block := index/width in
  let offset := index mod half in
  let left := values (block*width+offset) in
  let right := rootPower (S stage) offset * values (block*width+offset+half) in
  (if index mod width <? half then left+right else left-right) mod koxiaModulus.
Fixpoint iterativeStages stage (initial : Z -> Z) :=
  match stage with O => initial | S stage => butterfly stage (iterativeStages stage initial) end.
Definition iterativeTransform stage p :=
  iterativeStages stage (fun i => p (bitReverse stage i)).

Lemma stageSize_add a b : stageSize (a+b)%nat = stageSize a*stageSize b.
Proof. unfold stageSize. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. reflexivity. Qed.
Lemma block_offset width block offset : 0 < width -> 0 <= offset < width ->
  (block*width+offset)/width = block /\ (block*width+offset) mod width=offset.
Proof.
  intros positive range. replace (block*width+offset) with (offset+block*width) by ring.
  rewrite Z.div_add, Z.mod_add, Z.div_small, Z.mod_small by lia. lia.
Qed.

Theorem iterativeStages_blocks stage suffix p block offset :
  (stage+suffix <= 20)%nat -> 0 <= block < stageSize suffix -> 0 <= offset < stageSize stage ->
  congruent (iterativeStages stage (fun i => p (bitReverse (stage+suffix)%nat i))
    (block*stageSize stage+offset)) (fourier stage (strided p suffix block) offset).
Proof.
  induction stage as [|stage IH] in suffix,block,offset |- *.
  - intros bound blockRange offsetRange. change (0<=offset<1) in offsetRange.
    assert (offset=0) by lia. subst offset. cbn [iterativeStages].
    replace (block*stageSize 0+0) with block by (change (block=block*1+0); ring).
    cbn [fourier sizeNat Nat.pow zsum strided]. rewrite Z.mul_0_l, rootPower_zero, Z.mul_1_r, Z.add_0_l.
    change (congruent (p (bitReverse suffix block)) (p (bitReverse suffix block+stageSize suffix*0))).
    rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
  - intros bound blockRange offsetRange.
    pose proof (stageSize_positive stage) as hn.
    rewrite stageSize_succ in offsetRange.
    assert (combined : (S stage+suffix)%nat=(stage+S suffix)%nat) by lia.
    cbn [iterativeStages]. unfold butterfly. rewrite combined, stageSize_succ.
    pose proof (block_offset (2*stageSize stage) block offset ltac:(lia) offsetRange) as [quotient remainder].
    rewrite quotient, remainder.
    assert (smallOffset : (block*(2*stageSize stage)+offset) mod stageSize stage = offset mod stageSize stage).
    { replace (block*(2*stageSize stage)+offset) with (offset+(2*block)*stageSize stage) by ring.
      rewrite Z.mod_add by lia. reflexivity. }
    rewrite smallOffset.
    assert (loRange : 0 <= 2*block < stageSize (S suffix)).
    { rewrite stageSize_succ. lia. }
    assert (hiRange : 0 <= 2*block+1 < stageSize (S suffix)).
    { rewrite stageSize_succ. lia. }
    pose proof (Z.mod_pos_bound offset (stageSize stage) hn) as offsetMod.
    pose proof (IH (S suffix) (2*block) (offset mod stageSize stage) ltac:(lia) loRange offsetMod) as lo.
    pose proof (IH (S suffix) (2*block+1) (offset mod stageSize stage) ltac:(lia) hiRange offsetMod) as hi.
    replace (block*(2*stageSize stage)+offset mod stageSize stage) with
      ((2*block)*stageSize stage+offset mod stageSize stage) by ring.
    replace ((2*block)*stageSize stage+offset mod stageSize stage+stageSize stage) with
      ((2*block+1)*stageSize stage+offset mod stageSize stage) by ring.
    rewrite strided_even in lo. rewrite strided_odd in hi.
    destruct (offset <? stageSize stage) eqn:lower.
    + transitivity (fourier stage (fun i => strided p suffix block (2*i)) (offset mod stageSize stage)+
        rootPower (S stage) (offset mod stageSize stage)*
          fourier stage (fun i => strided p suffix block (2*i+1)) (offset mod stageSize stage)).
      * transitivity (iterativeStages stage (fun i => p (bitReverse (stage+S suffix)%nat i))
          ((2*block)*stageSize stage+offset mod stageSize stage)+
          rootPower (S stage) (offset mod stageSize stage)*
          iterativeStages stage (fun i => p (bitReverse (stage+S suffix)%nat i))
          ((2*block+1)*stageSize stage+offset mod stageSize stage)).
        -- apply congruent_modulo.
        -- setoid_rewrite lo. setoid_rewrite hi. reflexivity.
      * apply Z.ltb_lt in lower. rewrite Z.mod_small by lia. symmetry. apply fourier_even_odd; lia.
    + transitivity (fourier stage (fun i => strided p suffix block (2*i)) (offset mod stageSize stage)-
        rootPower (S stage) (offset mod stageSize stage)*
          fourier stage (fun i => strided p suffix block (2*i+1)) (offset mod stageSize stage)).
      * transitivity (iterativeStages stage (fun i => p (bitReverse (stage+S suffix)%nat i))
          ((2*block)*stageSize stage+offset mod stageSize stage)-
          rootPower (S stage) (offset mod stageSize stage)*
          iterativeStages stage (fun i => p (bitReverse (stage+S suffix)%nat i))
          ((2*block+1)*stageSize stage+offset mod stageSize stage)).
        -- apply congruent_modulo.
        -- unfold Z.sub. setoid_rewrite lo. setoid_rewrite hi. reflexivity.
      * apply Z.ltb_ge in lower.
        assert (offsetId : offset mod stageSize stage = offset-stageSize stage).
        { replace offset with ((offset-stageSize stage)+1*stageSize stage) at 1 by ring.
          rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
        rewrite offsetId.
        pose proof (fourier_second_half stage (strided p suffix block) (offset-stageSize stage)
          ltac:(lia) ltac:(lia)) as second.
        replace (offset-stageSize stage+stageSize stage) with offset in second by ring.
        symmetry. exact second.
Qed.

Theorem iterativeTransform_correct stage p index : (stage <= 20)%nat ->
  0 <= index < stageSize stage -> congruent (iterativeTransform stage p index) (fourier stage p index).
Proof.
  intros bound range. pose proof (iterativeStages_blocks stage 0 p 0 index ltac:(lia) ltac:(change (0<=0<1); lia) range) as result.
  rewrite Nat.add_0_r in result.
  replace (0*stageSize stage+index) with index in result by ring.
  assert (sample : strided p 0 0=p).
  { apply functional_extensionality. intro i. unfold strided. cbn [bitReverse]. change (p (0+1*i)=p i). f_equal. ring. }
  rewrite sample in result. exact result.
Qed.

Definition swapValues (values : Z -> Z) left right : Z -> Z :=
  fun index => if Z.eqb index left then values right
    else if Z.eqb index right then values left else values index.
Fixpoint reverseSwaps stage count p : Z -> Z :=
  match count with
  | O => p
  | S count => let values := reverseSwaps stage count p in
      let index := Z.of_nat count in
      let reversed := bitReverse stage index in
      if index <? reversed then swapValues values index reversed else values
  end.

Ltac finish_reverse :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] => let decision := fresh "comparison" in
      destruct (Z.ltb a b) eqn:decision;
        [apply Z.ltb_lt in decision | apply Z.ltb_ge in decision]
  end;
  cbn [orb]; try lia; try reflexivity; try (f_equal; lia).

Lemma reverseSwaps_invariant stage count p index :
  Z.of_nat count <= stageSize stage -> 0 <= index < stageSize stage ->
  reverseSwaps stage count p index =
    if (index <? Z.of_nat count) || (bitReverse stage index <? Z.of_nat count)
    then p (bitReverse stage index) else p index.
Proof.
  induction count as [|count IH] in index |- *.
  - intros bound range.
    change (p index = if (index <? 0) || (bitReverse stage index <? 0)
      then p (bitReverse stage index) else p index).
    assert (first : (index <? 0) = false) by (apply Z.ltb_ge; lia).
    assert (second : (bitReverse stage index <? 0) = false) by (apply Z.ltb_ge; pose proof (bitReverse_bounds stage index range); lia).
    rewrite first,second. reflexivity.
  - intros bound range. cbn [reverseSwaps].
    pose proof (bitReverse_bounds stage index range) as reversedRange.
    assert (countRange : 0 <= Z.of_nat count < stageSize stage) by lia.
    pose proof (bitReverse_bounds stage (Z.of_nat count) countRange) as countReversedRange.
    pose proof (bitReverse_involution stage (Z.of_nat count) countRange) as countTwice.
    rewrite Nat2Z.inj_succ.
    destruct (Z.eq_dec index (Z.of_nat count)) as [atCurrent|notCurrent].
    + subst index.
      destruct (Z.of_nat count <? bitReverse stage (Z.of_nat count)) eqn:swap.
      * unfold swapValues. rewrite Z.eqb_refl, IH by lia. rewrite countTwice.
        apply Z.ltb_lt in swap. finish_reverse.
      * rewrite IH by lia. apply Z.ltb_ge in swap. finish_reverse.
    + destruct (Z.eq_dec index (bitReverse stage (Z.of_nat count))) as [atReversed|notReversed].
      * subst index. rewrite countTwice.
        destruct (Z.of_nat count <? bitReverse stage (Z.of_nat count)) eqn:swap.
        -- unfold swapValues.
           rewrite (proj2 (Z.eqb_neq _ _) notCurrent), Z.eqb_refl.
           rewrite IH by lia. apply Z.ltb_lt in swap. finish_reverse.
        -- rewrite IH by lia. rewrite countTwice. apply Z.ltb_ge in swap. finish_reverse.
      * assert (notPair : bitReverse stage index <> Z.of_nat count).
        { intro equal. apply notReversed. rewrite <- (bitReverse_involution stage index range),equal. reflexivity. }
        destruct (Z.of_nat count <? bitReverse stage (Z.of_nat count));
          try unfold swapValues;
          rewrite ?(proj2 (Z.eqb_neq _ _) notCurrent), ?(proj2 (Z.eqb_neq _ _) notReversed);
          cbn;
          rewrite IH by lia.
        all: assert (first : (index <? Z.of_nat count)=(index <? Z.succ (Z.of_nat count))).
        all: try (apply Bool.eq_true_iff_eq; rewrite !Z.ltb_lt; lia).
        all: assert (second : (bitReverse stage index <? Z.of_nat count)=(bitReverse stage index <? Z.succ (Z.of_nat count))).
        all: try (apply Bool.eq_true_iff_eq; rewrite !Z.ltb_lt; lia).
        all: rewrite first,second; reflexivity.
Qed.
Theorem reverseSwaps_correct stage p index : 0 <= index < stageSize stage ->
  reverseSwaps stage (sizeNat stage) p index = p (bitReverse stage index).
Proof.
  intro range. rewrite reverseSwaps_invariant by (try rewrite <- stageSize_nat; lia).
  rewrite <- stageSize_nat. rewrite (proj2 (Z.ltb_lt _ _) (proj2 range)). reflexivity.
Qed.

Fixpoint incrementReverse stage reversed : Z :=
  match stage with
  | O => 0
  | S stage => if reversed <? stageSize stage then reversed+stageSize stage
      else incrementReverse stage (reversed-stageSize stage)
  end.
Lemma bitReverse_zero stage : bitReverse stage 0=0.
Proof.
  induction stage as [|stage IH]; [reflexivity|]. cbn [bitReverse].
  rewrite Z.mod_0_l, Z.div_0_l by lia. rewrite IH. ring.
Qed.
Lemma reverse_even_increment stage q : 0 <= q < stageSize stage ->
  incrementReverse (S stage) (bitReverse (S stage) (2*q)) = bitReverse (S stage) (2*q+1).
Proof.
  intro range. replace (2*q) with (2*q+0) at 1 by ring.
  rewrite !bitReverse_pair by lia. cbn [incrementReverse].
  pose proof (bitReverse_bounds stage q range) as reversedRange.
  assert (small : (0*stageSize stage+bitReverse stage q <? stageSize stage)=true) by (apply Z.ltb_lt; lia).
  rewrite small. ring.
Qed.

Theorem incrementReverse_correct stage index : 0 <= index < stageSize stage ->
  incrementReverse stage (bitReverse stage index) = bitReverse stage ((index+1) mod stageSize stage).
Proof.
  induction stage as [|stage IH] in index |- *.
  - intros range. reflexivity.
  - intro range. pose proof (stageSize_positive stage) as hn.
    rewrite stageSize_succ in range.
    assert (quotientRange : 0 <= index/2 < stageSize stage).
    { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
    pose proof (Z.mod_pos_bound index 2 ltac:(lia)) as remainder.
    pose proof (Z.div_mod index 2 ltac:(lia)) as decomposition.
    destruct (Z.eq_dec (index mod 2) 0) as [even|odd].
    + assert (value : index=2*(index/2)) by lia.
      assert (nextRange : 0<=index+1<stageSize (S stage)) by (rewrite stageSize_succ; lia).
      rewrite Z.mod_small by exact nextRange. rewrite value.
      apply reverse_even_increment. exact quotientRange.
    + assert (odd1 : index mod 2=1) by lia.
      assert (value : index=2*(index/2)+1) by lia.
      pose proof (bitReverse_bounds stage (index/2) quotientRange) as reversedRange.
      replace (bitReverse (S stage) index) with (stageSize stage+bitReverse stage (index/2)).
      2: { pose proof (bitReverse_pair stage (index/2) 1 ltac:(lia)) as pair.
           replace (2*(index/2)+1) with index in pair by lia.
           rewrite Z.mul_1_l in pair. symmetry. exact pair. }
      cbn [incrementReverse].
      rewrite (proj2 (Z.ltb_ge (stageSize stage+bitReverse stage (index/2)) (stageSize stage)) ltac:(lia)).
      replace (stageSize stage+bitReverse stage (index/2)-stageSize stage) with (bitReverse stage (index/2)) by ring.
      rewrite IH by exact quotientRange.
      destruct (Z.eq_dec (index/2+1) (stageSize stage)) as [last|before].
      * rewrite stageSize_succ.
        assert (whole : index+1=2*stageSize stage) by lia.
        rewrite whole, Z.mod_same by lia.
        rewrite last, Z.mod_same by lia. rewrite !bitReverse_zero. reflexivity.
      * assert (nextRange : 0 <= index+1 < stageSize (S stage)) by (rewrite stageSize_succ; lia).
        rewrite (Z.mod_small (index+1) _ nextRange).
        rewrite (Z.mod_small (index/2+1) (stageSize stage) ltac:(lia)).
        replace (index+1) with (2*(index/2+1)+0) by lia.
        rewrite bitReverse_pair by lia. ring.
Qed.

Fixpoint carryLoop fuel reversed bit : Z * Z :=
  match fuel with
  | O => (reversed,bit)
  | S fuel => if (bit =? 0) || (reversed <? bit) then (reversed,bit)
      else carryLoop fuel (reversed-bit) (bit/2)
  end.
Definition carryIncrement fuel reversed bit :=
  let '(reversed,bit) := carryLoop fuel reversed bit in reversed+bit.

Theorem carryIncrement_correct stage fuel reversed : (S stage <= fuel)%nat ->
  0 <= reversed < stageSize stage ->
  carryIncrement fuel reversed (stageSize stage/2) = incrementReverse stage reversed.
Proof.
  induction stage as [|stage IH] in fuel,reversed |- *.
  - intros enough range. change (0<=reversed<1) in range. assert (reversed=0) by lia. subst reversed.
    destruct fuel; [lia|]. reflexivity.
  - intros enough range. destruct fuel as [|fuel]; [lia|].
    rewrite stageSize_succ in range |- *.
    assert (half : 2*stageSize stage/2=stageSize stage).
    { replace (2*stageSize stage) with (stageSize stage*2) by ring. apply Z.div_mul; lia. }
    rewrite half. unfold carryIncrement. cbn [carryLoop incrementReverse].
    pose proof (stageSize_positive stage) as positive.
    rewrite (proj2 (Z.eqb_neq (stageSize stage) 0) ltac:(lia)).
    destruct (reversed <? stageSize stage) eqn:smaller; cbn [orb].
    + reflexivity.
    + apply Z.ltb_ge in smaller.
      change (carryIncrement fuel (reversed-stageSize stage) (stageSize stage/2) =
        incrementReverse stage (reversed-stageSize stage)).
      apply IH; lia.
Qed.
