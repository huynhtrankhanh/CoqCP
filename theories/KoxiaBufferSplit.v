From CoqCP Require Import Options Imperative Execution KoxiaPolynomial KoxiaModular KoxiaFourier KoxiaArrays KoxiaTables
  KoxiaArrayLoops KoxiaPolynomialBuffers KoxiaConvolutionCorrect.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.

Lemma activeCoefficient_low values len cut :
  activeCoefficient values (Nat.min len cut)=low (Z.of_nat cut) (activeCoefficient values len).
Proof.
  apply functional_extensionality. intro j. unfold activeCoefficient,low.
  destruct (Z_lt_ge_dec j 0) as [negative|nonnegative].
  - rewrite !bool_decide_false by lia. destruct (j <? Z.of_nat cut); reflexivity.
  - destruct (Z_lt_ge_dec j (Z.of_nat cut)) as [below|above].
    + rewrite (proj2 (Z.ltb_lt j (Z.of_nat cut))) by exact below.
      destruct (Z_lt_ge_dec j (Z.of_nat len)) as [inside|outside].
      * rewrite !bool_decide_true by (rewrite ?Nat2Z.inj_min; lia). reflexivity.
      * rewrite !bool_decide_false by (rewrite ?Nat2Z.inj_min; lia). reflexivity.
    + rewrite (proj2 (Z.ltb_ge j (Z.of_nat cut))) by lia.
      rewrite bool_decide_false by (rewrite Nat2Z.inj_min; lia). reflexivity.
Qed.
Lemma tailCoefficient_shift state len skip : (skip<=len)%nat ->
  tailCoefficient state len skip=KoxiaPolynomial.shift (Z.of_nat skip) (high (Z.of_nat skip)
    (activeCoefficient (memory state arraydef_0__poly) len)).
Proof.
  intro width. apply functional_extensionality. intro j. unfold tailCoefficient,KoxiaPolynomial.shift,high,activeCoefficient.
  destruct (Z_lt_ge_dec j 0) as [negative|nonnegative].
  - rewrite bool_decide_false by lia. rewrite (proj2 (Z.ltb_lt (j+Z.of_nat skip) (Z.of_nat skip))) by lia. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (j+Z.of_nat skip) (Z.of_nat skip))) by lia.
    destruct (Z_lt_ge_dec j (Z.of_nat (len-skip))) as [inside|outside].
    + rewrite !bool_decide_true by lia. f_equal. rewrite Z2Nat.inj_add by lia.
      rewrite Nat2Z.id. lia.
    + rewrite !bool_decide_false by lia. reflexivity.
Qed.

Definition mergeValue values len saved savedLen index :=
  (activeCoefficient values len (Z.of_nat index)+activeCoefficient saved savedLen (Z.of_nat index)) mod koxiaModulus.
Definition mergeBuffer values len saved savedLen :=
  fillValues (Nat.max len savedLen) values 0 (mergeValue values len saved savedLen).
Lemma mergeBuffer_length values len saved savedLen : length (mergeBuffer values len saved savedLen)=length values.
Proof. unfold mergeBuffer. apply fillValues_length. Qed.
Lemma mergeBuffer_canonical values len saved savedLen : tableCanonical values ->
  tableCanonical (mergeBuffer values len saved savedLen).
Proof. intro canonical. unfold mergeBuffer. apply fillValues_canonical; [exact canonical|intros; unfold mergeValue; apply residue_bounds]. Qed.
Theorem mergeBuffer_correct values len saved savedLen : (Nat.max len savedLen<=length values)%nat -> forall j,
  congruent (activeCoefficient (mergeBuffer values len saved savedLen) (Nat.max len savedLen) j)
    (KoxiaPolynomial.plus (activeCoefficient values len) (activeCoefficient saved savedLen) j).
Proof.
  intros room j. unfold KoxiaPolynomial.plus. destruct (Z_lt_ge_dec j 0) as [negative|nonnegative].
  - rewrite !activeCoefficient_outside by lia. reflexivity.
  - destruct (Z_lt_ge_dec j (Z.of_nat (Nat.max len savedLen))) as [inside|outside].
    + rewrite activeCoefficient_inside by lia. unfold mergeBuffer.
      assert (fillRoom : (0+Nat.max len savedLen<=length values)%nat) by lia.
      assert (indexRange : (0<=Z.to_nat j<0+Nat.max len savedLen)%nat) by lia.
      rewrite fillValues_lookup by exact fillRoom. rewrite bool_decide_true by exact indexRange.
      replace (Z.to_nat j-0)%nat with (Z.to_nat j) by lia. unfold mergeValue.
      rewrite Z2Nat.id by lia. apply congruent_modulo.
    + rewrite !activeCoefficient_outside by (rewrite ?Nat2Z.inj_max in outside; lia). reflexivity.
Qed.

Lemma binomialTransform_bounded width span p :
  (forall j, j<0 \/ Z.of_nat width<=j -> p j=0) ->
  forall j, j<0 \/ Z.of_nat (width+span)<=j -> binomialTransform span p j=0.
Proof.
  intros support. induction span as [|span IH]; intros j outside.
  - cbn [binomialTransform]. apply support. rewrite Nat.add_0_r in outside. exact outside.
  - change (binomialTransform span p j+binomialTransform span p (j-1)=0).
    rewrite !IH by lia. ring.
Qed.
Lemma tailCoefficient_bounded state len cut j : j<0 \/ Z.of_nat (len-cut)<=j -> tailCoefficient state len cut j=0.
Proof. intro outside. unfold tailCoefficient. rewrite bool_decide_false by lia. reflexivity. Qed.
Lemma bulk_tail_bounded state len cut span j :
  j<0 \/ Z.of_nat (len-cut+span)<=j -> binomialTransform span (tailCoefficient state len cut) j=0.
Proof. apply binomialTransform_bounded. intros index outside. apply tailCoefficient_bounded. exact outside. Qed.
