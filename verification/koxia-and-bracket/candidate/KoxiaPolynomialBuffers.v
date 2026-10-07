From CoqCP Require Import Options SwapUpdate.
From Submission Require Import KoxiaPolynomial KoxiaModular KoxiaFourier KoxiaArrays KoxiaTables KoxiaArrayLoops.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Existing Instance congruent_add.
Definition activeCoefficient (values : list Z) len j :=
  if bool_decide (0<=j<Z.of_nat len) then nth (Z.to_nat j) values 0 else 0.
Lemma activeCoefficient_inside values len j : 0<=j<Z.of_nat len ->
  activeCoefficient values len j=nth (Z.to_nat j) values 0.
Proof. intro range. unfold activeCoefficient. rewrite bool_decide_true by exact range. reflexivity. Qed.
Lemma activeCoefficient_outside values len j : j<0 \/ Z.of_nat len<=j -> activeCoefficient values len j=0.
Proof. intro range. unfold activeCoefficient. rewrite bool_decide_false by lia. reflexivity. Qed.
Lemma activeCoefficient_nat values len index :
  activeCoefficient values len (Z.of_nat index)=if bool_decide ((index<len)%nat) then nth index values 0 else 0.
Proof.
  unfold activeCoefficient. rewrite Nat2Z.id.
  destruct (bool_decide ((index<len)%nat)) eqn:inside.
  - apply bool_decide_eq_true in inside. rewrite bool_decide_true by lia. reflexivity.
  - apply bool_decide_eq_false in inside. rewrite bool_decide_false by lia. reflexivity.
Qed.
Definition ordinaryValue values index :=
  (nth index values 0+(if Nat.eqb index 0 then 0 else nth (index-1) values 0)) mod koxiaModulus.
Definition previousValue (values : list Z) count := match count with O => 0 | S count => nth count values 0 end.
Definition ordinaryBuffer values len := <[len:=previousValue values len]>(fillValues len values 0 (ordinaryValue values)).
Definition specialValue values len index :=
  (nth index values 0+(if bool_decide ((S index<len)%nat) then nth (S index) values 0 else 0)) mod koxiaModulus.
Definition specialBuffer values len := fillValues len values 0 (specialValue values len).
Lemma ordinaryBuffer_length values len : length (ordinaryBuffer values len)=length values.
Proof. unfold ordinaryBuffer. rewrite length_insert,fillValues_length. reflexivity. Qed.
Lemma specialBuffer_length values len : length (specialBuffer values len)=length values.
Proof. unfold specialBuffer. apply fillValues_length. Qed.
Lemma ordinaryBuffer_lookup values len index : (S len<=length values)%nat -> (index<S len)%nat ->
  nth index (ordinaryBuffer values len) 0=
    if Nat.eqb index len then previousValue values len else ordinaryValue values index.
Proof.
  intros room indexBound. unfold ordinaryBuffer. destruct (Nat.eq_dec index len) as [->|different].
  - rewrite nthUpdate by (rewrite fillValues_length; lia). rewrite Nat.eqb_refl. reflexivity.
  - rewrite nthUpdateExcept by (rewrite ?fillValues_length; lia).
    rewrite (proj2 (Nat.eqb_neq index len)) by exact different.
    rewrite fillValues_lookup,bool_decide_true by lia. replace (index-0)%nat with index by lia. reflexivity.
Qed.
Lemma ordinaryBuffer_canonical values len : (S len<=length values)%nat -> tableCanonical values ->
  tableCanonical (ordinaryBuffer values len).
Proof.
  intros room canonical. unfold ordinaryBuffer,tableCanonical. apply Forall_insert.
  - apply fillValues_canonical; [exact canonical|intros; unfold ordinaryValue; apply residue_bounds].
  - destruct len as [|len]; cbn [previousValue]; [pose proof modulus_positive; lia|apply tableCanonical_nth; [exact canonical|lia]].
Qed.
Lemma specialBuffer_canonical values len : tableCanonical values -> tableCanonical (specialBuffer values len).
Proof. intro canonical. unfold specialBuffer. apply fillValues_canonical; [exact canonical|intros; unfold specialValue; apply residue_bounds]. Qed.

Theorem ordinaryBuffer_correct values len : (S len<=length values)%nat -> forall j,
  congruent (activeCoefficient (ordinaryBuffer values len) (S len) j)
    (boundaryStep false (activeCoefficient values len) j).
Proof.
  intros room j. unfold boundaryStep,unrestrictedStep.
  destruct (Z_lt_ge_dec j 0) as [negative|nonnegative].
  - rewrite activeCoefficient_outside by lia. rewrite (proj2 (Z.ltb_lt j 0)) by exact negative. reflexivity.
  - rewrite (proj2 (Z.ltb_ge j 0)) by lia.
    destruct (Z_lt_ge_dec j (Z.of_nat (S len))) as [inside|outside].
    + rewrite activeCoefficient_inside by lia. rewrite ordinaryBuffer_lookup by lia.
      destruct (Nat.eqb (Z.to_nat j) len) eqn:last.
      * apply Nat.eqb_eq in last. assert (j=Z.of_nat len) by lia. subst j.
        rewrite activeCoefficient_outside by lia. destruct len as [|len].
        -- cbn [previousValue]. rewrite activeCoefficient_outside by lia. unfold congruent. cbn. reflexivity.
        -- cbn [previousValue]. rewrite activeCoefficient_inside by lia.
           replace (Z.to_nat (Z.of_nat (S len)-1)) with len by lia. rewrite Z.add_0_l. reflexivity.
      * apply Nat.eqb_neq in last. assert (j<Z.of_nat len) by lia.
        rewrite activeCoefficient_inside by lia. unfold ordinaryValue.
        transitivity (nth (Z.to_nat j) values 0+(if Nat.eqb (Z.to_nat j) 0 then 0 else nth (Z.to_nat j-1) values 0)).
        -- apply congruent_modulo.
        -- apply congruent_equal. f_equal. destruct (Nat.eqb (Z.to_nat j) 0) eqn:zero.
           ++ apply Nat.eqb_eq in zero. rewrite activeCoefficient_outside by lia. reflexivity.
           ++ apply Nat.eqb_neq in zero. rewrite activeCoefficient_inside by lia.
              replace (Z.to_nat (j-1)) with (Z.to_nat j-1)%nat by lia. reflexivity.
    + rewrite !activeCoefficient_outside by lia. reflexivity.
Qed.

Theorem specialBuffer_correct values len : (len<=length values)%nat -> forall j,
  congruent (activeCoefficient (specialBuffer values len) len j)
    (boundaryStep true (activeCoefficient values len) j).
Proof.
  intros room j. unfold boundaryStep,unrestrictedStep.
  destruct (Z_lt_ge_dec j 0) as [negative|nonnegative].
  - rewrite activeCoefficient_outside by lia. rewrite (proj2 (Z.ltb_lt j 0)) by exact negative. reflexivity.
  - rewrite (proj2 (Z.ltb_ge j 0)) by lia.
    destruct (Z_lt_ge_dec j (Z.of_nat len)) as [inside|outside].
    + rewrite activeCoefficient_inside by lia. unfold specialBuffer.
      rewrite fillValues_lookup,bool_decide_true by lia.
      replace (Z.to_nat j-0)%nat with (Z.to_nat j) by lia. unfold specialValue.
      rewrite activeCoefficient_inside by lia.
      transitivity (nth (Z.to_nat j) values 0+(if bool_decide ((S (Z.to_nat j)<len)%nat) then nth (S (Z.to_nat j)) values 0 else 0)).
      * apply congruent_modulo.
      * apply congruent_equal. f_equal. destruct (bool_decide ((S (Z.to_nat j)<len)%nat)) eqn:next.
        -- apply bool_decide_eq_true in next. rewrite activeCoefficient_inside by lia.
           replace (Z.to_nat (j+1)) with (S (Z.to_nat j)) by lia. reflexivity.
        -- apply bool_decide_eq_false in next. rewrite activeCoefficient_outside by lia. reflexivity.
    + rewrite !activeCoefficient_outside by lia. reflexivity.
Qed.
