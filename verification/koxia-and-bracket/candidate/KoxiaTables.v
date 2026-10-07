From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaPower KoxiaArrays KoxiaRoots KoxiaFourier KoxiaBinomial.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.
Local Existing Instance congruent_equivalence.
Local Opaque fastPower modularPower stageRoot stageInverse.

Definition tableRead name index : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (arrayType _ environment1 name) :=
  Dispatch _ _ _ (Retrieve _ _ name index) (fun value => Done _ _ _ value).
Definition tableWrite name index (value : arrayType _ environment1 name) : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  Dispatch _ _ _ (Store _ _ name index value) (fun _ => Done _ _ _ tt).

Definition intValues (name : arrayIndex1) (values : list Z) : list (arrayType _ environment1 name) :=
  match name return list (arrayType _ environment1 name) with
  | arraydef_0__sequence => values
  | arraydef_0__prefix => values
  | arraydef_0__factorial => values
  | arraydef_0__inverseFactorial => values
  | arraydef_0__roots => values
  | arraydef_0__work => values
  | arraydef_0__other => values
  | arraydef_0__poly => values
  | arraydef_0__arena => values
  | arraydef_0__result => values
  | arraydef_0__printBuffer => values
  | arraydef_0__frames => []
  end.
Definition intValue (name : arrayIndex1) (value : Z) : arrayType _ environment1 name :=
  match name return arrayType _ environment1 name with
  | arraydef_0__sequence => value
  | arraydef_0__prefix => value
  | arraydef_0__factorial => value
  | arraydef_0__inverseFactorial => value
  | arraydef_0__roots => value
  | arraydef_0__work => value
  | arraydef_0__other => value
  | arraydef_0__poly => value
  | arraydef_0__arena => value
  | arraydef_0__result => value
  | arraydef_0__printBuffer => value
  | arraydef_0__frames => (0,0,0,0,0)
  end.
Definition fromIntArray (name : arrayIndex1) : arrayType _ environment1 name -> Z :=
  match name return arrayType _ environment1 name -> Z with
  | arraydef_0__sequence => fun value => value
  | arraydef_0__prefix => fun value => value
  | arraydef_0__factorial => fun value => value
  | arraydef_0__inverseFactorial => fun value => value
  | arraydef_0__roots => fun value => value
  | arraydef_0__work => fun value => value
  | arraydef_0__other => fun value => value
  | arraydef_0__poly => fun value => value
  | arraydef_0__arena => fun value => value
  | arraydef_0__result => fun value => value
  | arraydef_0__printBuffer => fun value => value
  | arraydef_0__frames => fun _ => 0
  end.

Fixpoint chainValues count (values : list Z) start (factor : nat -> Z) : list Z :=
  match count with
  | O => values
  | S index => let previous := chainValues index values start factor in
      <[(start+S index)%nat := (nth (start+index) previous 0*factor index) mod koxiaModulus]>previous
  end.
Fixpoint chainProduct seed (factor : nat -> Z) count :=
  match count with O => seed | S count => (chainProduct seed factor count*factor count) mod koxiaModulus end.
Lemma chainValues_length count values start factor :
  length (chainValues count values start factor)=length values.
Proof. induction count as [|count IH]; cbn [chainValues]; rewrite ?length_insert,?IH; reflexivity. Qed.
Lemma chainValues_lookup count values start factor index :
  (start+count<length values)%nat -> (index<=count)%nat ->
  nth (start+index) (chainValues count values start factor) 0=
    chainProduct (nth start values 0) factor index.
Proof.
  induction count as [|count IH] in index |- *.
  - intros room bound. assert (index=0)%nat by lia. subst index.
    cbn [chainValues chainProduct]. rewrite Nat.add_0_r. reflexivity.
  - intros room bound. cbn [chainValues].
    destruct (Nat.eq_dec index (S count)) as [last|earlier].
    + subst index. rewrite nthUpdate by (rewrite chainValues_length; exact room).
      cbn [chainProduct]. rewrite IH by lia. reflexivity.
    + rewrite nthUpdateExcept by (rewrite ?chainValues_length; lia).
      apply IH; lia.
Qed.

Definition chainStep (name : arrayIndex1) 
  start index factor : Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  tableRead name (Z.of_nat (start+index)) >>= fun value =>
  tableWrite name (Z.of_nat (start+S index))
    (intValue name (machineProduct (fromIntArray name value) factor)).

Lemma chainStep_execution name state values start index factor :
  name<>arraydef_0__frames -> (start+S index<length values)%nat ->
  0<=nth (start+index) values 0<koxiaModulus -> 0<=factor<koxiaModulus ->
  exec (chainStep name start index factor) (withArray state name (intValues name values)) =
  Some (tt,withArray state name
    (intValues name (<[(start+S index)%nat := (nth (start+index) values 0*factor) mod koxiaModulus]>values))).
Proof.
  intros notFrames. destruct name; try contradiction.
  all: intros room valueRange factorRange; unfold chainStep,tableRead,tableWrite,intValue,intValues,fromIntArray.
  all: cbn [bind].
  all: match goal with
    | |- exec (Dispatch _ _ _ (Retrieve _ _ ?name _) _) _ = _ =>
      rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1
        unit state name values (start+index) 0) by (cbn; lia)
    end.
  all: unfold machineProduct; rewrite residue_product_coerce by assumption.
  all: rewrite execStoreArray by exact room; reflexivity.
Qed.

Definition tableCanonical := Forall (fun value => 0<=value<koxiaModulus).
Lemma tableCanonical_nth values index : tableCanonical values -> (index<length values)%nat ->
  0<=nth index values 0<koxiaModulus.
Proof.
  unfold tableCanonical. rewrite (Forall_nth (fun value => 0<=value<koxiaModulus) 0 values).
  intros canonical bound. apply canonical. exact bound.
Qed.
Lemma chainValues_canonical count values start factor : tableCanonical values ->
  tableCanonical (chainValues count values start factor).
Proof.
  intro canonical. induction count as [|count IH]; [exact canonical|]. cbn [chainValues].
  unfold tableCanonical in *. apply Forall_insert; [exact IH|apply residue_bounds].
Qed.
Fixpoint chainAction fuel total name start factor : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with
  | O => Done _ _ _ tt
  | S fuel => let index := (total-fuel-1)%nat in
    chainStep name start index (factor index) >>= fun _ => chainAction fuel total name start factor
  end.
Theorem chainAction_execution fuel count total name state values start factor :
  name<>arraydef_0__frames -> (count+fuel=total)%nat -> (start+total<length values)%nat ->
  tableCanonical values -> (forall index, (index<total)%nat -> 0<=factor index<koxiaModulus) ->
  exec (chainAction fuel total name start factor)
    (withArray state name (intValues name (chainValues count values start factor))) =
  Some (tt,withArray state name (intValues name (chainValues total values start factor))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros notFrames countFuel room canonical factorRange.
    assert (count=total) by lia. subst count. reflexivity.
  - intros notFrames countFuel room canonical factorRange.
    cbn [chainAction]. replace (total-fuel-1)%nat with count by lia.
    rewrite exec_bind,chainStep_execution.
    2: exact notFrames.
    2: rewrite chainValues_length; lia.
    2: apply tableCanonical_nth; [apply chainValues_canonical; exact canonical|rewrite chainValues_length; lia].
    2: apply factorRange; lia.
    cbn [optionBind fst snd]. apply (IH (S count)); [exact notFrames|lia|exact room|exact canonical|exact factorRange].
Qed.

Lemma chainProduct_factorial count :
  chainProduct 1 (fun index => Z.of_nat (S index)) count=factorialMod count.
Proof.
  induction count as [|count IH]; [reflexivity|]. cbn [chainProduct factorialMod]. rewrite IH. reflexivity.
Qed.

Lemma chainProduct_constant factor count :
  chainProduct 1 (fun _ => factor) count=factor^Z.of_nat count mod koxiaModulus.
Proof.
  induction count as [|count IH].
  - cbn [chainProduct Z.pow]. symmetry. apply Z.mod_small. unfold koxiaModulus; lia.
  - cbn [chainProduct]. rewrite IH,Nat2Z.inj_succ,Z.pow_succ_r by lia.
    rewrite mod_mul_left by (pose proof modulus_positive; lia).
    replace (factor*factor^Z.of_nat count) with (factor^Z.of_nat count*factor) by ring. reflexivity.
Qed.
Definition rootBlock stage values :=
  chainValues (sizeNat stage-1) (<[sizeNat stage:=1]>values) (sizeNat stage)
    (fun _ => stageRoot (S stage)).
Lemma rootBlock_length stage values : length (rootBlock stage values)=length values.
Proof. unfold rootBlock. rewrite chainValues_length,length_insert. reflexivity. Qed.
Lemma rootBlock_lookup stage values offset :
  (stage<20)%nat -> (sizeNat stage+sizeNat stage<=length values)%nat -> (offset<sizeNat stage)%nat ->
  congruent (nth (sizeNat stage+offset) (rootBlock stage values) 0)
    (rootPower (S stage) (Z.of_nat offset)).
Proof.
  intros bound room offsetBound. pose proof (stageSize_positive stage) as positive.
  rewrite stageSize_nat in positive. unfold rootBlock.
  rewrite chainValues_lookup by (rewrite ?length_insert; lia).
  rewrite nthUpdate by lia. rewrite chainProduct_constant.
  transitivity (stageRoot (S stage)^Z.of_nat offset).
  - apply congruent_modulo.
  - symmetry. apply rootPower_unrestricted; lia.
Qed.
Lemma rootBlock_canonical stage values : tableCanonical values -> tableCanonical (rootBlock stage values).
Proof.
  intro canonical. unfold rootBlock. apply chainValues_canonical.
  unfold tableCanonical in *. apply Forall_insert; [exact canonical|unfold koxiaModulus; lia].
Qed.
Lemma chainValues_outside count values start factor index :
  (start+count<length values)%nat -> ((index<=start)%nat \/ (start+count<index)%nat) ->
  nth index (chainValues count values start factor) 0=nth index values 0.
Proof.
  induction count as [|count IH]; [reflexivity|]. intros room outside. cbn [chainValues].
  rewrite nthUpdateExcept by (rewrite ?chainValues_length; lia). apply IH; lia.
Qed.
Lemma rootBlock_outside stage values index :
  (sizeNat stage+sizeNat stage<=length values)%nat ->
  ((index<sizeNat stage)%nat \/ (sizeNat stage+sizeNat stage<=index)%nat) ->
  nth index (rootBlock stage values) 0=nth index values 0.
Proof.
  intros room outside. pose proof (stageSize_positive stage) as positive.
  rewrite stageSize_nat in positive. unfold rootBlock.
  rewrite chainValues_outside by (rewrite ?length_insert; lia).
  rewrite nthUpdateExcept by lia. reflexivity.
Qed.

Theorem rootBlock_execution stage state values :
  (stage<20)%nat -> (sizeNat stage+sizeNat stage<=length values)%nat -> tableCanonical values ->
  exec (tableWrite arraydef_0__roots (stageSize stage) 1 >>= fun _ =>
    chainAction (sizeNat stage-1) (sizeNat stage-1) arraydef_0__roots (sizeNat stage)
      (fun _ => stageRoot (S stage)))
    (withArray state arraydef_0__roots values) =
  Some (tt,withArray state arraydef_0__roots (rootBlock stage values)).
Proof.
  intros bound room canonical. pose proof (stageSize_positive stage) as positive.
  rewrite stageSize_nat in positive. unfold tableWrite. rewrite stageSize_nat.
  cbn [bind]. rewrite (@execStoreArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1
    unit state arraydef_0__roots values (sizeNat stage) 1) by (cbn; lia).
  replace (<[sizeNat stage:=1]>values) with
    (chainValues 0 (<[sizeNat stage:=1]>values) (sizeNat stage) (fun _ => stageRoot (S stage))) at 1 by reflexivity.
  change (exec (chainAction (sizeNat stage-1) (sizeNat stage-1) arraydef_0__roots (sizeNat stage)
    (fun _ => stageRoot (S stage)))
    (withArray state arraydef_0__roots
      (intValues arraydef_0__roots (chainValues 0 (<[sizeNat stage:=1]>values) (sizeNat stage)
        (fun _ => stageRoot (S stage))))) =
    Some (tt,withArray state arraydef_0__roots
      (intValues arraydef_0__roots (chainValues (sizeNat stage-1) (<[sizeNat stage:=1]>values)
        (sizeNat stage) (fun _ => stageRoot (S stage)))))).
  apply chainAction_execution; [congruence|lia|rewrite length_insert; lia| |].
  - unfold tableCanonical in *. apply Forall_insert; [exact canonical|unfold koxiaModulus; lia].
  - intros. apply stageRoot_bounds.
Qed.

Fixpoint rootTableValues stages values :=
  match stages with O => values | S stage => rootBlock stage (rootTableValues stage values) end.
Lemma rootTableValues_length stages values : length (rootTableValues stages values)=length values.
Proof. induction stages as [|stage IH]; cbn [rootTableValues]; rewrite ?rootBlock_length,?IH; reflexivity. Qed.
Lemma rootTableValues_canonical stages values : tableCanonical values -> tableCanonical (rootTableValues stages values).
Proof. intro canonical. induction stages as [|stage IH]; cbn [rootTableValues]; [exact canonical|apply rootBlock_canonical; exact IH]. Qed.
Lemma sizeNat_succ stage : sizeNat (S stage)=(sizeNat stage+sizeNat stage)%nat.
Proof. apply Nat2Z.inj. rewrite Nat2Z.inj_add,<-!stageSize_nat,stageSize_succ. ring. Qed.
Lemma sizeNat_mono small large : (small<=large)%nat -> (sizeNat small<=sizeNat large)%nat.
Proof. intro bound. apply Nat2Z.inj_le. rewrite <-!stageSize_nat. unfold stageSize. apply Z.pow_le_mono_r; lia. Qed.
Theorem rootTableValues_correct stages values step offset :
  (stages<=20)%nat -> (sizeNat stages<=length values)%nat ->
  (step<stages)%nat -> (offset<sizeNat step)%nat ->
  congruent (nth (sizeNat step+offset) (rootTableValues stages values) 0)
    (rootPower (S step) (Z.of_nat offset)).
Proof.
  induction stages as [|stage IH]; [lia|]. intros bound room stepBound offsetBound.
  cbn [rootTableValues].
  destruct (Nat.eq_dec step stage) as [last|earlier].
  - subst step. apply rootBlock_lookup; [lia|rewrite rootTableValues_length,<-sizeNat_succ; exact room|exact offsetBound].
  - rewrite rootBlock_outside.
    + apply IH; [lia|pose proof (sizeNat_mono stage (S stage) ltac:(lia)); lia|lia|exact offsetBound].
    + rewrite rootTableValues_length,<-sizeNat_succ. exact room.
    + left. pose proof (sizeNat_mono (S step) stage ltac:(lia)) as sizeBound.
      rewrite sizeNat_succ in sizeBound. lia.
Qed.

Fixpoint backwardValues count (values : list Z) total :=
  match count with
  | O => values
  | S count => let current := (total-count)%nat in
    let previous := backwardValues count values total in
    <[(total-S count)%nat := (nth current previous 0*Z.of_nat current) mod koxiaModulus]>previous
  end.
Lemma backwardValues_length count values total : length (backwardValues count values total)=length values.
Proof. induction count as [|count IH]; cbn [backwardValues]; rewrite ?length_insert,?IH; reflexivity. Qed.
Lemma backwardValues_canonical count values total : tableCanonical values -> tableCanonical (backwardValues count values total).
Proof.
  intro canonical. induction count as [|count IH]; [exact canonical|]. cbn [backwardValues].
  unfold tableCanonical in *. apply Forall_insert; [exact IH|apply residue_bounds].
Qed.
Theorem backwardValues_inverse count values total index :
  (count<=total<length values)%nat -> Z.of_nat total<koxiaModulus ->
  nth total values 0=inverseFactorialMod total -> (total-count<=index<=total)%nat ->
  nth index (backwardValues count values total) 0=inverseFactorialMod index.
Proof.
  induction count as [|count IH] in index |- *.
  - intros bounds small seed range. assert (index=total) by lia. subst index. exact seed.
  - intros bounds small seed range. cbn [backwardValues].
    destruct (Nat.eq_dec index ((total-S count)%nat)) as [atNew|old].
    + subst index. rewrite nthUpdate by (rewrite backwardValues_length; lia).
      rewrite IH by lia.
      assert (successor : (total-count)%nat=S (total-S count)) by lia.
      rewrite successor. apply inverseFactorialMod_step. lia.
    + rewrite nthUpdateExcept by (rewrite ?backwardValues_length; lia). apply IH; lia.
Qed.

Definition backwardStep name index : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  tableRead name (Z.of_nat (S index)) >>= fun value =>
  tableWrite name (Z.of_nat index)
    (intValue name (machineProduct (fromIntArray name value) (Z.of_nat (S index)))).
Lemma backwardStep_execution name state values index : name<>arraydef_0__frames ->
  (S index<length values)%nat -> Z.of_nat (S index)<koxiaModulus ->
  0<=nth (S index) values 0<koxiaModulus ->
  exec (backwardStep name index) (withArray state name (intValues name values))=
  Some (tt,withArray state name
    (intValues name (<[index := (nth (S index) values 0*Z.of_nat (S index)) mod koxiaModulus]>values))).
Proof.
  intros notFrames. destruct name; try contradiction.
  all: intros room indexBound valueRange; unfold backwardStep,tableRead,tableWrite,intValue,fromIntArray,intValues.
  all: cbn [bind].
  all: match goal with
    | |- exec (Dispatch _ _ _ (Retrieve _ _ ?name _) _) _ = _ =>
      rewrite (@execReadArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1
        unit state name values (S index) 0) by (cbn; lia)
    end.
  all: unfold machineProduct; rewrite residue_product_coerce by (first [assumption|split; [apply Nat2Z.is_nonneg|exact indexBound]]).
  all: rewrite execStoreArray by (cbn; lia); reflexivity.
Qed.
Fixpoint backwardAction fuel name : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit :=
  match fuel with O => Done _ _ _ tt | S fuel => backwardStep name fuel >>= fun _ => backwardAction fuel name end.
Theorem backwardAction_execution fuel count total name state values :
  name<>arraydef_0__frames -> (count+fuel=total)%nat -> (total<length values)%nat ->
  Z.of_nat total<koxiaModulus -> tableCanonical values ->
  exec (backwardAction fuel name) (withArray state name (intValues name (backwardValues count values total)))=
  Some (tt,withArray state name (intValues name (backwardValues total values total))).
Proof.
  induction fuel as [|fuel IH] in count |- *.
  - intros notFrames countFuel room small canonical. assert (count=total) by lia. subst count. reflexivity.
  - intros notFrames countFuel room small canonical. cbn [backwardAction].
    rewrite exec_bind,backwardStep_execution.
    2: exact notFrames.
    2: rewrite backwardValues_length; lia.
    2: lia.
    2: apply tableCanonical_nth; [apply backwardValues_canonical; exact canonical|rewrite backwardValues_length; lia].
    cbn [optionBind fst snd].
    pose proof (IH (S count) notFrames ltac:(lia) room small canonical) as finish.
    cbn [backwardValues] in finish.
    replace (total-count)%nat with (S fuel) in finish by lia.
    replace (total-S count)%nat with fuel in finish by lia. exact finish.
Qed.

Definition factorialTableValues total values :=
  chainValues total (<[(0%nat):=1]>values) 0 (fun index => Z.of_nat (S index)).
Definition factorialTableAction total :=
  tableWrite arraydef_0__factorial 0 1 >>= fun _ =>
  chainAction total total arraydef_0__factorial 0 (fun index => Z.of_nat (S index)).
Lemma factorialTableValues_lookup total values index : (total<length values)%nat -> (index<=total)%nat ->
  nth index (factorialTableValues total values) 0=factorialMod index.
Proof.
  intros room bound. unfold factorialTableValues.
  replace index with (0+index)%nat at 1 by lia.
  rewrite chainValues_lookup by (rewrite ?length_insert; lia).
  rewrite nthUpdate by lia. apply chainProduct_factorial.
Qed.
Lemma factorialTableValues_length total values : length (factorialTableValues total values)=length values.
Proof. unfold factorialTableValues. rewrite chainValues_length,length_insert. reflexivity. Qed.
Lemma factorialTableValues_canonical total values : tableCanonical values -> tableCanonical (factorialTableValues total values).
Proof.
  intro canonical. unfold factorialTableValues. apply chainValues_canonical.
  unfold tableCanonical in *. apply Forall_insert; [exact canonical|unfold koxiaModulus; lia].
Qed.
Theorem factorialTableAction_execution total state values : (total<length values)%nat ->
  Z.of_nat total<koxiaModulus -> tableCanonical values ->
  exec (factorialTableAction total) (withArray state arraydef_0__factorial values)=
  Some (tt,withArray state arraydef_0__factorial (factorialTableValues total values)).
Proof.
  intros room small canonical. unfold factorialTableAction,tableWrite. cbn [bind].
  replace 0 with (Z.of_nat 0) at 1 by reflexivity.
  rewrite (@execStoreArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1
    unit state arraydef_0__factorial values 0 1) by (cbn; lia).
  change (exec (chainAction total total arraydef_0__factorial 0 (fun index => Z.of_nat (S index)))
    (withArray state arraydef_0__factorial
      (intValues arraydef_0__factorial (chainValues 0 (<[(0%nat):=1]>values) 0 (fun index => Z.of_nat (S index)))))=
    Some (tt,withArray state arraydef_0__factorial
      (intValues arraydef_0__factorial (chainValues total (<[(0%nat):=1]>values) 0 (fun index => Z.of_nat (S index)))))).
  apply chainAction_execution; [congruence|lia|rewrite length_insert; lia| |intros; lia].
  unfold tableCanonical in *. apply Forall_insert; [exact canonical|unfold koxiaModulus; lia].
Qed.

Definition inverseFactorialTableValues total values :=
  backwardValues total (<[total:=inverseFactorialMod total]>values) total.
Definition inverseFactorialTableAction total :=
  tableWrite arraydef_0__inverseFactorial (Z.of_nat total) (inverseFactorialMod total) >>= fun _ =>
  backwardAction total arraydef_0__inverseFactorial.
Lemma inverseFactorialTableValues_lookup total values index :
  (total<length values)%nat -> Z.of_nat total<koxiaModulus -> (index<=total)%nat ->
  nth index (inverseFactorialTableValues total values) 0=inverseFactorialMod index.
Proof.
  intros room small bound. unfold inverseFactorialTableValues. apply backwardValues_inverse.
  - rewrite length_insert. lia.
  - exact small.
  - rewrite nthUpdate by exact room. reflexivity.
  - lia.
Qed.
Lemma inverseFactorialTableValues_length total values : length (inverseFactorialTableValues total values)=length values.
Proof. unfold inverseFactorialTableValues. rewrite backwardValues_length,length_insert. reflexivity. Qed.
Lemma inverseFactorialTableValues_canonical total values : tableCanonical values -> tableCanonical (inverseFactorialTableValues total values).
Proof.
  intro canonical. unfold inverseFactorialTableValues. apply backwardValues_canonical.
  unfold tableCanonical in *. apply Forall_insert; [exact canonical|unfold inverseFactorialMod; apply modularPower_bounds].
Qed.
Theorem inverseFactorialTableAction_execution total state values : (total<length values)%nat ->
  Z.of_nat total<koxiaModulus -> tableCanonical values ->
  exec (inverseFactorialTableAction total) (withArray state arraydef_0__inverseFactorial values)=
  Some (tt,withArray state arraydef_0__inverseFactorial (inverseFactorialTableValues total values)).
Proof.
  intros room small canonical. unfold inverseFactorialTableAction,tableWrite. cbn [bind].
  rewrite (@execStoreArray arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1
    unit state arraydef_0__inverseFactorial values total (inverseFactorialMod total)) by exact room.
  change (exec (backwardAction total arraydef_0__inverseFactorial)
    (withArray state arraydef_0__inverseFactorial
      (intValues arraydef_0__inverseFactorial (backwardValues 0 (<[total:=inverseFactorialMod total]>values) total)))=
    Some (tt,withArray state arraydef_0__inverseFactorial
      (intValues arraydef_0__inverseFactorial (backwardValues total (<[total:=inverseFactorialMod total]>values) total)))).
  apply backwardAction_execution; [congruence|lia|rewrite length_insert; exact room|exact small|].
  unfold tableCanonical in *. apply Forall_insert; [exact canonical|unfold inverseFactorialMod; apply modularPower_bounds].
Qed.
