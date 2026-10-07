From CoqCP Require Import Options Imperative Execution KoxiaModular KoxiaIntegers KoxiaPower KoxiaRadix KoxiaArrays KoxiaRoots KoxiaFourier KoxiaNTT SwapUpdate.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.

Definition nttOffsetBody (half : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt)
  withLocalVariablesReturnValue LoopOutcome :=
(fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub half (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
      (liftToWithinLoop (((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left) x)) >>=
      fun _ => (liftToWithinLoop ((modIntUnsigned (multInt 64 ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) binder_2) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__roots) x) ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right) x)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) >>= fun x => ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => ((modIntUnsigned (subInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left)) (Done _ _ _ 998244353%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
      fun _ => Done _ _ _ tt
    ))).

Definition butterflyNums (nums : varsfuncdef_0__ntt -> Z) left right :=
  fun name => match name with
  | vardef_0__ntt_left => left
  | vardef_0__ntt_right => right
  | _ => nums name
  end.
Lemma butterflyNums_left nums old right left :
  update (butterflyNums nums old right) vardef_0__ntt_left left=butterflyNums nums left right.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma butterflyNums_right nums left old right :
  update (butterflyNums nums left old) vardef_0__ntt_right right=butterflyNums nums left right.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma butterflyNums_self nums : butterflyNums nums (nums vardef_0__ntt_left) (nums vardef_0__ntt_right)=nums.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Definition nttRead name index :=
  Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue _
    (Retrieve _ _ name index) (fun value => Done _ _ _ value).
Definition nttWrite name index (value : arrayType _ environment1 name) :=
  Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit
    (Store _ _ name index value) (fun _ => Done _ _ _ tt).
Definition butterflyAction nums offset :=
  let leftIndex := coerceInt (nums vardef_0__ntt_start+offset) 64 in
  let rightIndex := coerceInt (leftIndex+nums vardef_0__ntt_k) 64 in
  let rootIndex := coerceInt (nums vardef_0__ntt_k+offset) 64 in
  nttRead arraydef_0__work leftIndex >>= fun left =>
  nttRead arraydef_0__roots rootIndex >>= fun root =>
  nttRead arraydef_0__work rightIndex >>= fun value =>
  let right := machineProduct root value in
  nttWrite arraydef_0__work leftIndex (coerceInt (left+right) 64 mod koxiaModulus) >>= fun _ =>
  nttWrite arraydef_0__work rightIndex (coerceInt (coerceInt (left+koxiaModulus) 64-right) 64 mod koxiaModulus) >>= fun _ =>
  Done _ _ _ (butterflyNums nums left right).
Create Rewrite HintDb koxia_butterfly_steps.
#[local] Hint Rewrite butterflyNums_left butterflyNums_right
  @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 : koxia_butterfly_steps.
Ltac normalize_butterfly := repeat progress
  (autorewrite with advance_program koxia_butterfly_steps; try rewrite <- !bindAssoc;
   try rewrite decide_False by lia; cbn [bind butterflyNums]).
Lemma nttOffsetNormalized b nums half oldLeft oldRight remaining continuation :
  eliminateLocalVariables b (butterflyNums nums oldLeft oldRight)
    (nttOffsetBody half remaining >>= continuation) =
  butterflyAction nums (half-Z.of_nat remaining-1) >>= fun final =>
    eliminateLocalVariables b final (continuation KeepGoing).
Proof.
  unfold nttOffsetBody, numberLocalGet, numberLocalSet, retrieve, store, addInt,
    subInt, multInt, modIntUnsigned.
  normalize_butterfly.
  unfold butterflyAction, nttRead, nttWrite, machineProduct, koxiaModulus. cbn [bind].
  f_equal. apply functional_extensionality. intro left. normalize_butterfly.
  f_equal. apply functional_extensionality. intro root. normalize_butterfly.
  f_equal. apply functional_extensionality. intro value. normalize_butterfly.
  reflexivity.
Qed.

Definition butterflyValues values roots start half offset :=
  let left := nth (start+offset) values 0 in
  let right := (nth (half+offset) roots 0 * nth (start+offset+half) values 0) mod koxiaModulus in
  <[(start+offset+half)%nat := (left-right) mod koxiaModulus]>
    (<[(start+offset)%nat := (left+right) mod koxiaModulus]>values).
Lemma butterflyValues_length values roots start half offset :
  length (butterflyValues values roots start half offset)=length values.
Proof. unfold butterflyValues. rewrite !length_insert. reflexivity. Qed.
Lemma modular_difference x y : (x+koxiaModulus-y) mod koxiaModulus=(x-y) mod koxiaModulus.
Proof.
  replace (x+koxiaModulus-y) with ((x-y)+1*koxiaModulus) by ring.
  rewrite Z.mod_add by (pose proof modulus_positive; lia). reflexivity.
Qed.

Theorem butterflyAction_execution state values nums start half offset :
  nums vardef_0__ntt_start=Z.of_nat start -> nums vardef_0__ntt_k=Z.of_nat half ->
  (start+offset+half<length values)%nat ->
  (half+offset<length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  0<=nth (start+offset) values 0<koxiaModulus ->
  0<=nth (start+offset+half) values 0<koxiaModulus ->
  0<=nth (half+offset) (memory state arraydef_0__roots) 0<koxiaModulus ->
  exec (butterflyAction nums (Z.of_nat offset)) (withWork state values) =
  Some (butterflyNums nums (nth (start+offset) values 0)
      ((nth (half+offset) (memory state arraydef_0__roots) 0 * nth (start+offset+half) values 0) mod koxiaModulus),
    withWork state (butterflyValues values (memory state arraydef_0__roots) start half offset)).
Proof.
  intros startEq halfEq workBound rootBound workFit rootFit leftRange valueRange rootRange.
  unfold butterflyAction. rewrite startEq, halfEq.
  assert (leftAddress : coerceInt (Z.of_nat start+Z.of_nat offset) 64=Z.of_nat (start+offset)).
  { rewrite <- Nat2Z.inj_add. apply coerce64_small. change (0<=Z.of_nat (start+offset)<18446744073709551616). lia. }
  assert (rightAddress : coerceInt (Z.of_nat (start+offset)+Z.of_nat half) 64=Z.of_nat (start+offset+half)).
  { rewrite <- Nat2Z.inj_add. apply coerce64_small. change (0<=Z.of_nat (start+offset+half)<18446744073709551616). lia. }
  assert (rootAddress : coerceInt (Z.of_nat half+Z.of_nat offset) 64=Z.of_nat (half+offset)).
  { rewrite <- Nat2Z.inj_add. apply coerce64_small. change (0<=Z.of_nat (half+offset)<18446744073709551616). lia. }
  rewrite leftAddress,rightAddress,rootAddress.
  unfold nttRead. cbn [bind]. rewrite execReadWork by lia.
  rewrite (@KoxiaArrays.execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1
    _ (withWork state values) arraydef_0__roots (half+offset) 0) by exact rootBound.
  change (exec
    (nttRead arraydef_0__work (Z.of_nat (start+offset+half)) >>= fun value =>
     let right := machineProduct (nth (half+offset) (memory state arraydef_0__roots) 0) value in
     nttWrite arraydef_0__work (Z.of_nat (start+offset))
       (coerceInt (nth (start+offset) values 0+right) 64 mod koxiaModulus) >>= fun _ =>
     nttWrite arraydef_0__work (Z.of_nat (start+offset+half))
       (coerceInt (coerceInt (nth (start+offset) values 0+koxiaModulus) 64-right) 64 mod koxiaModulus) >>= fun _ =>
     Done _ _ _ (butterflyNums nums (nth (start+offset) values 0) right))
    (withWork state values) =
    Some (butterflyNums nums (nth (start+offset) values 0)
      ((nth (half+offset) (memory state arraydef_0__roots) 0 * nth (start+offset+half) values 0) mod koxiaModulus),
      withWork state (butterflyValues values (memory state arraydef_0__roots) start half offset))).
  unfold nttRead. cbn [bind]. rewrite execReadWork by exact workBound.
  unfold machineProduct. rewrite residue_product_coerce by assumption.
  pose proof (residue_bounds (nth (half+offset) (memory state arraydef_0__roots) 0 *
    nth (start+offset+half) values 0)) as rightRange.
  rewrite residue_sum_coerce by assumption.
  rewrite butterfly_difference_coerce by assumption. rewrite modular_difference.
  unfold nttWrite. cbn [bind]. rewrite execStoreWork by lia.
  rewrite execStoreWork by (rewrite length_insert; exact workBound). reflexivity.
Qed.

Definition canonicalValues := Forall (fun value => 0<=value<koxiaModulus).
Lemma canonical_nth values index : canonicalValues values -> (index<length values)%nat ->
  0<=nth index values 0<koxiaModulus.
Proof.
  intros canonical bound. unfold canonicalValues in canonical.
  rewrite (Forall_nth (fun value => 0<=value<koxiaModulus) 0 values) in canonical.
  apply canonical. exact bound.
Qed.
Lemma canonical_insert values index value : canonicalValues values ->
  0<=value<koxiaModulus -> canonicalValues (<[index:=value]>values).
Proof.
  intros canonical range. unfold canonicalValues in *. apply Forall_insert; assumption.
Qed.
Lemma butterflyValues_canonical values roots start half offset : canonicalValues values ->
  canonicalValues (butterflyValues values roots start half offset).
Proof.
  intro canonical. unfold butterflyValues. apply canonical_insert; [|apply residue_bounds].
  apply canonical_insert; [exact canonical|apply residue_bounds].
Qed.
Fixpoint butterflyBlock count values roots start half :=
  match count with
  | O => values
  | S count => butterflyValues (butterflyBlock count values roots start half) roots start half count
  end.
Lemma butterflyBlock_length count values roots start half :
  length (butterflyBlock count values roots start half)=length values.
Proof. induction count as [|count IH]; cbn [butterflyBlock]; rewrite ?butterflyValues_length, ?IH; reflexivity. Qed.
Lemma butterflyBlock_canonical count values roots start half : canonicalValues values ->
  canonicalValues (butterflyBlock count values roots start half).
Proof. intro canonical. induction count as [|count IH]; cbn [butterflyBlock]; [exact canonical|apply butterflyValues_canonical; exact IH]. Qed.

Fixpoint offsetsAction fuel half nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__ntt -> Z) :=
  match fuel with
  | O => Done _ _ _ nums
  | S fuel => butterflyAction nums (half-Z.of_nat fuel-1) >>= fun final => offsetsAction fuel half final
  end.
Lemma nttOffsetsNormalized b nums half fuel continuation :
  eliminateLocalVariables b nums (loop fuel (nttOffsetBody half) >>= continuation) =
  offsetsAction fuel half nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|].
  rewrite loop_S, <- bindAssoc, <- (butterflyNums_self nums) at 1.
  rewrite nttOffsetNormalized. cbn [offsetsAction].
  rewrite <- bindAssoc. unfold butterflyAction, nttRead, nttWrite. cbn [bind].
  f_equal. apply functional_extensionality. intro left.
  f_equal. apply functional_extensionality. intro root.
  f_equal. apply functional_extensionality. intro value.
  f_equal. apply functional_extensionality. intros [].
  f_equal. apply functional_extensionality. intros [].
  cbn [bind]. apply IH.
Qed.

Lemma butterflyValues_unchanged values roots start half offset index :
  (start+offset+half<length values)%nat -> index<>(start+offset)%nat -> index<>(start+offset+half)%nat ->
  nth index (butterflyValues values roots start half offset) 0=nth index values 0.
Proof.
  intros bound notLeft notRight. unfold butterflyValues.
  rewrite !nthUpdateExcept by (try rewrite length_insert; lia). reflexivity.
Qed.
Lemma butterflyBlock_future count values roots start half offset :
  (count<=offset<half)%nat -> (start+half+half<=length values)%nat ->
  nth (start+offset) (butterflyBlock count values roots start half) 0=nth (start+offset) values 0 /\
  nth (start+offset+half) (butterflyBlock count values roots start half) 0=nth (start+offset+half) values 0.
Proof.
  induction count as [|count IH]; [auto|]. intros offsets room. cbn [butterflyBlock].
  rewrite !butterflyValues_unchanged by (try rewrite butterflyBlock_length; lia).
  apply IH; lia.
Qed.

Definition blockValue values roots start half index :=
  let offset := (index-start)%nat in
  if bool_decide ((start<=index<start+half)%nat) then
    (nth index values 0 + (nth (half+offset) roots 0 * nth (index+half) values 0) mod koxiaModulus) mod koxiaModulus
  else if bool_decide ((start+half<=index<start+half+half)%nat) then
    (nth (index-half) values 0 - (nth offset roots 0 * nth index values 0) mod koxiaModulus) mod koxiaModulus
  else nth index values 0.

Definition partialBlockValue count values roots start half index :=
  if bool_decide ((start<=index<start+count)%nat) then blockValue values roots start half index
  else if bool_decide ((start+half<=index<start+half+count)%nat) then blockValue values roots start half index
  else nth index values 0.

Theorem butterflyBlock_lookup count values roots start half index :
  (count<=half)%nat -> (start+half+half<=length values)%nat ->
  nth index (butterflyBlock count values roots start half) 0=
    partialBlockValue count values roots start half index.
Proof.
  induction count as [|count IH].
  - intros bound room. cbn [butterflyBlock]. unfold partialBlockValue.
    rewrite !bool_decide_false by lia. reflexivity.
  - intros bound room. cbn [butterflyBlock].
    pose proof (butterflyBlock_future count values roots start half count ltac:(lia) room) as [futureLeft futureRight].
    destruct (Nat.eq_dec index (start+count)%nat) as [atLeft|notLeft].
    + subst index. unfold butterflyValues.
      rewrite nthUpdateExcept by (rewrite ?length_insert, ?butterflyBlock_length; lia).
      rewrite nthUpdate by (rewrite butterflyBlock_length; lia).
      rewrite futureLeft,futureRight.
      unfold partialBlockValue, blockValue.
      repeat progress (rewrite ?bool_decide_true by lia; rewrite ?bool_decide_false by lia).
      replace (start+count-start)%nat with count by lia. reflexivity.
    + destruct (Nat.eq_dec index (start+count+half)%nat) as [atRight|notRight].
      * subst index. unfold butterflyValues.
        rewrite nthUpdate by (rewrite length_insert, butterflyBlock_length; lia).
        rewrite futureLeft,futureRight.
        unfold partialBlockValue, blockValue.
        repeat progress (rewrite ?bool_decide_true by lia; rewrite ?bool_decide_false by lia).
        replace (start+count+half-half)%nat with (start+count)%nat by lia.
        replace (start+count+half-start)%nat with (half+count)%nat by lia. reflexivity.
      * rewrite butterflyValues_unchanged by (rewrite ?butterflyBlock_length; lia).
        rewrite IH by lia. unfold partialBlockValue.
        assert (leftEq : bool_decide ((start<=index<start+count)%nat)=
          bool_decide ((start<=index<start+S count)%nat)).
        { apply bool_decide_ext. lia. }
        assert (rightEq : bool_decide ((start+half<=index<start+half+count)%nat)=
          bool_decide ((start+half<=index<start+half+S count)%nat)).
        { apply bool_decide_ext. lia. }
        rewrite leftEq,rightEq. reflexivity.
Qed.
Theorem butterflyBlock_complete values roots start half index :
  (start+half+half<=length values)%nat ->
  nth index (butterflyBlock half values roots start half) 0=blockValue values roots start half index.
Proof.
  intro room. rewrite butterflyBlock_lookup by lia. unfold partialBlockValue, blockValue.
  destruct (bool_decide ((start<=index<start+half)%nat)),
    (bool_decide ((start+half<=index<start+half+half)%nat)); reflexivity.
Qed.

Lemma butterflyNums_other nums left right name :
  name<>vardef_0__ntt_left -> name<>vardef_0__ntt_right ->
  butterflyNums nums left right name=nums name.
Proof. intros notLeft notRight. unfold butterflyNums. destruct name; congruence. Qed.

Theorem offsetsAction_execution fuel count state values nums start half :
  (count+fuel=half)%nat -> nums vardef_0__ntt_start=Z.of_nat start -> nums vardef_0__ntt_k=Z.of_nat half ->
  (start+half+half<=length values)%nat ->
  (half+half<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  canonicalValues values -> canonicalValues (memory state arraydef_0__roots) ->
  exists finalNums,
    exec (offsetsAction fuel (Z.of_nat half) nums)
      (withWork state (butterflyBlock count values (memory state arraydef_0__roots) start half)) =
    Some (finalNums, withWork state (butterflyBlock half values (memory state arraydef_0__roots) start half)) /\
    (forall name, name<>vardef_0__ntt_left -> name<>vardef_0__ntt_right -> finalNums name=nums name).
Proof.
  induction fuel as [|fuel IH] in count,nums |- *.
  - intros countFuel startEq halfEq room rootsRoom workFit rootsFit canonical rootCanonical.
    assert (count=half) by lia. subst count. cbn [offsetsAction exec]. eexists.
    split; [reflexivity|]. intros; reflexivity.
  - intros countFuel startEq halfEq room rootsRoom workFit rootsFit canonical rootCanonical.
    cbn [offsetsAction].
    assert (rootIndex : (half+count<length (memory state arraydef_0__roots))%nat) by lia.
    assert (offsetId : Z.of_nat half-Z.of_nat fuel-1=Z.of_nat count) by lia.
    rewrite offsetId, exec_bind.
    rewrite butterflyAction_execution with (start:=start) (half:=half).
    2: exact startEq.
    2: exact halfEq.
    2: rewrite butterflyBlock_length; lia.
    2: exact rootIndex.
    2: rewrite butterflyBlock_length; exact workFit.
    2: exact rootsFit.
    2: apply canonical_nth; [apply butterflyBlock_canonical; exact canonical|rewrite butterflyBlock_length; lia].
    2: apply canonical_nth; [apply butterflyBlock_canonical; exact canonical|rewrite butterflyBlock_length; lia].
    2: apply canonical_nth; [exact rootCanonical|exact rootIndex].
    cbn [optionBind fst snd].
    set (nextNums := butterflyNums nums
      (nth (start+count) (butterflyBlock count values (memory state arraydef_0__roots) start half) 0)
      ((nth (half+count) (memory state arraydef_0__roots) 0 *
        nth (start+count+half) (butterflyBlock count values (memory state arraydef_0__roots) start half) 0) mod koxiaModulus)).
    destruct (IH (S count) nextNums ltac:(lia)
      ltac:(unfold nextNums; cbn [butterflyNums]; exact startEq)
      ltac:(unfold nextNums; cbn [butterflyNums]; exact halfEq)
      room rootsRoom workFit rootsFit canonical rootCanonical)
      as [final [executed others]].
    exists final. split; [exact executed|]. intros name notLeft notRight.
    rewrite others by assumption. apply butterflyNums_other; assumption.
Qed.

Lemma butterflyBlock_outside values roots start half index :
  (start+half+half<=length values)%nat ->
  ((index<start)%nat \/ (start+half+half<=index)%nat) ->
  nth index (butterflyBlock half values roots start half) 0=nth index values 0.
Proof.
  intros room outside. rewrite butterflyBlock_complete by exact room. unfold blockValue.
  rewrite !bool_decide_false by lia. reflexivity.
Qed.
Fixpoint stageWork count values roots half :=
  match count with
  | O => values
  | S count => butterflyBlock half (stageWork count values roots half) roots (count*(half+half))%nat half
  end.
Lemma stageWork_length count values roots half : length (stageWork count values roots half)=length values.
Proof. induction count as [|count IH]; cbn [stageWork]; rewrite ?butterflyBlock_length, ?IH; reflexivity. Qed.
Lemma stageWork_canonical count values roots half : canonicalValues values -> canonicalValues (stageWork count values roots half).
Proof.
  intro canonical. induction count as [|count IH]; cbn [stageWork]; [exact canonical|apply butterflyBlock_canonical; exact IH].
Qed.
Lemma stageWork_future count values roots half index :
  (count*(half+half)<=length values)%nat -> (count*(half+half)<=index)%nat ->
  nth index (stageWork count values roots half) 0=nth index values 0.
Proof.
  induction count as [|count IH]; [reflexivity|]. intros room later. cbn [stageWork].
  rewrite butterflyBlock_outside.
  - apply IH; nia.
  - rewrite stageWork_length. nia.
  - right. nia.
Qed.

Definition partialStageValue count values roots half index :=
  if bool_decide ((index<count*(half+half))%nat) then
    blockValue values roots ((index/(half+half))*(half+half))%nat half index
  else nth index values 0.

Theorem stageWork_lookup count values roots half index : (0<half)%nat ->
  (count*(half+half)<=length values)%nat ->
  nth index (stageWork count values roots half) 0=partialStageValue count values roots half index.
Proof.
  induction count as [|count IH]; intros positive room.
  - cbn [stageWork]. unfold partialStageValue.
    rewrite bool_decide_false by lia. reflexivity.
  - cbn [stageWork].
    destruct (lt_dec index (count*(half+half))) as [earlier|inCurrent].
    + rewrite butterflyBlock_outside.
      * rewrite IH by nia. unfold partialStageValue.
        rewrite !bool_decide_true by nia. reflexivity.
      * rewrite stageWork_length. nia.
      * left. exact earlier.
    + destruct (lt_dec index (S count*(half+half))) as [here|later].
      * rewrite butterflyBlock_complete by (rewrite stageWork_length; nia).
        unfold partialStageValue. rewrite bool_decide_true by exact here.
        assert (blockId : (index/(half+half))%nat=count).
        { symmetry. apply Nat.div_unique with (r:=(index-count*(half+half))%nat); nia. }
        rewrite blockId. unfold blockValue.
        destruct (bool_decide ((count*(half+half)<=index<count*(half+half)+half)%nat)) eqn:left.
        -- apply bool_decide_eq_true in left.
           rewrite !stageWork_future by nia. reflexivity.
        -- apply bool_decide_eq_false in left.
           rewrite bool_decide_true by nia.
           rewrite !stageWork_future by nia. reflexivity.
      * rewrite butterflyBlock_outside.
        -- unfold partialStageValue. rewrite bool_decide_false by lia.
           apply stageWork_future; nia.
        -- rewrite stageWork_length. nia.
        -- right. nia.
Qed.

Definition nttBlockBody (total : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt)
  withLocalVariablesReturnValue LoopOutcome :=
  fun remaining =>
  let block := Done _ _ _ (total-Z.of_nat remaining-1) in
  dropWithinLoop
    (liftToWithinLoop
      (multInt 64 (multInt 64 block (Done _ _ _ 2))
        (numberLocalGet _ _ _ vardef_0__ntt_k) >>= fun start =>
        numberLocalSet _ _ _ vardef_0__ntt_start start) >>= fun _ =>
     liftToWithinLoop
      (numberLocalGet _ _ _ vardef_0__ntt_k >>= fun half =>
        loop (Z.to_nat half) (nttOffsetBody half)) >>= fun _ => Done _ _ _ tt).

Fixpoint blocksAction fuel total nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__ntt -> Z) :=
  match fuel with
  | O => Done _ _ _ nums
  | S fuel =>
    let start := coerceInt (coerceInt ((total-Z.of_nat fuel-1)*2) 64 * nums vardef_0__ntt_k) 64 in
    offsetsAction (Z.to_nat (nums vardef_0__ntt_k)) (nums vardef_0__ntt_k)
      (update nums vardef_0__ntt_start start) >>= fun final => blocksAction fuel total final
  end.

Lemma nttBlockNormalized b nums total remaining continuation :
  eliminateLocalVariables b nums (nttBlockBody total remaining >>= continuation) =
  offsetsAction (Z.to_nat (nums vardef_0__ntt_k)) (nums vardef_0__ntt_k)
    (update nums vardef_0__ntt_start
      (coerceInt (coerceInt ((total-Z.of_nat remaining-1)*2) 64 * nums vardef_0__ntt_k) 64)) >>= fun final =>
  eliminateLocalVariables b final (continuation KeepGoing).
Proof.
  unfold nttBlockBody, multInt, numberLocalGet, numberLocalSet.
  normalize_butterfly.
  rewrite nttOffsetsNormalized. reflexivity.
Qed.

Lemma nttBlocksNormalized b nums total fuel continuation :
  eliminateLocalVariables b nums (loop fuel (nttBlockBody total) >>= continuation) =
  blocksAction fuel total nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|].
  rewrite loop_S, <- bindAssoc, nttBlockNormalized. cbn [blocksAction].
  rewrite <- bindAssoc. apply f_equal. apply functional_extensionality. intro final. apply IH.
Qed.

Theorem blocksAction_execution fuel count total state values nums half :
  (0<half)%nat -> (count+fuel=total)%nat -> nums vardef_0__ntt_k=Z.of_nat half ->
  (total*(half+half)<=length values)%nat ->
  (half+half<=length (memory state arraydef_0__roots))%nat ->
  Z.of_nat (length values)<18446744073709551616 ->
  Z.of_nat (length (memory state arraydef_0__roots))<18446744073709551616 ->
  canonicalValues values -> canonicalValues (memory state arraydef_0__roots) ->
  exists final,
    exec (blocksAction fuel (Z.of_nat total) nums)
      (withWork state (stageWork count values (memory state arraydef_0__roots) half)) =
      Some (final,withWork state (stageWork total values (memory state arraydef_0__roots) half)) /\
    (forall name, name<>vardef_0__ntt_start -> name<>vardef_0__ntt_left ->
      name<>vardef_0__ntt_right -> final name=nums name).
Proof.
  induction fuel as [|fuel IH] in count,nums |- *.
  - intros positive countFuel halfEq room rootRoom workFit rootsFit canonical rootCanonical.
    assert (count=total) by lia. subst count. cbn [blocksAction exec]. eexists.
    split; [reflexivity|]. intros; reflexivity.
  - intros positive countFuel halfEq room rootRoom workFit rootsFit canonical rootCanonical.
    cbn [blocksAction].
    assert (blockId : Z.of_nat total-Z.of_nat fuel-1=Z.of_nat count) by lia.
    rewrite blockId,halfEq.
    assert (twice : coerceInt (Z.of_nat count*2) 64=Z.of_nat (count*2)).
    { rewrite Nat2Z.inj_mul. change (coerceInt (Z.of_nat count*2) 64=Z.of_nat count*2).
      apply coerce64_small. change (0<=Z.of_nat count*2<18446744073709551616). nia. }
    rewrite twice.
    assert (startId : coerceInt (Z.of_nat (count*2)*Z.of_nat half) 64=Z.of_nat (count*(half+half))).
    { replace (Z.of_nat (count*2)*Z.of_nat half) with (Z.of_nat (count*(half+half)))
        by (rewrite !Nat2Z.inj_mul,Nat2Z.inj_add; ring).
      apply coerce64_small. change (0<=Z.of_nat (count*(half+half))<18446744073709551616).
      assert (count*(half+half)<length values)%nat by nia. lia. }
    rewrite startId.
    set (started := update nums vardef_0__ntt_start (Z.of_nat (count*(half+half)))).
    rewrite Nat2Z.id,exec_bind.
    destruct (offsetsAction_execution half 0 state
      (stageWork count values (memory state arraydef_0__roots) half)
      started (count*(half+half)) half ltac:(lia)
      ltac:(unfold started, update; reflexivity)
      ltac:(unfold started, update; exact halfEq)
      ltac:(rewrite stageWork_length; nia) rootRoom
      ltac:(rewrite stageWork_length; exact workFit) rootsFit
      ltac:(apply stageWork_canonical; exact canonical) rootCanonical)
      as [next [executed nextOthers]].
    cbn [butterflyBlock] in executed. rewrite executed. cbn [optionBind fst snd].
    destruct (IH (S count) next positive ltac:(lia)
      ltac:(rewrite nextOthers by congruence; unfold started,update; exact halfEq)
      room rootRoom workFit rootsFit canonical rootCanonical) as [final [finished finalOthers]].
    exists final. split; [exact finished|]. intros name notStart notLeft notRight.
    rewrite finalOthers by assumption. rewrite nextOthers by assumption.
    unfold started,update. destruct (decide (name=vardef_0__ntt_start)); [congruence|reflexivity].
Qed.

Definition nttStageCompact : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt)
  withLocalVariablesReturnValue LoopOutcome :=
  fun _ => dropWithinLoop
    ((liftToWithinLoop
       (numberLocalGet _ _ _ vardef_0__ntt_k >>= fun half =>
        numberLocalGet _ _ _ vardef_0__ntt_size >>= fun size =>
        Done _ _ _ (negb (bool_decide (half<size))))) >>= fun finished =>
       (if finished then break _ _ _ >>= fun _ => Done _ _ _ tt else Done _ _ _ tt) >>= fun _ =>
     liftToWithinLoop
       (divIntUnsigned (numberLocalGet _ _ _ vardef_0__ntt_size)
          (multInt 64 (Done _ _ _ 2) (numberLocalGet _ _ _ vardef_0__ntt_k)) >>= fun blocks =>
        loop (Z.to_nat blocks) (nttBlockBody blocks)) >>= fun _ =>
     liftToWithinLoop
       (multInt 64 (numberLocalGet _ _ _ vardef_0__ntt_k) (Done _ _ _ 2) >>= fun doubled =>
        numberLocalSet _ _ _ vardef_0__ntt_k doubled) >>= fun _ => Done _ _ _ tt).
Lemma nttStageCompact_exact : nttStageBody=nttStageCompact.
Proof. reflexivity. Qed.

Lemma nttStageNormalized b nums remaining continuation :
  coerceInt (2*nums vardef_0__ntt_k) 64<>0 ->
  eliminateLocalVariables b nums (nttStageBody remaining >>= continuation) =
  if bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size) then
    let total := nums vardef_0__ntt_size / coerceInt (2*nums vardef_0__ntt_k) 64 in
    blocksAction (Z.to_nat total) total nums >>= fun final =>
      eliminateLocalVariables b (update final vardef_0__ntt_k (coerceInt (final vardef_0__ntt_k*2) 64))
        (continuation KeepGoing)
  else eliminateLocalVariables b nums (continuation Stop).
Proof.
  intros nonzero. rewrite nttStageCompact_exact.
  unfold nttStageCompact, numberLocalGet, numberLocalSet, multInt, divIntUnsigned.
  normalize_butterfly.
  destruct (bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size)) eqn:continuing.
  - cbn [negb]. normalize_butterfly.
    rewrite nttBlocksNormalized.
    apply f_equal. apply functional_extensionality. intro final. normalize_butterfly. reflexivity.
  - cbn [negb]. normalize_butterfly. reflexivity.
Qed.

Definition nttFail {R : Type} : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R :=
  Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun impossible => False_rect _ impossible).
Lemma nttStageNormalized_exact b nums remaining continuation :
  eliminateLocalVariables b nums (nttStageBody remaining >>= continuation) =
  if bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size) then
    if decide (coerceInt (2*nums vardef_0__ntt_k) 64=0) then nttFail else
    let total := nums vardef_0__ntt_size / coerceInt (2*nums vardef_0__ntt_k) 64 in
    blocksAction (Z.to_nat total) total nums >>= fun final =>
      eliminateLocalVariables b (update final vardef_0__ntt_k (coerceInt (final vardef_0__ntt_k*2) 64))
        (continuation KeepGoing)
  else eliminateLocalVariables b nums (continuation Stop).
Proof.
  destruct (decide (coerceInt (2*nums vardef_0__ntt_k) 64=0)) as [zero|nonzero].
  - rewrite nttStageCompact_exact.
    unfold nttStageCompact,numberLocalGet,numberLocalSet,multInt,divIntUnsigned.
    normalize_butterfly.
    destruct (bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size)) eqn:continuing.
    + cbn [negb]. normalize_butterfly. rewrite decide_True by exact zero.
      unfold trap,nttFail. normalize_butterfly.
      f_equal. apply functional_extensionality. intro impossible. contradiction.
    + cbn [negb]. normalize_butterfly. reflexivity.
  - rewrite nttStageNormalized by exact nonzero.
    destruct (bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size)); reflexivity.
Qed.

Fixpoint stagesAction fuel nums : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__ntt -> Z) :=
  match fuel with
  | O => Done _ _ _ nums
  | S fuel =>
    if bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size) then
      if decide (coerceInt (2*nums vardef_0__ntt_k) 64=0) then nttFail else
      let total := nums vardef_0__ntt_size / coerceInt (2*nums vardef_0__ntt_k) 64 in
      blocksAction (Z.to_nat total) total nums >>= fun final =>
        stagesAction fuel (update final vardef_0__ntt_k (coerceInt (final vardef_0__ntt_k*2) 64))
    else Done _ _ _ nums
  end.

Lemma nttStagesNormalized b nums fuel continuation :
  eliminateLocalVariables b nums (loop fuel nttStageBody >>= continuation) =
  stagesAction fuel nums >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums |- *; [reflexivity|].
  rewrite loop_S, <- bindAssoc, nttStageNormalized_exact. cbn [stagesAction].
  destruct (bool_decide (nums vardef_0__ntt_k<nums vardef_0__ntt_size)).
  - destruct (decide (coerceInt (2*nums vardef_0__ntt_k) 64=0)).
    + unfold nttFail. cbn [bind]. f_equal. apply functional_extensionality. intro impossible. contradiction.
    + rewrite <- bindAssoc. apply f_equal. apply functional_extensionality. intro final. apply IH.
  - reflexivity.
Qed.
