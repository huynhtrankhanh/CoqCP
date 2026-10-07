From CoqCP Require Import Options Imperative Execution SwapUpdate.
From Submission Require Import KoxiaModular KoxiaIntegers KoxiaPower KoxiaRadix KoxiaArrays KoxiaRoots KoxiaFourier.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.

Definition carryNums (nums : varsfuncdef_0__ntt -> Z) j bit :=
  fun name => match name with
  | vardef_0__ntt_j => j
  | vardef_0__ntt_bit => bit
  | _ => nums name
  end.
Definition nttCarryBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt)
  withLocalVariablesReturnValue LoopOutcome :=
(fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub 21%Z (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop (shortCircuitOr ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))))) >>= fun x => if x then (
      (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j) x)) >>=
    fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit) x)) >>=
    fun _ => Done _ _ _ tt
  ))).

Lemma carryNums_j nums old bit j :
  update (carryNums nums old bit) vardef_0__ntt_j j=carryNums nums j bit.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma carryNums_bit nums j old bit :
  update (carryNums nums j old) vardef_0__ntt_bit bit=carryNums nums j bit.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Definition carryStop j bit := bool_decide (bit=0) || bool_decide (j<bit).
Fixpoint machineCarry fuel j bit : Z*Z :=
  match fuel with
  | O => (j,bit)
  | S fuel => if carryStop j bit then (j,bit) else machineCarry fuel (coerceInt (j-bit) 64) (bit/2)
  end.
Create Rewrite HintDb koxia_ntt_steps.
#[local] Hint Rewrite carryNums_j carryNums_bit
  @dropWithinLoopLiftToWithinLoop @dropWithinLoop_break @dropWithinLoop_1 : koxia_ntt_steps.
Ltac normalize_ntt := repeat progress
  (autorewrite with advance_program koxia_ntt_steps; try rewrite <- !bindAssoc;
   try rewrite decide_False by lia; cbn [bind carryNums orb]).

Lemma nttCarryStep b nums j bit index continuation :
  eliminateLocalVariables b (carryNums nums j bit) (nttCarryBody index >>= continuation) =
  if carryStop j bit then eliminateLocalVariables b (carryNums nums j bit) (continuation Stop)
  else eliminateLocalVariables b (carryNums nums (coerceInt (j-bit) 64) (bit/2)) (continuation KeepGoing).
Proof.
  unfold nttCarryBody, numberLocalGet, numberLocalSet, shortCircuitOr, subInt, divIntUnsigned.
  normalize_ntt. unfold carryStop.
  repeat (case_bool_decide; normalize_ntt; try congruence; try lia).
  all: reflexivity.
Qed.
Lemma nttCarryNormalized b nums fuel j bit continuation :
  eliminateLocalVariables b (carryNums nums j bit) (loop fuel nttCarryBody >>= continuation) =
  let '(j,bit) := machineCarry fuel j bit in
  eliminateLocalVariables b (carryNums nums j bit) (continuation tt).
Proof.
  induction fuel as [|fuel IH] in j,bit |- *; [reflexivity|].
  rewrite loop_S, <- bindAssoc, nttCarryStep. cbn [machineCarry].
  destruct (carryStop j bit); cbn [bind]; [reflexivity|]. rewrite IH.
  destruct (machineCarry fuel (coerceInt (j-bit) 64) (bit/2)); reflexivity.
Qed.
Lemma carryStop_model j bit : carryStop j bit = (bit =? 0) || (j <? bit).
Proof.
  unfold carryStop. rewrite bool_decide_eqb. f_equal.
  destruct (bool_decide (j<bit)) eqn:decision.
  - apply bool_decide_eq_true in decision. symmetry. apply Z.ltb_lt. exact decision.
  - apply bool_decide_eq_false in decision. symmetry. apply Z.ltb_ge. lia.
Qed.
Theorem machineCarry_correct fuel j bit : 0 <= j < 18446744073709551616 ->
  0 <= bit < 18446744073709551616 -> machineCarry fuel j bit = carryLoop fuel j bit.
Proof.
  induction fuel as [|fuel IH] in j,bit |- *; [reflexivity|].
  intros hj hb. cbn [machineCarry carryLoop]. rewrite carryStop_model.
  destruct ((bit =? 0) || (j <? bit)) eqn:stop; [reflexivity|].
  apply Bool.orb_false_iff in stop as [nonzero continue]. apply Z.ltb_ge in continue.
  rewrite coerce64_small by (change (0 <= j-bit < 18446744073709551616); lia).
  apply IH.
  - lia.
  - split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_upper_bound bit 2 bit ltac:(lia) ltac:(lia)). lia.
Qed.

Definition nttReverseBody (size : Z) : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt)
  withLocalVariablesReturnValue LoopOutcome :=
(fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub size (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (binder_0 >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b)))) >>= fun x => if x then (
    (liftToWithinLoop ((binder_0 >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_tmp) x)) >>=
    fun _ => (liftToWithinLoop (binder_0 >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) >>= fun x => ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_tmp)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit) x)) >>=
  fun _ => (liftToWithinLoop ((Done _ _ _ 21%Z) >>= fun x => loop (Z.to_nat x) nttCarryBody)) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_bit))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_j) x)) >>=
  fun _ => Done _ _ _ tt
))).

Definition nttSwap (index reversed tmp : Z) : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue Z :=
  if bool_decide (index<reversed) then
    Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue _ (Retrieve _ _ arraydef_0__work index) (fun saved =>
    Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue _ (Retrieve _ _ arraydef_0__work reversed) (fun value =>
    Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue _ (Store _ _ arraydef_0__work index value) (fun _ =>
    Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue _ (Store _ _ arraydef_0__work reversed saved) (fun _ => Done _ _ _ saved))))
  else Done _ _ _ tmp.
Lemma carryNums_tmp nums j bit tmp :
  update (carryNums nums j bit) vardef_0__ntt_tmp tmp =
    carryNums (update nums vardef_0__ntt_tmp tmp) j bit.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma carryNums_overwrite nums j bit oldJ oldBit :
  carryNums (carryNums nums oldJ oldBit) j bit=carryNums nums j bit.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
#[local] Hint Rewrite carryNums_tmp carryNums_overwrite : koxia_ntt_steps.
Lemma ntt_update_tmp_size (nums : varsfuncdef_0__ntt -> Z) tmp : update nums vardef_0__ntt_tmp tmp vardef_0__ntt_size = nums vardef_0__ntt_size.
Proof. reflexivity. Qed.
Lemma ntt_update_tmp_id (nums : varsfuncdef_0__ntt -> Z) : update nums vardef_0__ntt_tmp (nums vardef_0__ntt_tmp)=nums.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
#[local] Hint Rewrite ntt_update_tmp_size ntt_update_tmp_id : koxia_ntt_steps.

Lemma nttReverseStep b nums size j bit remaining continuation :
  nums vardef_0__ntt_size=size ->
  eliminateLocalVariables b (carryNums nums j bit) (nttReverseBody size remaining >>= continuation) =
  nttSwap (size-Z.of_nat remaining-1) j (nums vardef_0__ntt_tmp) >>= fun tmp =>
    let '(j,bit) := machineCarry 21 j (size/2) in
    eliminateLocalVariables b
      (carryNums (update nums vardef_0__ntt_tmp tmp) (coerceInt (j+bit) 64) bit)
      (continuation KeepGoing).
Proof.
  intro sizeEq. unfold nttReverseBody, numberLocalGet, numberLocalSet, retrieve, store,
    divIntUnsigned, addInt. repeat progress (normalize_ntt; try rewrite sizeEq).
  unfold nttSwap. destruct (bool_decide (size-Z.of_nat remaining-1<j)) eqn:swap.
  - repeat progress (normalize_ntt; try rewrite sizeEq; try rewrite swap).
    f_equal. apply functional_extensionality. intro saved.
    repeat progress (normalize_ntt; try rewrite sizeEq). f_equal. apply functional_extensionality. intro value.
    repeat progress (normalize_ntt; try rewrite sizeEq). f_equal. apply functional_extensionality. intros [].
    repeat progress (normalize_ntt; try rewrite sizeEq). f_equal. apply functional_extensionality. intros [].
    repeat progress (normalize_ntt; try rewrite sizeEq). rewrite nttCarryNormalized.
    repeat progress (normalize_ntt; try rewrite sizeEq).
    replace (Z.to_nat 21) with 21%nat by reflexivity.
    destruct (machineCarry 21 j (size/2)) as [nextJ nextBit]. repeat progress (normalize_ntt; try rewrite sizeEq). reflexivity.
  - repeat progress (normalize_ntt; try rewrite sizeEq; try rewrite swap).
    rewrite nttCarryNormalized. replace (Z.to_nat 21) with 21%nat by reflexivity.
    destruct (machineCarry 21 j (size/2)) as [nextJ nextBit].
    repeat progress (normalize_ntt; try rewrite sizeEq). reflexivity.
Qed.

Definition workMemory (state : @Machine arrayIndex1 (arrayType _ environment1)) (values : list Z) : forall name, list (arrayType _ environment1 name) :=
  fun name => match name with
  | arraydef_0__work => values
  | arraydef_0__sequence => memory state arraydef_0__sequence
  | arraydef_0__prefix => memory state arraydef_0__prefix
  | arraydef_0__factorial => memory state arraydef_0__factorial
  | arraydef_0__inverseFactorial => memory state arraydef_0__inverseFactorial
  | arraydef_0__roots => memory state arraydef_0__roots
  | arraydef_0__other => memory state arraydef_0__other
  | arraydef_0__poly => memory state arraydef_0__poly
  | arraydef_0__arena => memory state arraydef_0__arena
  | arraydef_0__frames => memory state arraydef_0__frames
  | arraydef_0__result => memory state arraydef_0__result
  | arraydef_0__printBuffer => memory state arraydef_0__printBuffer
  end.
Definition withWork state values := withMemory state (workMemory state values).
Lemma workMemory_self state : workMemory state (memory state arraydef_0__work)=memory state.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma withWork_self state : withWork state (memory state arraydef_0__work)=state.
Proof. unfold withWork. rewrite workMemory_self. destruct state; reflexivity. Qed.
Lemma withWork_twice state old values : withWork (withWork state old) values=withWork state values.
Proof. reflexivity. Qed.
Lemma modify_workMemory state values index value :
  modifyArray (workMemory state values) arraydef_0__work index value=workMemory state (<[index:=value]>values).
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma execReadWork {R} state values index
  (next : Z -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
  (index<length values)%nat ->
  exec (Dispatch _ _ _ (Retrieve _ _ arraydef_0__work (Z.of_nat index)) next) (withWork state values) =
  exec (next (nth index values 0)) (withWork state values).
Proof.
  intro bound.
  rewrite (@KoxiaArrays.execRetrieve arrayIndex1 (arrayType _ environment1) arrayIndexEqualityDecidable1 R
    (withWork state values) arraydef_0__work index 0 next bound). reflexivity.
Qed.
Lemma execStoreWork {R} state values index value
  (next : unit -> Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
  (index<length values)%nat ->
  exec (Dispatch _ _ _ (Store _ _ arraydef_0__work (Z.of_nat index) value) next) (withWork state values) =
  exec (next tt) (withWork state (<[index:=value]>values)).
Proof.
  intro bound. rewrite execStore by exact bound.
  change (exec (next tt)
    (withMemory (withWork state values) (modifyArray (workMemory state values) arraydef_0__work index value)) =
    exec (next tt) (withWork state (<[index:=value]>values))).
  rewrite modify_workMemory. unfold withWork. rewrite withMemory_twice. reflexivity.
Qed.
Definition swappedWork values left right :=
  <[right:=nth left values 0]>(<[left:=nth right values 0]>values).
Lemma swappedWork_length values left right : length (swappedWork values left right)=length values.
Proof. unfold swappedWork. rewrite !length_insert. reflexivity. Qed.
Theorem nttSwap_execution state values left right tmp :
  (left<length values)%nat -> (right<length values)%nat ->
  exec (nttSwap (Z.of_nat left) (Z.of_nat right) tmp) (withWork state values) =
  if bool_decide ((left<right)%nat) then
    Some (nth left values 0, withWork state (swappedWork values left right))
  else Some (tmp, withWork state values).
Proof.
  intros leftBound rightBound. unfold nttSwap.
  assert (comparison : bool_decide (Z.of_nat left<Z.of_nat right)=bool_decide ((left<right)%nat)).
  { apply bool_decide_ext. symmetry. apply Nat2Z.inj_lt. }
  rewrite comparison. destruct (bool_decide ((left<right)%nat)); [|reflexivity].
  rewrite execReadWork by exact leftBound. rewrite execReadWork by exact rightBound.
  rewrite execStoreWork by exact leftBound. rewrite execStoreWork by (rewrite length_insert; exact rightBound).
  reflexivity.
Qed.

Fixpoint reverseAction fuel size nums j bit : Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__ntt -> Z) :=
  match fuel with
  | O => Done _ _ _ (carryNums nums j bit)
  | S fuel => nttSwap (size-Z.of_nat fuel-1) j (nums vardef_0__ntt_tmp) >>= fun tmp =>
      let '(nextJ,nextBit) := machineCarry 21 j (size/2) in
      reverseAction fuel size (update nums vardef_0__ntt_tmp tmp) (coerceInt (nextJ+nextBit) 64) nextBit
  end.
Lemma nttReverseNormalized b nums size fuel j bit continuation :
  nums vardef_0__ntt_size=size ->
  eliminateLocalVariables b (carryNums nums j bit) (loop fuel (nttReverseBody size) >>= continuation) =
  reverseAction fuel size nums j bit >>= fun final => eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [|fuel IH] in nums,j,bit |- *; [reflexivity|].
  intro sizeEq. rewrite loop_S, <- bindAssoc, nttReverseStep by exact sizeEq.
  cbn [reverseAction]. rewrite <- bindAssoc. unfold nttSwap.
  destruct (bool_decide (size-Z.of_nat fuel-1<j)).
  - cbn [bind]. f_equal. apply functional_extensionality. intro saved.
    f_equal. apply functional_extensionality. intro value.
    f_equal. apply functional_extensionality. intros [].
    f_equal. apply functional_extensionality. intros [].
    destruct (machineCarry 21 j (size/2)) as [nextJ nextBit]. cbn [bind].
    apply IH. rewrite ntt_update_tmp_size. exact sizeEq.
  - cbn [bind]. destruct (machineCarry 21 j (size/2)) as [nextJ nextBit].
    cbn [bind]. apply IH. rewrite ntt_update_tmp_size. exact sizeEq.
Qed.

Theorem generated_reverse_increment stage index : (stage<=20)%nat ->
  0<=index<stageSize stage ->
  let '(nextJ,nextBit) := machineCarry 21 (bitReverse stage index) (stageSize stage/2) in
  coerceInt (nextJ+nextBit) 64=bitReverse stage ((index+1) mod stageSize stage).
Proof.
  intros bound range.
  pose proof (stageSize_positive stage) as hn.
  pose proof (stageSize_bound stage bound) as sizeBound.
  pose proof (bitReverse_bounds stage index range) as reversedRange.
  rewrite machineCarry_correct.
  2: change (0<=bitReverse stage index<18446744073709551616); lia.
  2: { split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_upper_bound (stageSize stage) 2 (stageSize stage) ltac:(lia) ltac:(lia)). lia. }
  pose proof (carryIncrement_correct stage 21 (bitReverse stage index) ltac:(lia) reversedRange) as carry.
  pose proof (incrementReverse_correct stage index range) as next.
  unfold carryIncrement in carry.
  destruct (carryLoop 21 (bitReverse stage index) (stageSize stage/2)) as [nextJ nextBit].
  rewrite carry,next. apply coerce64_small.
  pose proof (Z.mod_pos_bound (index+1) (stageSize stage) hn) as nextRange.
  pose proof (bitReverse_bounds stage _ nextRange). change (0<=bitReverse stage ((index+1) mod stageSize stage)<18446744073709551616). lia.
Qed.

Lemma nth_swappedWork values left right index : (left<length values)%nat -> (right<length values)%nat ->
  nth index (swappedWork values left right) 0 =
    if Nat.eqb index left then nth right values 0
    else if Nat.eqb index right then nth left values 0 else nth index values 0.
Proof.
  intros leftBound rightBound. unfold swappedWork.
  destruct (Nat.eq_dec index left) as [atLeft|notLeft].
  - subst index. rewrite Nat.eqb_refl.
    destruct (Nat.eq_dec left right) as [same|different].
    + subst right. rewrite nthUpdate by (rewrite length_insert; exact leftBound). reflexivity.
    + rewrite nthUpdateExcept by (try rewrite length_insert; lia). rewrite nthUpdate by exact leftBound. reflexivity.
  - rewrite (proj2 (Nat.eqb_neq _ _) notLeft).
    destruct (Nat.eq_dec index right) as [atRight|notRight].
    + subst index. rewrite Nat.eqb_refl, nthUpdate by (rewrite length_insert; exact rightBound). reflexivity.
    + rewrite (proj2 (Nat.eqb_neq _ _) notRight).
      rewrite !nthUpdateExcept by (try rewrite length_insert; lia). reflexivity.
Qed.

Fixpoint reverseWork stage count values : list Z :=
  match count with
  | O => values
  | S count => let current := reverseWork stage count values in
      if bool_decide ((count<Z.to_nat (bitReverse stage (Z.of_nat count)))%nat)
      then swappedWork current count (Z.to_nat (bitReverse stage (Z.of_nat count))) else current
  end.
Lemma reverseWork_length stage count values : length (reverseWork stage count values)=length values.
Proof.
  induction count as [|count IH]; [reflexivity|]. cbn [reverseWork].
  destruct (bool_decide ((count<Z.to_nat (bitReverse stage (Z.of_nat count)))%nat));
    rewrite ?swappedWork_length, IH; reflexivity.
Qed.
Lemma natural_eqb i j : Nat.eqb i j=Z.eqb (Z.of_nat i) (Z.of_nat j).
Proof. apply Bool.eq_true_iff_eq. rewrite Nat.eqb_eq, Z.eqb_eq. lia. Qed.
Lemma natural_ltb i j : bool_decide ((i<j)%nat)=Z.ltb (Z.of_nat i) (Z.of_nat j).
Proof.
  destruct (bool_decide ((i<j)%nat)) eqn:comparison.
  - apply bool_decide_eq_true in comparison. symmetry. apply Z.ltb_lt. lia.
  - apply bool_decide_eq_false in comparison. symmetry. apply Z.ltb_ge. lia.
Qed.
Theorem reverseWork_lookup stage count values index :
  Z.of_nat count<=stageSize stage -> stageSize stage<=Z.of_nat (length values) ->
  0<=index<Z.of_nat (length values) ->
  nth (Z.to_nat index) (reverseWork stage count values) 0 =
    reverseSwaps stage count (fun i => nth (Z.to_nat i) values 0) index.
Proof.
  induction count as [|count IH] in index |- *; [reflexivity|].
  intros countBound room range. cbn [reverseWork reverseSwaps].
  assert (countRange : 0<=Z.of_nat count<stageSize stage) by lia.
  pose proof (bitReverse_bounds stage (Z.of_nat count) countRange) as reversedRange.
  rewrite natural_ltb, Z2Nat.id by lia.
  destruct (Z.of_nat count <? bitReverse stage (Z.of_nat count)) eqn:swapping.
  - rewrite nth_swappedWork by (rewrite reverseWork_length; lia).
    rewrite !natural_eqb, !Z2Nat.id by lia.
    unfold swapValues. destruct (index =? Z.of_nat count) eqn:left;
      [apply Z.eqb_eq in left; subst index|].
    + rewrite IH by lia. reflexivity.
    + destruct (index =? bitReverse stage (Z.of_nat count)) eqn:right;
        [apply Z.eqb_eq in right; subst index|].
      * pose proof (IH (Z.of_nat count) ltac:(lia) room ltac:(lia)) as current.
        rewrite Nat2Z.id in current. exact current.
      * rewrite IH by lia. reflexivity.
  - apply IH; lia.
Qed.
Theorem reverseWork_correct stage values index :
  stageSize stage<=Z.of_nat (length values) -> 0<=index<stageSize stage ->
  nth (Z.to_nat index) (reverseWork stage (sizeNat stage) values) 0 =
    nth (Z.to_nat (bitReverse stage index)) values 0.
Proof.
  intros room range. rewrite reverseWork_lookup by (try rewrite <- stageSize_nat; lia).
  apply reverseSwaps_correct. exact range.
Qed.

Lemma nttSwap_executionZ state values left reversed tmp :
  (left<length values)%nat -> 0<=reversed<Z.of_nat (length values) ->
  exec (nttSwap (Z.of_nat left) reversed tmp) (withWork state values) =
  if bool_decide ((left<Z.to_nat reversed)%nat) then
    Some (nth left values 0, withWork state (swappedWork values left (Z.to_nat reversed)))
  else Some (tmp, withWork state values).
Proof.
  intros leftBound reversedBound.
  replace reversed with (Z.of_nat (Z.to_nat reversed)) at 1 by (rewrite Z2Nat.id by lia; reflexivity).
  apply nttSwap_execution; lia.
Qed.

Theorem reverseAction_execution stage fuel count state values nums bit :
  (stage<=20)%nat -> (count+fuel=sizeNat stage)%nat ->
  stageSize stage<=Z.of_nat (length values) -> nums vardef_0__ntt_size=stageSize stage ->
  exists finalNums,
    exec (reverseAction fuel (stageSize stage) nums
      (bitReverse stage (Z.of_nat count mod stageSize stage)) bit)
      (withWork state (reverseWork stage count values)) =
      Some (finalNums, withWork state (reverseWork stage (sizeNat stage) values)) /\
    finalNums vardef_0__ntt_j=bitReverse stage 0 /\
    finalNums vardef_0__ntt_size=stageSize stage /\
    (forall name, name<>vardef_0__ntt_j -> name<>vardef_0__ntt_bit -> name<>vardef_0__ntt_tmp ->
      finalNums name=nums name).
Proof.
  induction fuel as [|fuel IH] in count,nums,bit |- *.
  - intros bound countFuel room sizeEq.
    assert (whole : count=sizeNat stage) by lia. subst count.
    rewrite <- stageSize_nat, Z.mod_same by (pose proof (stageSize_positive stage); lia).
    cbn [reverseAction exec]. eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [exact sizeEq|].
    intros name notJ notBit notTmp. unfold carryNums. destruct name; congruence.
  - intros bound countFuel room sizeEq.
    pose proof (stageSize_positive stage) as hn.
    assert (countRange : 0<=Z.of_nat count<stageSize stage).
    { rewrite stageSize_nat. lia. }
    pose proof (bitReverse_bounds stage (Z.of_nat count) countRange) as reversedRange.
    rewrite Z.mod_small by exact countRange. cbn [reverseAction].
    assert (indexEq : stageSize stage-Z.of_nat fuel-1=Z.of_nat count).
    { rewrite stageSize_nat. lia. }
    rewrite indexEq, exec_bind.
    rewrite nttSwap_executionZ by (rewrite reverseWork_length; lia).
    pose proof (generated_reverse_increment stage (Z.of_nat count) bound countRange) as increment.
    destruct (machineCarry 21 (bitReverse stage (Z.of_nat count)) (stageSize stage/2)) as [nextJ nextBit].
    rewrite increment. replace (Z.of_nat count+1) with (Z.of_nat (S count)) by lia.
    destruct (bool_decide ((count<Z.to_nat (bitReverse stage (Z.of_nat count)))%nat)) eqn:swap.
    + cbn [optionBind fst snd].
      destruct (IH (S count) (update nums vardef_0__ntt_tmp (nth count (reverseWork stage count values) 0))
        nextBit bound ltac:(lia) room ltac:(rewrite ntt_update_tmp_size; exact sizeEq)) as [final [execution [finished [sizeFinal others]]]].
      cbn [reverseWork] in execution. rewrite swap in execution.
      exists final. split; [exact execution|]. split; [exact finished|]. split; [exact sizeFinal|].
      intros name notJ notBit notTmp. rewrite others by assumption.
      unfold update. destruct (decide (name=vardef_0__ntt_tmp)); [congruence|reflexivity].
    + cbn [optionBind fst snd].
      destruct (IH (S count) (update nums vardef_0__ntt_tmp (nums vardef_0__ntt_tmp)) nextBit
        bound ltac:(lia) room ltac:(rewrite ntt_update_tmp_size; exact sizeEq)) as [final [execution [finished [sizeFinal others]]]].
      cbn [reverseWork] in execution. rewrite swap in execution.
      exists final. split; [exact execution|]. split; [exact finished|]. split; [exact sizeFinal|].
      intros name notJ notBit notTmp. rewrite others by assumption.
      unfold update. destruct (decide (name=vardef_0__ntt_tmp)); [congruence|reflexivity].
Qed.

Definition nttStageBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt)
  withLocalVariablesReturnValue LoopOutcome :=
(fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub 20%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) >>= fun b => Done _ _ _ (bool_decide (Z.lt a b))) >>= fun x => Done _ _ _ (negb x))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_size)) (multInt 64 (Done _ _ _ 2%Z) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)))) >>= fun x => loop (Z.to_nat x) (fun binder_1_intermediate => let binder_1 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_1_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop ((multInt 64 (multInt 64 binder_1 (Done _ _ _ 2%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) >>= fun x => loop (Z.to_nat x) (fun binder_2_intermediate => let binder_2 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt) withLocalVariablesReturnValue _ (Z.sub (Z.sub x (Z.of_nat binder_2_intermediate)) 1%Z) in dropWithinLoop ((
      (liftToWithinLoop (((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left) x)) >>=
      fun _ => (liftToWithinLoop ((modIntUnsigned (multInt 64 ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) binder_2) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__roots) x) ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => retrieve arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x)) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right) x)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) >>= fun x => ((modIntUnsigned (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
      fun _ => (liftToWithinLoop ((addInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_start)) binder_2) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k))) >>= fun x => ((modIntUnsigned (subInt 64 (addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_left)) (Done _ _ _ 998244353%Z)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_right))) (Done _ _ _ 998244353%Z)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (arraydef_0__work) x y)) >>=
      fun _ => Done _ _ _ tt
    ))))) >>=
    fun _ => Done _ _ _ tt
  ))))) >>=
  fun _ => (liftToWithinLoop ((multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__ntt (vardef_0__ntt_k) x)) >>=
  fun _ => Done _ _ _ tt
))).

Lemma carryNums_self nums : carryNums nums (nums vardef_0__ntt_j) (nums vardef_0__ntt_bit)=nums.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma generated_ntt_reverse_normalized b nums :
  funcdef_0__ntt b nums =
    reverseAction (Z.to_nat (nums vardef_0__ntt_size)) (nums vardef_0__ntt_size) nums
      (nums vardef_0__ntt_j) (nums vardef_0__ntt_bit) >>= fun final =>
      eliminateLocalVariables b final
        (numberLocalSet _ _ _ vardef_0__ntt_k 1 >>= fun _ =>
          loop 20 nttStageBody >>= fun _ => Done _ _ _ tt).
Proof.
  unfold funcdef_0__ntt, funcdef_0__ntt_body.
  change (eliminateLocalVariables b nums
    (numberLocalGet _ _ _ vardef_0__ntt_size >>= fun size =>
       loop (Z.to_nat size) (nttReverseBody size) >>= fun _ =>
       numberLocalSet _ _ _ vardef_0__ntt_k 1 >>= fun _ =>
       loop 20 nttStageBody >>= fun _ => Done _ _ _ tt) =
    reverseAction (Z.to_nat (nums vardef_0__ntt_size)) (nums vardef_0__ntt_size) nums
      (nums vardef_0__ntt_j) (nums vardef_0__ntt_bit) >>= fun final =>
      eliminateLocalVariables b final
        (numberLocalSet _ _ _ vardef_0__ntt_k 1 >>= fun _ =>
          loop 20 nttStageBody >>= fun _ => Done _ _ _ tt)).
  unfold numberLocalGet at 1. cbn [bind]. rewrite pushNumberGet.
  rewrite <- (carryNums_self nums) at 1.
  rewrite nttReverseNormalized by reflexivity. reflexivity.
Qed.
