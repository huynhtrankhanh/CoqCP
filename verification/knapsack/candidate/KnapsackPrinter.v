From CoqCP Require Import Options Imperative Execution DecimalDigits.
From CoqCP Require Import DecimalEncoding Optimality ArrayExecution.
From Submission Require Import KnapsackCode KnapsackTable KnapsackExecution KnapsackIO KnapsackMain.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.

Definition printerNums value count character : varsfuncdef_0_PrintInt64_unsigned -> Z :=
  fun name => match name with
  | vardef_0_PrintInt64_unsigned_num => value
  | vardef_0_PrintInt64_unsigned_i => count
  | vardef_0_PrintInt64_unsigned_tmpChar => character
  end.
Definition printerCollectBody  : nat -> Action
  (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned)
  withLocalVariablesReturnValue LoopOutcome := (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue _ (Z.sub (Z.sub 20%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    ((liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
      (break arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) >>=
      fun _ => Done _ _ _ tt
    ) else (
      Done _ _ _ tt
    )) >>=
    fun _ => (liftToWithinLoop (((addInt 64 (modIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) (Done _ _ _ 10%Z)) (Done _ _ _ 48%Z)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_tmpChar) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) >>= fun x => ((numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_tmpChar)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (arraydef_0_PrintInt64_buffer) x y)) >>=
    fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num)) (Done _ _ _ 10%Z)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_num) x)) >>=
    fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i) x)) >>=
    fun _ => Done _ _ _ tt
  ))).
Definition printerOutputBody (count : Z) : nat -> Action
  (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned)
  withLocalVariablesReturnValue LoopOutcome := (fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned) withLocalVariablesReturnValue _ (Z.sub (Z.sub count (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
    (liftToWithinLoop (((subInt 64 (subInt 64 (numberLocalGet arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (vardef_0_PrintInt64_unsigned_i)) binder_0) (Done _ _ _ 1%Z)) >>= fun x => retrieve arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned (arraydef_0_PrintInt64_buffer) x) >>= fun x => writeChar arrayIndex0 (arrayType _ environment0) varsfuncdef_0_PrintInt64_unsigned x)) >>=
    fun _ => Done _ _ _ tt
  ))).
Definition printerDigit value := coerceInt (coerceInt ((value mod 10 + 48)%Z) 64) 8.
Definition outputChar {I T} value :=
  Dispatch (WithArrays I T) withArraysReturnValue unit (DoBasicEffect _ _ (WriteChar value)) (fun _ => Done _ _ _ tt).
Fixpoint collectDigits fuel value count character : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue (varsfuncdef_0_PrintInt64_unsigned -> Z) :=
  match fuel with
  | O => Done _ _ _ (printerNums value count character)
  | S fuel => if bool_decide (value = 0) then Done _ _ _ (printerNums value count character)
      else Dispatch _ _ _ (Store _ _ arraydef_0_PrintInt64_buffer count (printerDigit value)) (fun _ =>
        collectDigits fuel ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value))
  end.
Definition outputIndex count remaining :=
  coerceInt (coerceInt (count - (count - Z.of_nat remaining - 1)) 64 - 1) 64.
Definition outputDigits count : Action (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue unit :=
  arrayLoop (Z.to_nat count) (fun remaining =>
    Dispatch _ _ _ (Retrieve _ _ arraydef_0_PrintInt64_buffer (outputIndex count remaining))
      (fun digit => outputChar digit)).

Lemma printerNums_character value count old character :
  update (printerNums value count old) vardef_0_PrintInt64_unsigned_tmpChar character = printerNums value count character.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma printerNums_value old count character value :
  update (printerNums old count character) vardef_0_PrintInt64_unsigned_num value = printerNums value count character.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma printerNums_count value old character count :
  update (printerNums value old character) vardef_0_PrintInt64_unsigned_i count = printerNums value count character.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Create Rewrite HintDb printer_steps.
#[local] Hint Rewrite printerNums_character printerNums_value printerNums_count
  @dropWithinLoopLiftToWithinLoop @dropWithinLoop_break @dropWithinLoop_1 : printer_steps.
Ltac normalize_printer := repeat progress (autorewrite with advance_program printer_steps; try rewrite <- !bindAssoc; cbn [bind printerNums]).

Lemma printerCollectStep b value count character index continuation :
  eliminateLocalVariables b (printerNums value count character) (printerCollectBody index >>= continuation) =
  if bool_decide (value = 0) then eliminateLocalVariables b (printerNums value count character) (continuation Stop)
  else Dispatch _ _ _ (Store _ _ arraydef_0_PrintInt64_buffer count (printerDigit value)) (fun _ =>
    eliminateLocalVariables b (printerNums ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value)) (continuation KeepGoing)).
Proof.
  unfold printerCollectBody, numberLocalGet, numberLocalSet, store, addInt, subInt, modIntUnsigned, divIntUnsigned.
  autorewrite with printer_steps. rewrite <- !bindAssoc.
  normalize_printer.
  match goal with |- context [if ?test then _ else _] =>
    assert (testEq : test = bool_decide (value = 0)) by reflexivity; rewrite testEq
  end.
  destruct (bool_decide (value = 0)) eqn:hZero; cbn [bind].
  - normalize_printer. try rewrite hZero. normalize_printer. reflexivity.
  - normalize_printer. try rewrite hZero. normalize_printer.
    destruct (decide (10 = 0)%Z) as [zeroDivisor | nonzeroDivisor]; [lia |]. normalize_printer. fold printerDigit.
    reflexivity.
Qed.

Lemma printerCollectLoop b fuel value count character continuation :
  eliminateLocalVariables b (printerNums value count character) (loop fuel printerCollectBody >>= continuation) =
  collectDigits fuel value count character >>= fun nums => eliminateLocalVariables b nums (continuation tt).
Proof.
  induction fuel as [| fuel IH] in value, count, character |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, printerCollectStep.
  cbn [collectDigits]. destruct (bool_decide (value = 0)); cbn [bind]; [reflexivity |].
  f_equal. apply functional_extensionality. intros []. apply IH.
Qed.

Lemma printerOutputNormalized b value count character :
  eliminateLocalVariables b (printerNums value count character)
    (loop (Z.to_nat count) (printerOutputBody count) >>= fun _ => Done _ _ _ tt) = outputDigits count.
Proof.
  unfold outputDigits.
  transitivity (arrayLoop (Z.to_nat count) (fun remaining =>
    Dispatch (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue unit (Retrieve _ _ arraydef_0_PrintInt64_buffer (outputIndex count remaining)) (fun digit => outputChar digit)) >>= fun _ => Done _ _ _ tt).
  - eapply (eliminate_arrayLoop b (printerNums value count character) _ _ _ _ (fun _ => Done _ _ _ tt)).
  - apply bind_unit_identity.
  Unshelve.
  intros index continuation. cbn beta. unfold printerOutputBody, subInt, numberLocalGet, retrieve, writeChar.
  normalize_printer.
  unfold outputIndex, outputChar. cbn [bind].
  reflexivity.
Qed.

Lemma printerCollectLoopFor b body
  (step : forall value count character index continuation,
    eliminateLocalVariables b (printerNums value count character) (body index >>= continuation) =
    if bool_decide (value = 0) then eliminateLocalVariables b (printerNums value count character) (continuation Stop)
    else Dispatch _ _ _ (Store _ _ arraydef_0_PrintInt64_buffer count (printerDigit value)) (fun _ =>
      eliminateLocalVariables b (printerNums ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value)) (continuation KeepGoing)))
  fuel value count character continuation :
  eliminateLocalVariables b (printerNums value count character) (loop fuel body >>= continuation) =
  collectDigits fuel value count character >>= fun nums => eliminateLocalVariables b nums (continuation tt).
Proof.
  induction fuel as [| fuel IH] in value, count, character |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, step.
  cbn [collectDigits]. destruct (bool_decide (value = 0)); cbn [bind]; [reflexivity |].
  f_equal. apply functional_extensionality. intros []. apply IH.
Qed.

Definition printerAction value :=
  if bool_decide (value = 0) then outputChar 48
  else collectDigits 20 value 0 0 >>= fun nums => outputDigits (nums vardef_0_PrintInt64_unsigned_i).

Lemma printerNormalized value :
  funcdef_0_PrintInt64_unsigned (fun _ => false)
    (update (fun _ => 0) vardef_0_PrintInt64_unsigned_num value) = printerAction value.
Proof.
  unfold funcdef_0_PrintInt64_unsigned.
  replace (update (fun _ : varsfuncdef_0_PrintInt64_unsigned => 0) vardef_0_PrintInt64_unsigned_num value) with (printerNums value 0 0).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  unfold funcdef_0_PrintInt64_unsigned_body. rewrite <- !bindAssoc.
  unfold numberLocalGet, numberLocalSet, writeChar. normalize_printer.
  unfold printerAction.
  match goal with |- context [if ?test then _ else _] =>
    assert (testEq : test = bool_decide (value = 0)) by reflexivity; rewrite testEq
  end.
  destruct (bool_decide (value = 0)) eqn:hZero; normalize_printer.
  - try rewrite hZero. normalize_printer. reflexivity.
  - try rewrite hZero. normalize_printer. fold printerCollectBody.
    match goal with |- eliminateLocalVariables ?b ?nums (loop ?fuel ?body >>= ?cont) = _ =>
      assert (collectStep : forall value' count character index continuation,
        eliminateLocalVariables b (printerNums value' count character) (body index >>= continuation) =
        if bool_decide (value' = 0) then eliminateLocalVariables b (printerNums value' count character) (continuation Stop)
        else Dispatch _ _ _ (Store _ _ arraydef_0_PrintInt64_buffer count (printerDigit value')) (fun _ =>
          eliminateLocalVariables b (printerNums (value' / 10) (coerceInt (count + 1) 64) (printerDigit value')) (continuation KeepGoing)))
    end.
    { intros value' count character index continuation. cbn beta.
      unfold numberLocalGet, numberLocalSet, store, addInt, subInt, modIntUnsigned, divIntUnsigned.
      normalize_printer.
      match goal with |- context [if ?test then _ else _] =>
        assert (testEq' : test = bool_decide (value' = 0)) by reflexivity; rewrite testEq'
      end.
      destruct (bool_decide (value' = 0)) eqn:hZero'; cbn [bind].
      - normalize_printer. try rewrite hZero'. normalize_printer. reflexivity.
      - normalize_printer. try rewrite hZero'. normalize_printer.
        destruct (decide (10 = 0)%Z) as [zeroDivisor | nonzeroDivisor]; [lia |]. normalize_printer. fold printerDigit.
        reflexivity. }
    rewrite (printerCollectLoopFor _ _ collectStep).
    f_equal. apply functional_extensionality. intro nums.
    normalize_printer.
    unfold outputDigits.
    transitivity (arrayLoop (Z.to_nat (nums vardef_0_PrintInt64_unsigned_i)) (fun remaining =>
      Dispatch (WithArrays arrayIndex0 (arrayType _ environment0)) withArraysReturnValue unit
        (Retrieve _ _ arraydef_0_PrintInt64_buffer (outputIndex (nums vardef_0_PrintInt64_unsigned_i) remaining))
        (fun digit => outputChar digit)) >>= fun _ => Done _ _ _ tt).
    + eapply (eliminate_arrayLoop (fun _ => false) nums _ _ _ _ (fun _ => Done _ _ _ tt)).
    + apply bind_unit_identity.
    Unshelve.
    intros index continuation. cbn beta.
    unfold subInt, numberLocalGet, retrieve, writeChar. normalize_printer.
    unfold outputIndex, outputChar. cbn [bind]. reflexivity.
Qed.

Definition printerMapping name := match name with arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end.
Definition printerCongruent name : arrayType _ environment0 name = arrayType _ environment2 (printerMapping name) :=
  match name with arraydef_0_PrintInt64_buffer => eq_refl end.
Fixpoint mappedCollectDigits fuel value count character : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue (varsfuncdef_0_PrintInt64_unsigned -> Z) :=
  match fuel with
  | O => Done _ _ _ (printerNums value count character)
  | S fuel => if bool_decide (value = 0) then Done _ _ _ (printerNums value count character)
      else Dispatch _ _ _ (Store _ _ arraydef_0__printBuffer count (printerDigit value)) (fun _ =>
        mappedCollectDigits fuel ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value))
  end.
Definition mappedOutputDigits count : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit :=
  arrayLoop (Z.to_nat count) (fun remaining =>
    Dispatch _ _ _ (Retrieve _ _ arraydef_0__printBuffer (outputIndex count remaining)) (fun digit => outputChar digit)).

Lemma translate_collectDigits fuel value count character :
  translateArrays (collectDigits fuel value count character) (arrayType _ environment2) printerMapping printerCongruent =
  mappedCollectDigits fuel value count character.
Proof.
  induction fuel as [| fuel IH] in value, count, character |- *; [reflexivity |].
  cbn [collectDigits mappedCollectDigits]. destruct (bool_decide (value = 0)); [reflexivity |].
  change (Dispatch (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue (varsfuncdef_0_PrintInt64_unsigned -> Z)
    (Store _ _ arraydef_0__printBuffer count (printerDigit value))
    (fun _ => translateArrays (collectDigits fuel ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value)) (arrayType _ environment2) printerMapping printerCongruent) =
    Dispatch _ _ _ (Store _ _ arraydef_0__printBuffer count (printerDigit value))
      (fun _ => mappedCollectDigits fuel ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value))).
  f_equal. apply functional_extensionality. intros []. apply IH.
Qed.
Lemma translate_outputDigits count :
  translateArrays (outputDigits count) (arrayType _ environment2) printerMapping printerCongruent = mappedOutputDigits count.
Proof.
  unfold outputDigits, mappedOutputDigits. rewrite translate_arrayLoop.
  reflexivity.
Qed.
Lemma mappedPrinterNormalized value : mappedPrinter value =
  if bool_decide (value = 0) then outputChar 48
  else mappedCollectDigits 20 value 0 0 >>= fun nums => mappedOutputDigits (nums vardef_0_PrintInt64_unsigned_i).
Proof.
  unfold mappedPrinter. fold printerMapping printerCongruent.
  rewrite printerNormalized. unfold printerAction. destruct (bool_decide (value = 0)); [reflexivity |].
  rewrite translateArrays_bind, translate_collectDigits.
  f_equal. apply functional_extensionality. intro nums. apply translate_outputDigits.
Qed.

Definition printerMemory (s : @Machine arrayIndex2 (arrayType _ environment2)) buffer : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__printBuffer => buffer
  | arraydef_0__dp => memory s arraydef_0__dp
  | arraydef_0__weights => memory s arraydef_0__weights
  | arraydef_0__values => memory s arraydef_0__values
  | arraydef_0__message => memory s arraydef_0__message
  | arraydef_0__n => memory s arraydef_0__n
  | arraydef_0__input => memory s arraydef_0__input
  end.
Definition setBuffer s buffer := withMemory s (printerMemory s buffer).
Lemma setBuffer_twice s previous buffer : setBuffer (setBuffer s previous) buffer = setBuffer s buffer.
Proof. reflexivity. Qed.
Lemma modify_printerMemory s buffer index value :
  modifyArray (printerMemory s buffer) arraydef_0__printBuffer index value = printerMemory s (<[index := value]> buffer).
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma execStoreBuffer {R} s buffer index value
  (next : unit -> Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue R)
  (h : (index < length buffer)%nat) :
  exec (Dispatch _ _ _ (Store _ _ arraydef_0__printBuffer (Z.of_nat index) value) next) (setBuffer s buffer) =
  exec (next tt) (setBuffer s (<[index := value]> buffer)).
Proof.
  cbn [exec step optionBind setBuffer withMemory printerMemory memory]. rewrite Nat2Z.id.
  destruct (decide (Nat.lt index (length buffer))) as [bound | bad]; [| lia].
  cbn [optionBind fst snd]. rewrite modify_printerMemory. reflexivity.
Qed.
Lemma printerDigit_exact value : printerDigit value = (value mod 10 + 48)%Z.
Proof.
  unfold printerDigit, coerceInt. pose proof Z.mod_pos_bound value 10 ltac:(lia) as bound.
  assert (power : (58 < 2^64)%Z) by (vm_compute; reflexivity).
  rewrite (Z.mod_small ((value mod 10 + 48)%Z) (2^64)) by lia.
  assert (power8 : (58 < 2^8)%Z) by (vm_compute; reflexivity).
  rewrite Z.mod_small; lia.
Qed.
Lemma coerce_count count (h : (count <= 20)%nat) : coerceInt (Z.of_nat count + 1) 64 = Z.of_nat (S count).
Proof.
  unfold coerceInt. assert (power : (21 < 2^64)%Z) by (vm_compute; reflexivity).
  rewrite Z.mod_small; lia.
Qed.
Fixpoint collectResult fuel value count character : varsfuncdef_0_PrintInt64_unsigned -> Z :=
  match fuel with
  | O => printerNums value count character
  | S fuel => if bool_decide (value = 0) then printerNums value count character
      else collectResult fuel ((value / 10)%Z) (coerceInt (count + 1) 64) (printerDigit value)
  end.
Lemma collectResult_count fuel value character count (h : (count + fuel <= 20)%nat) :
  collectResult fuel value (Z.of_nat count) character vardef_0_PrintInt64_unsigned_i =
  Z.of_nat (count + length (littleDigits fuel value)).
Proof.
  induction fuel as [| fuel IH] in value, character, count, h |- *; [cbn [collectResult printerNums littleDigits length]; lia |].
  cbn [collectResult littleDigits]. destruct (decide (value = 0)) as [zero | nonzero].
  - subst value. rewrite bool_decide_true; [cbn [printerNums length]; lia | reflexivity].
  - rewrite bool_decide_false; [| exact nonzero]. rewrite coerce_count; [| lia].
    rewrite IH; [| lia]. cbn [length]. f_equal. lia.
Qed.

Lemma collectExecution fuel value character prefix s (h : (length prefix + fuel <= 20)%nat) :
  exec (mappedCollectDigits fuel value (Z.of_nat (length prefix)) character)
    (setBuffer s (prefix ++ repeat 0%Z (20 - length prefix))) =
  Some (collectResult fuel value (Z.of_nat (length prefix)) character,
    setBuffer s ((prefix ++ littleDigits fuel value) ++ repeat 0%Z (20 - length prefix - length (littleDigits fuel value)))).
Proof.
  induction fuel as [| fuel IH] in value, character, prefix, h |- *.
  - cbn [mappedCollectDigits collectResult littleDigits exec length]. rewrite app_nil_r, Nat.sub_0_r. reflexivity.
  - cbn [mappedCollectDigits collectResult littleDigits]. destruct (decide (value = 0)) as [zero | nonzero].
    + subst value. rewrite bool_decide_true; [| reflexivity]. cbn [exec length]. rewrite app_nil_r, Nat.sub_0_r. reflexivity.
    + rewrite bool_decide_false; [| exact nonzero].
      rewrite execStoreBuffer; [| rewrite length_app, repeat_length; change (length prefix < length prefix + (20 - length prefix))%nat; lia].
      rewrite coerce_count; [| lia].
      replace (20 - length prefix)%nat with (S (20 - S (length prefix))) by lia.
      rewrite insert_at_prefix.
      replace (S (length prefix)) with (length (prefix ++ [printerDigit value])) by (rewrite length_app; cbn [length]; lia).
      rewrite IH; [| rewrite length_app; cbn [length]; lia].
      rewrite printerDigit_exact. f_equal. f_equal. f_equal.
      replace (S (20 - length (prefix ++ [(value mod 10 + 48)%Z])) - length ((value mod 10 + 48)%Z :: littleDigits fuel ((value / 10)%Z)))%nat
        with (20 - length (prefix ++ [(value mod 10 + 48)%Z]) - length (littleDigits fuel ((value / 10)%Z)))%nat
        by (rewrite length_app; cbn [length]; pose proof (littleDigits_length fuel ((value / 10)%Z)); lia).
      rewrite <- (app_assoc prefix [(value mod 10 + 48)%Z] (littleDigits fuel ((value / 10)%Z))). reflexivity.
Qed.

Lemma outputIndex_exact count remaining (h : (remaining < count <= 20)%nat) :
  outputIndex (Z.of_nat count) remaining = Z.of_nat remaining.
Proof.
  unfold outputIndex. replace (Z.of_nat count - (Z.of_nat count - Z.of_nat remaining - 1)) with (Z.of_nat (remaining + 1)) by lia.
  rewrite coerce_nat64; [| assert (20 < 2^64)%nat by (apply Nat2Z.inj_lt; rewrite Nat2Z.inj_pow; vm_compute; reflexivity); lia].
  replace (Z.of_nat (remaining + 1) - 1) with (Z.of_nat remaining) by lia.
  rewrite coerce_nat64; [reflexivity | assert (20 < 2^64)%nat by (apply Nat2Z.inj_lt; rewrite Nat2Z.inj_pow; vm_compute; reflexivity); lia].
Qed.
Definition outputBufferLoop count : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit :=
  arrayLoop count (fun remaining => readArray arraydef_0__printBuffer (Z.of_nat remaining) >>= outputChar).
Lemma outputLoopNormalized count (h : (count <= 20)%nat) : mappedOutputDigits (Z.of_nat count) = outputBufferLoop count.
Proof.
  unfold mappedOutputDigits, outputBufferLoop. rewrite Nat2Z.id. apply arrayLoop_ext. intros index bound.
  rewrite outputIndex_exact; [reflexivity | lia].
Qed.
Lemma outputBufferExecution count s (h : (count <= length (memory s arraydef_0__printBuffer))%nat) :
  exec (outputBufferLoop count) s = Some (tt, withOutput s (stdout s ++ reverse (take count (memory s arraydef_0__printBuffer)))).
Proof.
  induction count as [| count IH] in s, h |- *.
  - cbn [outputBufferLoop arrayLoop exec take reverse]. rewrite app_nil_r. destruct s; reflexivity.
  - unfold outputBufferLoop. cbn [arrayLoop]. rewrite exec_bind, (execRead arraydef_0__printBuffer count 0%Z); [| lia].
    change (exec (outputBufferLoop count) (withOutput s (stdout s ++ [nth count (memory s arraydef_0__printBuffer) 0%Z])) =
      Some (tt, withOutput s (stdout s ++ reverse (take (S count) (memory s arraydef_0__printBuffer))))).
 rewrite IH; [| exact (Nat.le_trans _ _ _ (Nat.le_succ_diag_r count) h)].
    cbn [stdout withOutput memory].
    assert (lookup : memory s arraydef_0__printBuffer !! count = Some (nth count (memory s arraydef_0__printBuffer) 0%Z)).
    { destruct (nth_lookup_or_length (memory s arraydef_0__printBuffer) count 0%Z); [assumption | lia]. }
    rewrite (take_S_r _ _ _ lookup), reverse_app. cbn [reverse]. rewrite app_assoc. reflexivity.
Qed.

Lemma printerExecution value s (h : (value < 2^64)%nat) :
  exists buffer, exec (mappedPrinter (Z.of_nat value)) (setBuffer s (repeat 0%Z 20)) =
    Some (tt, withOutput (setBuffer s buffer) (stdout s ++ decimalBytes value)).
Proof.
  rewrite mappedPrinterNormalized. destruct (decide (value = 0)%nat) as [zero | nonzero].
  - subst value. rewrite bool_decide_true; [| reflexivity]. exists (repeat 0%Z 20). reflexivity.
  - rewrite bool_decide_false; [| lia]. rewrite exec_bind.
    pose proof (collectExecution 20 (Z.of_nat value) 0 [] s ltac:(reflexivity)) as collected.
    cbn [length app Nat.sub Z.of_nat] in collected.
    match goal with |- context[exec ?code ?state] =>
      assert (collectedNative : exec code state = Some (collectResult 20 (Z.of_nat value) 0 0,
        setBuffer s (littleDigits 20 (Z.of_nat value) ++ repeat 0%Z (20 - length (littleDigits 20 (Z.of_nat value)))))) by exact collected
    end. rewrite collectedNative. cbn [optionBind fst snd app length Nat.sub].
    assert (countResult : collectResult 20 (Z.of_nat value) 0 0 vardef_0_PrintInt64_unsigned_i = Z.of_nat (length (littleDigits 20 (Z.of_nat value))))
      by exact (collectResult_count 20 (Z.of_nat value) 0 0 ltac:(reflexivity)).
    rewrite countResult. rewrite outputLoopNormalized; [| apply littleDigits_length].
    rewrite outputBufferExecution.
    + cbn [memory setBuffer withMemory printerMemory stdout].
      rewrite take_app_length'; [| reflexivity].
      exists (littleDigits 20 (Z.of_nat value) ++ repeat 0%Z (20 - length (littleDigits 20 (Z.of_nat value)))).
      unfold decimalBytes. destruct (decide (value = 0)%nat); [contradiction |]. reflexivity.
    + cbn [memory setBuffer withMemory printerMemory]. rewrite length_app, repeat_length.
      change (length (littleDigits 20 (Z.of_nat value)) <= length (littleDigits 20 (Z.of_nat value)) + (20 - length (littleDigits 20 (Z.of_nat value))))%nat. lia.
Qed.
