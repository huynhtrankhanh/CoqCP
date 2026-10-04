From CoqCP Require Import Options Imperative Execution KnapsackCode KnapsackTable KnapsackExecution KnapsackIO DecimalDigits.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.
Create Rewrite HintDb main_maps.
#[local] Hint Rewrite @dropWithinLoopLiftToWithinLoop @dropWithinLoop_1 @eliminateLift : main_maps.
#[local] Hint Rewrite @lookupSame @lookupDifferent using discriminate : main_maps.

Definition loadAction count :=
  arrayLoop (Z.to_nat count) (fun remaining =>
    mappedReader >>= fun _ =>
    readArray arraydef_0__input 0 >>= fun weight =>
    writeArray arraydef_0__weights (count - Z.of_nat remaining - 1) (coerceInt weight 32) >>= fun _ =>
    mappedReader >>= fun _ =>
    readArray arraydef_0__input 0 >>= fun value =>
    writeArray arraydef_0__values (count - Z.of_nat remaining - 1) (coerceInt value 32)).
Definition mappedPrinter value := translateArrays
  (funcdef_0_PrintInt64_unsigned (fun _ => false)
    (update (fun _ => 0%Z) vardef_0_PrintInt64_unsigned_num value))
  (arrayType _ environment2)
  (fun name => match name with arraydef_0_PrintInt64_buffer => arraydef_0__printBuffer end)
  (fun name => match name with arraydef_0_PrintInt64_buffer => eq_refl end).
Definition mainAction :=
  mappedReader >>= fun _ =>
  readArray arraydef_0__input 0 >>= fun count =>
  writeArray arraydef_0__n 0 count >>= fun _ =>
  mappedReader >>= fun _ =>
  readArray arraydef_0__input 0 >>= fun limit =>
  Dispatch _ _ _ (Grow _ _ arraydef_0__weights count 0%Z) (fun _ => Done _ _ _ tt) >>= fun _ =>
  Dispatch _ _ _ (Grow _ _ arraydef_0__values count 0%Z) (fun _ => Done _ _ _ tt) >>= fun _ =>
  Dispatch _ _ _ (Grow _ _ arraydef_0__dp (coerceInt (coerceInt (count + 1) 64 * coerceInt (limit + 1) 64) 64) 0%Z) (fun _ => Done _ _ _ tt) >>= fun _ =>
  loadAction count >>= fun _ =>
  funcdef_0__solve (fun _ => false) (fun _ => limit) >>= fun _ =>
  readArray arraydef_0__dp (previousIndex count limit limit) >>= fun answer =>
  mappedPrinter answer >>= fun _ =>
  Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar 10)) (fun _ => Done _ _ _ tt).

Ltac normalize_main :=
  repeat progress (autorewrite with advance_program main_maps; cbn [bind]).

Lemma mainNormalized : funcdef_0__main (fun _ => false) (fun _ => 0) = mainAction.
Proof.
  unfold funcdef_0__main, funcdef_0__main_body.
  cbn [bind]. fold mappedReader.
  unfold numberLocalSet, numberLocalGet, retrieve, store, grow, addInt, multInt, writeChar.
  cbn [bind]. rewrite eliminateLift.
  unfold mainAction. f_equal. apply functional_extensionality. intros [].
  normalize_main. unfold readArray. cbn [bind].
  f_equal. apply functional_extensionality. intro count.
  normalize_main. unfold writeArray. cbn [bind].
  f_equal. apply functional_extensionality. intros [].
  normalize_main.
  f_equal. apply functional_extensionality. intros [].
  normalize_main.
  f_equal. apply functional_extensionality. intro limit.
  normalize_main.
  f_equal. apply functional_extensionality. intros [].
  normalize_main.
  f_equal. apply functional_extensionality. intros [].
  normalize_main.
  f_equal. apply functional_extensionality. intros [].
  normalize_main.
  unfold loadAction.
  match goal with |- eliminateLocalVariables ?b ?nums (loop ?n ?body >>= ?continuation) = arrayLoop _ ?code >>= _ =>
    assert (loadBody : forall index next,
      eliminateLocalVariables b nums (body index >>= next) =
      code index >>= fun _ => eliminateLocalVariables b nums (next KeepGoing))
  end.
  { intros index next. cbn beta.
    autorewrite with main_maps. rewrite <- !bindAssoc.
    normalize_main. fold mappedReader. cbn [bind].
    unfold readArray, writeArray. cbn [bind].
    f_equal. apply functional_extensionality. intros [].
    normalize_main.
    f_equal. apply functional_extensionality. intro weight.
    normalize_main.
    f_equal. apply functional_extensionality. intros [].
    normalize_main. fold mappedReader. rewrite <- !bindAssoc. reflexivity. }
  rewrite (eliminate_arrayLoop _ _ _ _ _ loadBody).
  f_equal. apply functional_extensionality. intros [].
  normalize_main.
  replace (update (fun _ : varsfuncdef_0__solve => 0%Z) vardef_0__solve_limit limit) with (fun _ : varsfuncdef_0__solve => limit).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  f_equal. apply functional_extensionality. intros [].
  normalize_main. unfold previousIndex. cbn [bind].
  f_equal. apply functional_extensionality. intro answer.
  normalize_main. fold mappedPrinter. reflexivity.
Qed.

Definition itemsInput items := concat (map (fun item : nat * nat => decimalBytes (fst item) ++ [32%Z] ++ decimalBytes (snd item) ++ [10%Z]) items).
Definition loadingArrays count weights values dp inputValue : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__dp => dp
  | arraydef_0__weights => weights
  | arraydef_0__values => values
  | arraydef_0__message => [0%Z]
  | arraydef_0__n => [Z.of_nat count]
  | arraydef_0__input => [inputValue]
  | arraydef_0__printBuffer => repeat 0%Z 20
  end.
Definition loadingMachine count weights values dp inputValue input :=
  {| memory := loadingArrays count weights values dp inputValue; stdin := input; stdout := [] |}.
Ltac fold_loading :=
  match goal with |- context [{| memory := loadingArrays ?n ?w ?v ?dp ?value; stdin := ?stream; stdout := [] |}] =>
    change {| memory := loadingArrays n w v dp value; stdin := stream; stdout := [] |}
      with (loadingMachine n w v dp value stream)
  end.
Lemma modify_loading_input count weights values dp oldValue value :
  modifyArray (loadingArrays count weights values dp oldValue) arraydef_0__input 0 value =
  loadingArrays count weights values dp value.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma modify_loading_weights count weights values dp inputValue index value :
  modifyArray (loadingArrays count weights values dp inputValue) arraydef_0__weights index value =
  loadingArrays count (<[index := value]> weights) values dp inputValue.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma modify_loading_values count weights values dp inputValue index value :
  modifyArray (loadingArrays count weights values dp inputValue) arraydef_0__values index value =
  loadingArrays count weights (<[index := value]> values) dp inputValue.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.

Lemma loadingRead value separator tail count weights values dp inputValue
  (hValue : (value < 2^64)%nat) (hSeparator : invalidDigit separator = true) :
  exec mappedReader (loadingMachine count weights values dp inputValue (decimalBytes value ++ separator :: tail)) =
  Some (tt, loadingMachine count weights values dp (Z.of_nat value) tail).
Proof.
  change (exec mappedReader (withInput (loadingMachine count weights values dp inputValue []) (decimalBytes value ++ separator :: tail)) = Some (tt, loadingMachine count weights values dp (Z.of_nat value) tail)).
  rewrite decimalReaderExecution; [| assumption | assumption | cbn [loadingMachine memory loadingArrays length]; lia].
  unfold withMemory, withInput, loadingMachine. cbn [memory stdin stdout].
  rewrite modify_loading_input. reflexivity.
Qed.

Lemma coerce_nat32 value (h : (value < 2^32)%nat) : coerceInt (Z.of_nat value) 32 = Z.of_nat value.
Proof.
  unfold coerceInt. apply Z.mod_small. split; [lia |].
  assert (power : Z.of_nat (2^32)%nat = (2^32)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  rewrite <- power. lia.
Qed.
Lemma loading_insert {A} (prefix : list A) zero suffixLength value :
  <[length prefix := value]>(prefix ++ repeat zero (S suffixLength)) = (prefix ++ [value]) ++ repeat zero suffixLength.
Proof.
  rewrite insert_app_r_alt; [| lia]. rewrite Nat.sub_diag. cbn [repeat insert].
  rewrite <- app_assoc. reflexivity.
Qed.

Definition loadRemaining n count :=
  arrayLoop count (fun remaining =>
    mappedReader >>= fun _ =>
    readArray arraydef_0__input 0 >>= fun weight =>
    writeArray arraydef_0__weights (Z.of_nat n - Z.of_nat remaining - 1) (coerceInt weight 32) >>= fun _ =>
    mappedReader >>= fun _ =>
    readArray arraydef_0__input 0 >>= fun value =>
    writeArray arraydef_0__values (Z.of_nat n - Z.of_nat remaining - 1) (coerceInt value 32)).

Lemma loadExecution prefix remaining dp inputValue
  (hWeights : forall item, In item remaining -> (fst item < 2^32)%nat)
  (hValues : forall item, In item remaining -> (snd item < 2^32)%nat) :
  exec (loadRemaining (length prefix + length remaining) (length remaining))
    (loadingMachine (length prefix + length remaining)
      (map (fun item => Z.of_nat (fst item)) prefix ++ repeat 0%Z (length remaining))
      (map (fun item => Z.of_nat (snd item)) prefix ++ repeat 0%Z (length remaining))
      dp inputValue (itemsInput remaining)) =
  Some (tt, loadingMachine (length prefix + length remaining)
    (map (fun item => Z.of_nat (fst item)) (prefix ++ remaining))
    (map (fun item => Z.of_nat (snd item)) (prefix ++ remaining))
    dp (fold_left (fun _ item => Z.of_nat (snd item)) remaining inputValue) []).
Proof.
  induction remaining as [| [weight value] remaining IH] in prefix, inputValue, hWeights, hValues |- *.
  - unfold loadRemaining. cbn [arrayLoop exec repeat itemsInput map concat fold_left]. rewrite !app_nil_r. reflexivity.
  - cbn [length]. unfold loadRemaining at 1. cbn [arrayLoop]. rewrite exec_bind.
    assert (hw : (weight < 2^32)%nat) by (apply (hWeights (weight, value)); cbn; auto).
    assert (hv : (value < 2^32)%nat) by (apply (hValues (weight, value)); cbn; auto).
    assert (powerOrder : (2^32 < 2^64)%nat) by (apply Nat.pow_lt_mono_r; lia).
    unfold itemsInput at 1. cbn [map concat fst snd]. fold (itemsInput remaining).
    rewrite <- !app_assoc. cbn [app].
    rewrite exec_bind.
    rewrite loadingRead; [| lia | reflexivity].
    cbn [optionBind fst snd].
    rewrite (execRead arraydef_0__input 0 0%Z); [| cbn [loadingMachine memory loadingArrays length]; lia].
    cbn [loadingMachine memory loadingArrays nth]. rewrite coerce_nat32; [| exact hw].
    replace (Z.of_nat (length prefix + S (length remaining)) - Z.of_nat (length remaining) - 1)%Z with (Z.of_nat (length prefix)) by lia.
    rewrite exec_bind, execWrite; [| cbn [loadingMachine memory loadingArrays length]; rewrite length_app, length_map, repeat_length; lia].
    cbn [optionBind fst snd]. unfold withMemory. cbn [loadingMachine memory stdin stdout].
    rewrite modify_loading_weights.
    assert (insertWeight : <[length prefix := Z.of_nat weight]>
      (map (fun item : nat * nat => Z.of_nat (fst item)) prefix ++ repeat 0%Z (S (length remaining))) =
      map (fun item : nat * nat => Z.of_nat (fst item)) (prefix ++ [(weight, value)]) ++ repeat 0%Z (length remaining)).
    { replace (length prefix) with (length (map (fun item : nat * nat => Z.of_nat (fst item)) prefix)) by (rewrite length_map; reflexivity).
      rewrite loading_insert, map_app. reflexivity. }
    match goal with |- context [loadingArrays _ ?weights _ _ _] =>
      assert (weightEq : weights = map (fun item : nat * nat => Z.of_nat (fst item)) (prefix ++ [(weight, value)]) ++ repeat 0%Z (length remaining)) by exact insertWeight
    end.
    rewrite weightEq.
    fold_loading.
    rewrite exec_bind, loadingRead; [| lia | reflexivity].
    cbn [optionBind fst snd].
    rewrite (execRead arraydef_0__input 0 0%Z); [| cbn [loadingMachine memory loadingArrays length]; lia].
    cbn [loadingMachine memory loadingArrays nth]. rewrite coerce_nat32; [| exact hv].
    rewrite execWrite; [| cbn [loadingMachine memory loadingArrays]; rewrite length_app, length_map, repeat_length; lia].
    cbn [optionBind fst snd]. unfold withMemory. cbn [loadingMachine memory stdin stdout].
    rewrite modify_loading_values.
    assert (insertValue : <[length prefix := Z.of_nat value]>
      (map (fun item : nat * nat => Z.of_nat (snd item)) prefix ++ repeat 0%Z (S (length remaining))) =
      map (fun item : nat * nat => Z.of_nat (snd item)) (prefix ++ [(weight, value)]) ++ repeat 0%Z (length remaining)).
    { replace (length prefix) with (length (map (fun item : nat * nat => Z.of_nat (snd item)) prefix)) by (rewrite length_map; reflexivity).
      rewrite loading_insert, map_app. reflexivity. }
    match goal with |- context [loadingArrays _ _ ?values _ _] =>
      assert (valueEq : values = map (fun item : nat * nat => Z.of_nat (snd item)) (prefix ++ [(weight, value)]) ++ repeat 0%Z (length remaining)) by exact insertValue
    end.
    rewrite valueEq. fold_loading.
    specialize (IH (prefix ++ [(weight, value)]) (Z.of_nat value) ltac:(intros; apply hWeights; cbn; auto) ltac:(intros; apply hValues; cbn; auto)).
    rewrite length_app in IH. cbn [length] in IH.
    replace (length prefix + 1 + length remaining)%nat with (length prefix + S (length remaining))%nat in IH by lia.
    rewrite <- !app_assoc in IH. cbn [app] in IH.
    exact IH.
Qed.
