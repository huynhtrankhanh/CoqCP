From CoqCP Require Import Options Imperative Execution Knapsack KnapsackCode KnapsackTable KnapsackExecution KnapsackIO KnapsackMain KnapsackPrinter DecimalDigits.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
From Coq Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.

Lemma modify_loading_n count weights values dp inputValue newCount :
  modifyArray (loadingArrays count weights values dp inputValue) arraydef_0__n 0 (Z.of_nat newCount) =
  loadingArrays newCount weights values dp inputValue.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma grow_loading_weights count weights values dp inputValue size :
  growArrays (loadingArrays count weights values dp inputValue) arraydef_0__weights size 0%Z =
  loadingArrays count (growList weights size 0%Z) values dp inputValue.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma grow_loading_values count weights values dp inputValue size :
  growArrays (loadingArrays count weights values dp inputValue) arraydef_0__values size 0%Z =
  loadingArrays count weights (growList values size 0%Z) dp inputValue.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Lemma grow_loading_dp count weights values dp inputValue size :
  growArrays (loadingArrays count weights values dp inputValue) arraydef_0__dp size 0%Z =
  loadingArrays count weights values (growList dp size 0%Z) inputValue.
Proof. apply functional_extensionality_dep. intro name. destruct name; reflexivity. Qed.
Definition arrayZero name : arrayType _ environment2 name := match name with
| arraydef_0__dp | arraydef_0__weights | arraydef_0__values | arraydef_0__message
| arraydef_0__n | arraydef_0__input | arraydef_0__printBuffer => 0%Z end.
Definition growAction name size : Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit :=
  Dispatch (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit
    (Grow _ _ name size (arrayZero name)) (fun _ => Done _ _ _ tt).
Lemma execGrow name size s : exec (growAction name size) s =
  Some (tt, withMemory s (growArrays (memory s) name (Z.to_nat size) (arrayZero name))).
Proof. reflexivity. Qed.
Lemma initialLoading items limit :
  {| memory := arrays _ environment2; stdin := generateData items limit; stdout := [] |} =
  loadingMachine 0 [] [] [] 0 (decimalBytes (length items) ++ 32 :: decimalBytes limit ++ 10 :: itemsInput items).
Proof. reflexivity. Qed.

Lemma mainExecution items limit
  (hSize : (tableSize items limit < 2^64)%nat)
  (hWeights : forall item, In item items -> (fst item < 2^32)%nat)
  (hValues : forall item, In item items -> (snd item < 2^32)%nat)
  (hSum : (list_sum (map snd items) < 2^64)%nat) :
  exists s, exec (funcdef_0__main (fun _ => false) (fun _ => 0))
    {| memory := arrays _ environment2; stdin := generateData items limit; stdout := [] |} = Some (tt, s) /\
    stdout s = decimalBytes (knapsack items limit) ++ [10].
Proof.
  assert (hCount : (length items < 2^64)%nat) by (unfold tableSize in hSize; nia).
  assert (hLimit : (limit < 2^64)%nat) by (unfold tableSize in hSize; nia).
  rewrite mainNormalized, initialLoading. unfold mainAction.
  rewrite exec_bind, loadingRead; [| exact hCount | reflexivity]. cbn [optionBind fst snd].
  rewrite (execRead arraydef_0__input 0 0%Z); [| cbn [loadingMachine memory loadingArrays length]; lia].
  cbn [loadingMachine memory loadingArrays nth]. rewrite exec_bind, (execWrite arraydef_0__n 0 (Z.of_nat (length items))); [| cbn [loadingMachine memory loadingArrays length]; lia].
  cbn [optionBind fst snd]. unfold withMemory. cbn [loadingMachine memory stdin stdout].
  rewrite modify_loading_n. fold_loading.
  rewrite exec_bind, loadingRead; [| exact hLimit | reflexivity]. cbn [optionBind fst snd].
  rewrite (execRead arraydef_0__input 0 0%Z); [| cbn [loadingMachine memory loadingArrays length]; lia].
  cbn [loadingMachine memory loadingArrays nth].
  change (Dispatch _ _ _ (Grow _ _ arraydef_0__weights (Z.of_nat (length items)) 0%Z) (fun _ => Done _ _ _ tt)) with (growAction arraydef_0__weights (Z.of_nat (length items))).
  rewrite exec_bind, execGrow. cbn [optionBind fst snd].
  unfold withMemory. cbn [loadingMachine memory stdin stdout]. rewrite Nat2Z.id, grow_loading_weights.
  cbn [growList length Nat.sub app]. fold_loading.
  change (Dispatch _ _ _ (Grow _ _ arraydef_0__values (Z.of_nat (length items)) 0%Z) (fun _ => Done _ _ _ tt)) with (growAction arraydef_0__values (Z.of_nat (length items))).
  rewrite exec_bind, execGrow. cbn [optionBind fst snd].
  unfold withMemory. cbn [loadingMachine memory stdin stdout]. rewrite Nat2Z.id, grow_loading_values.
  cbn [growList length Nat.sub app]. fold_loading.
  replace (Z.of_nat (length items) + 1) with (Z.of_nat (length items + 1)) by lia.
  replace (Z.of_nat limit + 1) with (Z.of_nat (limit + 1)) by lia.
  rewrite !coerce_nat64; [| unfold tableSize in hSize; nia | unfold tableSize in hSize; nia].
  rewrite <- Nat2Z.inj_mul, coerce_nat64; [| exact hSize].
  match goal with |- context[Dispatch _ _ _ (Grow _ _ arraydef_0__dp ?size ?zero) ?next] =>
    change (Dispatch _ _ _ (Grow _ _ arraydef_0__dp size zero) next) with (growAction arraydef_0__dp size)
  end.
  rewrite exec_bind, execGrow. cbn [optionBind fst snd].
  unfold withMemory. cbn [loadingMachine memory stdin stdout]. rewrite Nat2Z.id, grow_loading_dp.
  cbn [growList length Nat.sub app]. fold_loading.
  rewrite !Nat.sub_0_r.
  assert (loaded : exec (loadAction (Z.of_nat (length items)))
    (loadingMachine (length items) (repeat 0%Z (length items)) (repeat 0%Z (length items))
      (repeat 0%Z (tableSize items limit)) (Z.of_nat limit) (itemsInput items)) =
    Some (tt, loadingMachine (length items) (map (fun item => Z.of_nat (fst item)) items)
      (map (fun item => Z.of_nat (snd item)) items) (repeat 0%Z (tableSize items limit))
      (fold_left (fun _ item => Z.of_nat (snd item)) items (Z.of_nat limit)) [])).
  { unfold loadAction. rewrite Nat2Z.id. exact (loadExecution [] items (repeat 0%Z (tableSize items limit)) (Z.of_nat limit) hWeights hValues). }
  rewrite exec_bind.
  match goal with |- context[exec (loadAction ?count) ?state] =>
    assert (loadedNative : exec (loadAction count) state =
      Some (tt, loadingMachine (length items) (map (fun item => Z.of_nat (fst item)) items)
        (map (fun item => Z.of_nat (snd item)) items) (repeat 0%Z (tableSize items limit))
        (fold_left (fun _ item => Z.of_nat (snd item)) items (Z.of_nat limit)) [])) by exact loaded
  end. rewrite loadedNative. cbn [optionBind fst snd].
  set (lastInput := fold_left (fun _ item => Z.of_nat (snd item)) items (Z.of_nat limit)).
  replace (loadingMachine (length items) (map (fun item => Z.of_nat (fst item)) items)
    (map (fun item => Z.of_nat (snd item)) items) (repeat 0%Z (tableSize items limit)) lastInput [])
    with (tableMachine items limit (limit + 1) 0 [lastInput] (repeat 0%Z 20))
    by (unfold tableMachine; rewrite table_base; reflexivity).
  rewrite solveNormalized.
  change (Dispatch _ _ _ (Retrieve _ _ arraydef_0__n 0) (fun count => solveAction count (Z.of_nat limit)))
    with (readArray arraydef_0__n 0 >>= fun count => solveAction count (Z.of_nat limit)).
  rewrite <- bindAssoc, (execRead arraydef_0__n 0 0%Z); [| cbn [tableMachine memory knapsackArrays length]; lia].
  cbn [tableMachine memory knapsackArrays nth]. rewrite exec_bind, solveActionExecution; try assumption.
  cbn [optionBind fst snd].
  rewrite previousIndex_nat; [| exact hSize | lia].
  rewrite (execRead arraydef_0__dp _ 0%Z); [| cbn [tableMachine memory knapsackArrays]; rewrite table_length; [unfold tableSize; nia | lia]].
  cbn [tableMachine memory knapsackArrays]. rewrite table_read; [| lia | unfold tableSize; nia].
  rewrite take_ge; [| lia]. rewrite knapsackReverse.
  assert (hAnswer : (knapsack items limit < 2^64)%nat) by (pose proof (knapsack_sum items limit); lia).
  rewrite exec_bind.
  set (result := tableMachine items limit (tableSize items limit) 0 [lastInput] (repeat 0%Z 20)).
  assert (bufferInitial : setBuffer result (repeat 0%Z 20) = result) by reflexivity.
  destruct (printerExecution (knapsack items limit) result hAnswer) as [buffer printed].
  rewrite bufferInitial in printed. rewrite printed. cbn [optionBind fst snd].
  eexists. split; [reflexivity | reflexivity].
Qed.
