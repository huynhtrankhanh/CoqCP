From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaIntegers.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.

Definition inputNums n ch balance minimum split : varsfuncdef_0__main -> Z :=
  fun name => match name with
  | vardef_0__main_n => n
  | vardef_0__main_ch => ch
  | vardef_0__main_balance => balance
  | vardef_0__main_minimum => minimum
  | vardef_0__main_split => split
  | _ => 0
  end.
Definition inputLoopBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main)
  withLocalVariablesReturnValue LoopOutcome :=
(fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) withLocalVariablesReturnValue _ (Z.sub (Z.sub 500001%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  (liftToWithinLoop ((readChar arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch) x)) >>=
  fun _ => ((liftToWithinLoop (shortCircuitAnd ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))) ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 41%Z) >>= fun y => Done _ _ _ (bool_decide (x <> y))))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => (((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => Done _ _ _ (coerceInt x 8)) >>= fun tuple_element_0 => Done _ _ _ (tuple_element_0)) >>= fun y => store arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (arraydef_0__sequence) x y)) >>=
  fun _ => (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n) x)) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_ch)) >>= fun x => (Done _ _ _ 40%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((addInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    (liftToWithinLoop ((subInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) (Done _ _ _ 1%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance) x)) >>=
    fun _ => Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) >>= fun a => (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_minimum)) >>= fun b => Done _ _ _ (bool_decide (Z.lt (toSigned a 64) (toSigned b 64))))) >>= fun x => if x then (
    (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_balance)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_minimum) x)) >>=
    fun _ => (liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_n)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__main (vardef_0__main_split) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => Done _ _ _ tt
))).

Definition invalidBracket ch := bool_decide (ch<>40) && bool_decide (ch<>41).
Definition nextBalance ch level := if bool_decide (ch=40) then coerceInt (level+1) 64 else coerceInt (level-1) 64.
Definition nextInputNums n ch level minimum split :=
  let n := coerceInt (n+1) 64 in
  let level := nextBalance ch level in
  if bool_decide (toSigned level 64 < toSigned minimum 64)
  then inputNums n ch level level n else inputNums n ch level minimum split.
Definition inputCharAction :=
  Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue Z
    (DoBasicEffect _ _ ReadChar) (fun ch => Done _ _ _ ch).
Definition sequenceStore index ch :=
  Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit
    (Store _ _ arraydef_0__sequence index (coerceInt ch 8)) (fun _ => Done _ _ _ tt).
Fixpoint inputAction fuel (nums : varsfuncdef_0__main -> Z) :
  Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue (varsfuncdef_0__main -> Z) :=
  match fuel with
  | O => Done _ _ _ nums
  | S fuel => inputCharAction >>= fun ch =>
      if invalidBracket ch then Done _ _ _ (update nums vardef_0__main_ch ch)
      else sequenceStore (nums vardef_0__main_n) ch >>= fun _ =>
        inputAction fuel (nextInputNums (nums vardef_0__main_n) ch
          (nums vardef_0__main_balance) (nums vardef_0__main_minimum) (nums vardef_0__main_split))
  end.

Lemma inputNums_n old ch level minimum split n :
  update (inputNums old ch level minimum split) vardef_0__main_n n = inputNums n ch level minimum split.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma inputNums_ch n old level minimum split ch :
  update (inputNums n old level minimum split) vardef_0__main_ch ch = inputNums n ch level minimum split.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma inputNums_balance n ch old minimum split level :
  update (inputNums n ch old minimum split) vardef_0__main_balance level = inputNums n ch level minimum split.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma inputNums_minimum n ch level old split minimum :
  update (inputNums n ch level old split) vardef_0__main_minimum minimum = inputNums n ch level minimum split.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma inputNums_split n ch level minimum old split :
  update (inputNums n ch level minimum old) vardef_0__main_split split = inputNums n ch level minimum split.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Create Rewrite HintDb koxia_input_steps.
#[local] Hint Rewrite inputNums_n inputNums_ch inputNums_balance inputNums_minimum inputNums_split
  @dropWithinLoopLiftToWithinLoop @dropWithinLoop_break @dropWithinLoop_1 : koxia_input_steps.
Ltac normalize_input := repeat progress
  (autorewrite with advance_program koxia_input_steps; try rewrite <- !bindAssoc; cbn [bind inputNums]).

Lemma inputLoopStep b n old level minimum split index continuation :
  eliminateLocalVariables b (inputNums n old level minimum split) (inputLoopBody index >>= continuation) =
  inputCharAction >>= fun ch =>
    if invalidBracket ch then eliminateLocalVariables b (inputNums n ch level minimum split) (continuation Stop)
    else sequenceStore n ch >>= fun _ =>
      eliminateLocalVariables b (nextInputNums n ch level minimum split) (continuation KeepGoing).
Proof.
  unfold inputLoopBody, readChar, numberLocalGet, numberLocalSet, store, addInt, subInt, shortCircuitAnd.
  autorewrite with koxia_input_steps. rewrite <- !bindAssoc. cbn [bind].
  rewrite pushDispatch. unfold inputCharAction. cbn [bind]. f_equal.
  apply functional_extensionality. intro ch. normalize_input.
  unfold invalidBracket. destruct (Z.eq_dec ch 40) as [opens | notOpen];
    destruct (Z.eq_dec ch 41) as [closes | notClose]; try congruence.
  all: repeat progress (normalize_input; rewrite ?bool_decide_true by congruence;
    rewrite ?bool_decide_false by congruence; cbn [andb bind]).
  all: try reflexivity.
  all: unfold sequenceStore, nextInputNums, nextBalance; cbn [bind].
  all: f_equal; apply functional_extensionality; intros []; normalize_input.
  all: repeat progress (rewrite ?bool_decide_true by congruence;
    rewrite ?bool_decide_false by congruence; normalize_input).
  all: repeat (case_bool_decide; normalize_input; try congruence; try lia).
  all: reflexivity.
Qed.

Lemma inputLoopNormalized b fuel n ch level minimum split continuation :
  eliminateLocalVariables b (inputNums n ch level minimum split)
    (loop fuel inputLoopBody >>= continuation) =
  inputAction fuel (inputNums n ch level minimum split) >>= fun final =>
    eliminateLocalVariables b final (continuation tt).
Proof.
  induction fuel as [| fuel IH] in n,ch,level,minimum,split |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, inputLoopStep. cbn [inputAction inputNums].
  unfold inputCharAction. cbn [bind]. f_equal. apply functional_extensionality. intro next.
  destruct (invalidBracket next); cbn [bind].
  - rewrite inputNums_ch. reflexivity.
  - unfold sequenceStore. cbn [bind]. f_equal. apply functional_extensionality. intros [].
    unfold nextInputNums. destruct (bool_decide (toSigned (nextBalance next level) 64 < toSigned minimum 64)); apply IH.
Qed.

Fixpoint scanInputNums (characters : list Z) (nums : varsfuncdef_0__main -> Z) :=
  match characters with
  | [] => update nums vardef_0__main_ch 10
  | ch::rest => scanInputNums rest (nextInputNums (nums vardef_0__main_n) ch
      (nums vardef_0__main_balance) (nums vardef_0__main_minimum) (nums vardef_0__main_split))
  end.
Lemma input_loading_insert (prefix : list Z) space ch :
  <[length prefix := ch]>(prefix ++ repeat 0 (S space)) = (prefix ++ [ch]) ++ repeat 0 space.
Proof.
  rewrite insert_app_r_alt; [|lia]. rewrite Nat.sub_diag. cbn [repeat insert].
  rewrite <- app_assoc. reflexivity.
Qed.
Lemma nextInputNums_count n ch level minimum split :
  nextInputNums n ch level minimum split vardef_0__main_n = coerceInt (n+1) 64.
Proof.
  unfold nextInputNums. destruct (bool_decide (toSigned (nextBalance ch level) 64 < toSigned minimum 64)); reflexivity.
Qed.

Theorem inputAction_execution characters fuel prefix space nums state :
  Forall (fun ch => ch=40 \/ ch=41) characters ->
  (length characters < fuel)%nat -> (length characters <= space)%nat ->
  Z.of_nat (length prefix + length characters) < 18446744073709551616 ->
  nums vardef_0__main_n = Z.of_nat (length prefix) ->
  stdin state = characters ++ [10] ->
  memory state arraydef_0__sequence = prefix ++ repeat 0 space ->
  exists final,
    exec (inputAction fuel nums) state = Some (scanInputNums characters nums, final) /\
    stdin final=[] /\ stdout final=stdout state /\
    memory final arraydef_0__sequence = (prefix++characters) ++ repeat 0 (space-length characters) /\
    (forall name, name <> arraydef_0__sequence -> memory final name=memory state name).
Proof.
  induction characters as [|ch rest IH] in fuel,prefix,space,nums,state |- *.
  - intros valid enough room bound count incoming storage.
    destruct fuel as [|fuel]; [cbn in enough; lia|].
    cbn [inputAction]. unfold inputCharAction. cbn [bind exec step]. rewrite incoming.
    cbn [optionBind fst snd stdin withInput invalidBracket].
    cbn [andb exec].
    exists (withInput state []). repeat split; try reflexivity.
    + cbn [memory withInput]. rewrite storage, app_nil_r, Nat.sub_0_r. reflexivity.
  - intros valid enough room bound count incoming storage.
    inversion valid as [|head tail headValid restValid]; subst head tail.
    destruct fuel as [|fuel]; [cbn in enough; lia|].
    destruct space as [|space]; [cbn in room; lia|].
    assert (validByte : invalidBracket ch=false /\ coerceInt ch 8=ch).
    { destruct headValid as [-> | ->]; vm_compute; auto. }
    destruct validByte as [isBracket byte].
    cbn [inputAction]. unfold inputCharAction. cbn [bind exec step]. rewrite incoming.
    cbn [app optionBind fst snd stdin withInput]. rewrite isBracket.
    unfold sequenceStore. cbn [bind exec step optionBind]. rewrite count, Nat2Z.id.
    rewrite decide_True by (cbn [memory withInput]; rewrite storage, length_app, repeat_length; lia).
    rewrite byte. cbn [fst snd].
    set (nextState := withMemory (withInput state (rest++[10]))
      (modifyArray (memory state) arraydef_0__sequence (length prefix) ch)).
    set (nextNums := nextInputNums (nums vardef_0__main_n) ch
      (nums vardef_0__main_balance) (nums vardef_0__main_minimum) (nums vardef_0__main_split)).
    assert (nextStorage : memory nextState arraydef_0__sequence =
      (prefix++[ch])++repeat 0 space).
    { unfold nextState. cbn [memory withMemory withInput]. unfold modifyArray.
      destruct (decide (arraydef_0__sequence = arraydef_0__sequence)) as [equal | impossible]; [|congruence].
      replace equal with (@eq_refl arrayIndex1 arraydef_0__sequence) by apply proof_irrel.
      cbn.
      change (<[length prefix:=ch]> (memory state arraydef_0__sequence) = (prefix++[ch])++repeat 0 space).
      setoid_rewrite storage. rewrite input_loading_insert. reflexivity. }
    assert (nextCount : nextNums vardef_0__main_n = Z.of_nat (length (prefix++[ch]))).
    { unfold nextNums. rewrite nextInputNums_count, count, coerce64_small.
      - rewrite length_app, Nat2Z.inj_add. cbn. lia.
      - rewrite Nat2Z.inj_add in bound. cbn in bound.
        change (0 <= Z.of_nat (length prefix)+1 < 18446744073709551616). lia. }
    destruct (IH fuel (prefix++[ch]) space nextNums nextState restValid ltac:(cbn in enough; lia)
      ltac:(cbn in room; lia)
      ltac:(replace (length (prefix++[ch])+length rest)%nat with
        (length prefix+length (ch::rest))%nat by (rewrite length_app; cbn; lia); exact bound)
      nextCount eq_refl nextStorage) as [final [executed [empty [out [loaded other]]]]].
    exists final. split.
    { cbn [optionBind fst snd scanInputNums]. unfold nextNums, nextState in executed.
      rewrite count in executed. rewrite count. exact executed. }
    split; [exact empty|]. split; [exact out|]. split.
    + rewrite loaded.
      replace ((prefix++[ch])++rest) with (prefix++ch::rest) by (rewrite <- app_assoc; reflexivity).
      replace (S space-length (ch::rest))%nat with (space-length rest)%nat by (cbn; lia). reflexivity.
    + intros name different. rewrite other by exact different.
      unfold nextState. cbn [memory withMemory withInput]. unfold modifyArray.
      destruct (decide (name=arraydef_0__sequence)); [congruence|reflexivity].
Qed.
