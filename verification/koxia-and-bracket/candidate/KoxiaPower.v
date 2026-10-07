From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaModular.
From Generated Require Import KoxiaAndBracket.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality Lia.
Local Open Scope Z_scope.

Definition powerNums base exponent answer : varsfuncdef_0__power -> Z :=
  fun name => match name with
  | vardef_0__power_base => base
  | vardef_0__power_exponent => exponent
  | vardef_0__power_answer => answer
  end.
Definition powerLoopBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power)
  withLocalVariablesReturnValue LoopOutcome :=
(fun binder_0_intermediate => let binder_0 := Done (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power) withLocalVariablesReturnValue _ (Z.sub (Z.sub 64%Z (Z.of_nat binder_0_intermediate)) 1%Z) in dropWithinLoop ((
  ((liftToWithinLoop ((numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent)) >>= fun x => (Done _ _ _ 0%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (break arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => ((liftToWithinLoop ((modIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent)) (Done _ _ _ 2%Z)) >>= fun x => (Done _ _ _ 1%Z) >>= fun y => Done _ _ _ (bool_decide (x = y)))) >>= fun x => if x then (
    (liftToWithinLoop ((modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_answer)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base))) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_answer) x)) >>=
    fun _ => Done _ _ _ tt
  ) else (
    Done _ _ _ tt
  )) >>=
  fun _ => (liftToWithinLoop ((modIntUnsigned (multInt 64 (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base)) (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base))) (Done _ _ _ 998244353%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_base) x)) >>=
  fun _ => (liftToWithinLoop ((divIntUnsigned (numberLocalGet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent)) (Done _ _ _ 2%Z)) >>= fun x => numberLocalSet arrayIndex1 (arrayType _ environment1) varsfuncdef_0__power (vardef_0__power_exponent) x)) >>=
  fun _ => Done _ _ _ tt
))).

Definition machineProduct x y := (coerceInt (x*y) 64) mod koxiaModulus.
Definition nextPowerAnswer base exponent answer :=
  if bool_decide (exponent mod 2 = 1) then machineProduct answer base else answer.
Fixpoint powerLocals fuel base exponent answer :=
  match fuel with
  | O => powerNums base exponent answer
  | S fuel => if bool_decide (exponent = 0) then powerNums base exponent answer else
      powerLocals fuel (machineProduct base base) (exponent/2)
        (nextPowerAnswer base exponent answer)
  end.

Lemma powerNums_base old exponent answer base :
  update (powerNums old exponent answer) vardef_0__power_base base = powerNums base exponent answer.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma powerNums_exponent base old answer exponent :
  update (powerNums base old answer) vardef_0__power_exponent exponent = powerNums base exponent answer.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma powerNums_answer base exponent old answer :
  update (powerNums base exponent old) vardef_0__power_answer answer = powerNums base exponent answer.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Create Rewrite HintDb koxia_power_steps.
#[local] Hint Rewrite powerNums_base powerNums_exponent powerNums_answer
  @dropWithinLoopLiftToWithinLoop @dropWithinLoop_break @dropWithinLoop_1 : koxia_power_steps.
Ltac normalize_power := repeat progress
  (autorewrite with advance_program koxia_power_steps; try rewrite <- !bindAssoc; cbn [bind powerNums]).

Lemma powerLoopStep b base exponent answer index continuation :
  eliminateLocalVariables b (powerNums base exponent answer) (powerLoopBody index >>= continuation) =
  if bool_decide (exponent = 0) then eliminateLocalVariables b (powerNums base exponent answer) (continuation Stop)
  else eliminateLocalVariables b
    (powerNums (machineProduct base base) (exponent/2) (nextPowerAnswer base exponent answer))
    (continuation KeepGoing).
Proof.
  unfold powerLoopBody, numberLocalGet, numberLocalSet, multInt, modIntUnsigned, divIntUnsigned.
  autorewrite with koxia_power_steps. rewrite <- !bindAssoc. normalize_power.
  match goal with |- context [if ?test then _ else _] =>
    let testType := type of test in unify testType bool;
    assert (testEq : test = bool_decide (exponent = 0)) by reflexivity; rewrite testEq
  end.
  destruct (bool_decide (exponent = 0)) eqn:zero; cbn [bind].
  - repeat progress (normalize_power; try rewrite zero; cbn [bind]). reflexivity.
  - repeat progress (normalize_power; try rewrite zero; cbn [bind]).
    repeat progress (rewrite decide_False by lia; normalize_power).
    destruct (bool_decide (exponent mod 2 = 1)) eqn:odd;
      repeat progress (normalize_power; try rewrite odd; cbn [bind]; try rewrite decide_False by lia).
    all: unfold machineProduct, nextPowerAnswer, koxiaModulus; rewrite odd; reflexivity.
Qed.

Lemma powerLoopNormalized b fuel base exponent answer continuation :
  eliminateLocalVariables b (powerNums base exponent answer)
    (loop fuel powerLoopBody >>= continuation) =
  eliminateLocalVariables b (powerLocals fuel base exponent answer) (continuation tt).
Proof.
  induction fuel as [| fuel IH] in base, exponent, answer |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, powerLoopStep. cbn [powerLocals].
  destruct (bool_decide (exponent = 0)); cbn [bind]; [reflexivity | apply IH].
Qed.

Definition powerAction base exponent :=
  Dispatch (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit
    (Store _ _ arraydef_0__result 2 (powerLocals 64 base exponent 1 vardef_0__power_answer))
    (fun _ => Done _ _ _ tt).

Lemma generated_power_normalized b nums :
  funcdef_0__power b nums = powerAction (nums vardef_0__power_base) (nums vardef_0__power_exponent).
Proof.
  unfold funcdef_0__power, funcdef_0__power_body.
  change (eliminateLocalVariables b nums
    ((Done _ _ _ 1 >>= fun value => numberLocalSet _ _ _ vardef_0__power_answer value) >>=
      fun _ => loop 64 powerLoopBody >>= fun _ =>
      (Done _ _ _ 2 >>= fun index =>
      (numberLocalGet _ _ _ vardef_0__power_answer >>= fun value => Done _ _ _ value) >>= fun value =>
      store _ _ _ arraydef_0__result index value) >>= fun _ => Done _ _ _ tt) =
      powerAction (nums vardef_0__power_base) (nums vardef_0__power_exponent)).
  unfold numberLocalSet. cbn [bind]. rewrite pushNumberSet.
  replace (update nums vardef_0__power_answer 1) with
    (powerNums (nums vardef_0__power_base) (nums vardef_0__power_exponent) 1).
  2: { apply functional_extensionality. intro name. destruct name; cbn [powerNums]; reflexivity. }
  rewrite powerLoopNormalized. unfold powerAction, numberLocalGet, store.
  normalize_power. reflexivity.
Qed.

Lemma bool_decide_eqb x y : bool_decide (x = y) = Z.eqb x y.
Proof.
  destruct (bool_decide (x = y)) eqn:b, (Z.eqb x y) eqn:z; try reflexivity.
  - apply bool_decide_eq_true in b. apply Z.eqb_neq in z. contradiction.
  - apply bool_decide_eq_false in b. apply Z.eqb_eq in z. contradiction.
Qed.

Lemma powerLocals_answer fuel base exponent answer :
  0 <= base < koxiaModulus -> 0 <= answer < koxiaModulus ->
  powerLocals fuel base exponent answer vardef_0__power_answer = fastPower fuel base exponent answer.
Proof.
  induction fuel as [| fuel IH] in base, exponent, answer |- *; [reflexivity |].
  intros hb ha. cbn [powerLocals fastPower]. rewrite bool_decide_eqb.
  destruct (Z.eqb exponent 0); [reflexivity |].
  unfold nextPowerAnswer, machineProduct. rewrite bool_decide_eqb.
  rewrite residue_product_coerce by exact hb. rewrite IH.
  - destruct (Z.eqb (exponent mod 2) 1); [rewrite residue_product_coerce by assumption |]; reflexivity.
  - apply residue_bounds.
  - destruct (Z.eqb (exponent mod 2) 1); [apply residue_bounds | exact ha].
Qed.

Theorem generated_power_execution b nums state :
  0 <= nums vardef_0__power_base < koxiaModulus ->
  0 <= nums vardef_0__power_exponent < 2^64 ->
  (2 < length (memory state arraydef_0__result))%nat ->
  exec (funcdef_0__power b nums) state =
  Some (tt, withMemory state (modifyArray (memory state) arraydef_0__result 2
    ((nums vardef_0__power_base)^(nums vardef_0__power_exponent) mod koxiaModulus))).
Proof.
  intros hb he storage. rewrite generated_power_normalized. unfold powerAction.
  rewrite powerLocals_answer by (try exact hb; unfold koxiaModulus; lia).
  rewrite fastPower_correct by (try exact he; unfold koxiaModulus; lia).
  rewrite Z.mul_1_l. cbn [exec step optionBind]. rewrite decide_True by exact storage. reflexivity.
Qed.
