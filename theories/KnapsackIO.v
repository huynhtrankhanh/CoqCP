From CoqCP Require Import Options Imperative Execution KnapsackCode DecimalDigits.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list.
From Stdlib Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.

Definition readerNums (value character : Z) : varsfuncdef_0_ReadUnsignedInt64_ -> Z :=
  fun name => match name with
  | vardef_0_ReadUnsignedInt64__result => value
  | vardef_0_ReadUnsignedInt64__tmpChar => character
  end.
Definition readerFirstBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_)
  withLocalVariablesReturnValue LoopOutcome := ltac:(
  let code := eval cbn [funcdef_0_ReadUnsignedInt64__body bind] in funcdef_0_ReadUnsignedInt64__body in
  match code with context [loop _ ?body] => exact body end).
Definition readerRestBody : nat -> Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0_ReadUnsignedInt64_)
  withLocalVariablesReturnValue LoopOutcome := ltac:(
  let code := eval cbn [funcdef_0_ReadUnsignedInt64__body bind] in funcdef_0_ReadUnsignedInt64__body in
  match code with (_ >>= ?next) =>
    let rest := eval cbn [bind] in (next tt) in
    match rest with (loop _ _ >>= ?afterFirst) =>
      let last := eval cbn [bind] in (afterFirst tt) in
      match last with (loop _ ?body >>= _) => exact body end
    end
  end).

Definition invalidDigit character := bool_decide (character < 48) || negb (bool_decide (character < 58)).
Definition appendDigit value character := coerceInt (coerceInt (value * 10) 64 + coerceInt (character - 48) 64) 64.
Definition charAction {I T} :=
  Dispatch (WithArrays I T) withArraysReturnValue Z (DoBasicEffect _ _ ReadChar) (fun value => Done _ _ _ value).
Fixpoint readFirst {I T} fuel value character : Action (WithArrays I T) withArraysReturnValue (Z * Z) :=
  match fuel with
  | O => Done _ _ _ (value, character)
  | S fuel => charAction >>= fun character =>
      if invalidDigit character then readFirst fuel value character
      else Done _ _ _ (appendDigit value character, character)
  end.
Fixpoint readRest {I T} fuel value character : Action (WithArrays I T) withArraysReturnValue (Z * Z) :=
  match fuel with
  | O => Done _ _ _ (value, character)
  | S fuel => charAction >>= fun character =>
      if invalidDigit character then Done _ _ _ (value, character)
      else readRest fuel (appendDigit value character) character
  end.

Lemma readerNums_character value previous character :
  update (readerNums value previous) vardef_0_ReadUnsignedInt64__tmpChar character = readerNums value character.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Lemma readerNums_value previous character value :
  update (readerNums previous character) vardef_0_ReadUnsignedInt64__result value = readerNums value character.
Proof. apply functional_extensionality. intro name. destruct name; reflexivity. Qed.
Create Rewrite HintDb reader_steps.
#[local] Hint Rewrite readerNums_character readerNums_value @dropWithinLoopLiftToWithinLoop @dropWithinLoop_continue @dropWithinLoop_break @dropWithinLoop_1 : reader_steps.

Lemma readerFirstStep b value character index continuation :
  eliminateLocalVariables b (readerNums value character) (readerFirstBody index >>= continuation) =
  charAction >>= fun digit =>
    if invalidDigit digit then eliminateLocalVariables b (readerNums value digit) (continuation KeepGoing)
    else eliminateLocalVariables b (readerNums (appendDigit value digit) digit) (continuation Stop).
Proof.
  unfold readerFirstBody, charAction.
  rewrite dropWithinLoopLiftToWithinLoop. rewrite <- !bindAssoc.
  unfold readChar, numberLocalSet. cbn [bind]. rewrite pushDispatch.
  f_equal. apply functional_extensionality. intro digit.
  repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
  unfold shortCircuitOr, numberLocalGet. cbn [bind].
  repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
  repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
  unfold invalidDigit. destruct (bool_decide (digit < 48)); cbn [orb].
  - repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]); reflexivity.
  - repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
    destruct (bool_decide (digit < 58)); cbn [negb orb].
    + unfold addInt, multInt, subInt, appendDigit, numberLocalGet, numberLocalSet.
      repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]); reflexivity.
    + repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]); reflexivity.
Qed.

Lemma readerRestStep b value character index continuation :
  eliminateLocalVariables b (readerNums value character) (readerRestBody index >>= continuation) =
  charAction >>= fun digit =>
    if invalidDigit digit then eliminateLocalVariables b (readerNums value digit) (continuation Stop)
    else eliminateLocalVariables b (readerNums (appendDigit value digit) digit) (continuation KeepGoing).
Proof.
  unfold readerRestBody, charAction.
  rewrite dropWithinLoopLiftToWithinLoop. rewrite <- !bindAssoc.
  unfold readChar, numberLocalSet. cbn [bind]. rewrite pushDispatch.
  f_equal. apply functional_extensionality. intro digit.
  repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
  unfold shortCircuitOr, numberLocalGet. cbn [bind].
  repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
  repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
  unfold invalidDigit. destruct (bool_decide (digit < 48)); cbn [orb].
  - repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]); reflexivity.
  - repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]).
    destruct (bool_decide (digit < 58)); cbn [negb orb].
    + unfold addInt, multInt, subInt, appendDigit, numberLocalGet, numberLocalSet.
      repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]); reflexivity.
    + repeat progress (autorewrite with advance_program reader_steps; cbn [bind readerNums]); reflexivity.
Qed.

Lemma readerFirstLoop b fuel value character continuation :
  eliminateLocalVariables b (readerNums value character) (loop fuel readerFirstBody >>= continuation) =
  readFirst fuel value character >>= fun response =>
    eliminateLocalVariables b (readerNums (fst response) (snd response)) (continuation tt).
Proof.
  induction fuel as [| fuel IH] in value, character |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, readerFirstStep.
  cbn [readFirst]. rewrite <- bindAssoc. unfold charAction. cbn [bind].
  f_equal. apply functional_extensionality. intro digit.
  destruct (invalidDigit digit); cbn [bind].
  - apply IH.
  - reflexivity.
Qed.

Lemma readerRestLoop b fuel value character continuation :
  eliminateLocalVariables b (readerNums value character) (loop fuel readerRestBody >>= continuation) =
  readRest fuel value character >>= fun response =>
    eliminateLocalVariables b (readerNums (fst response) (snd response)) (continuation tt).
Proof.
  induction fuel as [| fuel IH] in value, character |- *; [reflexivity |].
  rewrite loop_S, <- bindAssoc, readerRestStep.
  cbn [readRest]. rewrite <- bindAssoc. unfold charAction. cbn [bind].
  f_equal. apply functional_extensionality. intro digit.
  destruct (invalidDigit digit); cbn [bind].
  - reflexivity.
  - apply IH.
Qed.

Definition readUnsignedAction {I : Type} {T : I -> Type} name
  (hType : T name = Z) : Action (WithArrays I T) withArraysReturnValue unit :=
  readFirst 20 0 0 >>= fun response =>
  readRest 20 (fst response) (snd response) >>= fun response =>
  Dispatch _ _ _ (Store _ _ name 0 (eq_rect_r (fun t => t) (fst response) hType)) (fun _ => Done _ _ _ tt).

Lemma readerNormalized : funcdef_0_ReadUnsignedInt64_ (fun _ => false) (fun _ => 0) =
  readUnsignedAction arraydef_0_ReadUnsignedInt64_resultArray eq_refl.
Proof.
  unfold funcdef_0_ReadUnsignedInt64_, funcdef_0_ReadUnsignedInt64__body.
  cbn [bind]. unfold numberLocalSet. cbn [bind]. rewrite pushNumberSet.
  replace (update (fun _ : varsfuncdef_0_ReadUnsignedInt64_ => 0%Z) vardef_0_ReadUnsignedInt64__result 0) with (readerNums 0 0).
  2: { apply functional_extensionality. intro name. destruct name; reflexivity. }
  fold readerFirstBody readerRestBody.
  change (eliminateLocalVariables (fun _ => false) (readerNums 0 0)
    (loop 20 readerFirstBody >>= fun _ => loop 20 readerRestBody >>= fun _ =>
      (Done _ _ _ 0%Z >>= fun index =>
        (numberLocalGet _ _ _ vardef_0_ReadUnsignedInt64__result >>= fun value => Done _ _ _ value) >>=
        fun value => store _ _ _ arraydef_0_ReadUnsignedInt64_resultArray index value) >>= fun _ => Done _ _ _ tt) = readUnsignedAction arraydef_0_ReadUnsignedInt64_resultArray eq_refl).
  rewrite readerFirstLoop.
  unfold readUnsignedAction. f_equal. apply functional_extensionality. intros [value character].
  cbn [fst snd bind]. rewrite readerRestLoop.
  reflexivity.
Qed.

Lemma translate_readFirst {I J T} fuel value character (U : J -> Type) (mapping : I -> J) congruent :
  translateArrays (@readFirst I T fuel value character) U mapping congruent =
  @readFirst J U fuel value character.
Proof.
  induction fuel as [| fuel IH] in value, character |- *; [reflexivity |].
  cbn [readFirst]. rewrite translateArrays_bind.
  cbn [charAction bind translateArrays Action_rect withArraysReturnValueDoBasicEffectArrayType withArraysReturnValue basicEffectReturnValue].
  f_equal. apply functional_extensionality. intro digit.
  unfold withArraysReturnValueDoBasicEffectArrayType. cbv [eq_rect]. cbn [bind].
  destruct (invalidDigit digit); [apply IH | reflexivity].
Qed.
Lemma translate_readRest {I J T} fuel value character (U : J -> Type) (mapping : I -> J) congruent :
  translateArrays (@readRest I T fuel value character) U mapping congruent =
  @readRest J U fuel value character.
Proof.
  induction fuel as [| fuel IH] in value, character |- *; [reflexivity |].
  cbn [readRest]. rewrite translateArrays_bind.
  cbn [charAction bind translateArrays Action_rect withArraysReturnValueDoBasicEffectArrayType withArraysReturnValue basicEffectReturnValue].
  f_equal. apply functional_extensionality. intro digit.
  unfold withArraysReturnValueDoBasicEffectArrayType. cbv [eq_rect]. cbn [bind].
  destruct (invalidDigit digit); [reflexivity | apply IH].
Qed.

Definition mappedReader := translateArrays
  (funcdef_0_ReadUnsignedInt64_ (fun _ => false) (fun _ => 0))
  (arrayType _ environment2)
  (fun name => match name with arraydef_0_ReadUnsignedInt64_resultArray => arraydef_0__input end)
  (fun name => match name with arraydef_0_ReadUnsignedInt64_resultArray => eq_refl end).
Lemma mappedReaderNormalized : mappedReader = readUnsignedAction arraydef_0__input eq_refl.
Proof.
  unfold mappedReader. rewrite readerNormalized. unfold readUnsignedAction.
  rewrite translateArrays_bind, translate_readFirst.
  f_equal. apply functional_extensionality. intros [value character].
  rewrite translateArrays_bind, translate_readRest.
  reflexivity.
Qed.

Lemma digit_valid character (h : decimalDigit character) : invalidDigit character = false.
Proof.
  unfold invalidDigit, decimalDigit in *. rewrite bool_decide_false; [| lia].
  rewrite bool_decide_true; [reflexivity | lia].
Qed.
Lemma appendDigit_exact value character
  (hValue : 0 <= value) (hDigit : decimalDigit character)
  (hBound : 10 * value + character - 48 < 2^64) :
  appendDigit value character = 10 * value + character - 48.
Proof.
  unfold appendDigit, coerceInt, decimalDigit in *.
  assert (powerPositive : (10 < 2^64)%Z) by (vm_compute; reflexivity).
  rewrite (Z.mod_small (value * 10) (2^64)) by lia.
  rewrite (Z.mod_small (character - 48) (2^64)) by lia.
  rewrite Z.mod_small; lia.
Qed.
Lemma execChar {R}
  (next : Z -> Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue R)
  s character tail :
  exec (charAction >>= next) (withInput s (character :: tail)) =
  exec (next character) (withInput s tail).
Proof. destruct s. reflexivity. Qed.
Lemma readFirst_S {I T} fuel value character :
  @readFirst I T (S fuel) value character =
  charAction >>= fun digit => if invalidDigit digit then readFirst fuel value digit
    else Done _ _ _ (appendDigit value digit, digit).
Proof. reflexivity. Qed.
Lemma readRest_S {I T} fuel value character :
  @readRest I T (S fuel) value character =
  charAction >>= fun digit => if invalidDigit digit then Done _ _ _ (value, digit)
    else readRest fuel (appendDigit value digit) digit.
Proof. reflexivity. Qed.

Lemma readRestExecution fuel digits value character separator tail s
  (hFuel : (length digits < fuel)%nat) (hDigits : Forall decimalDigit digits)
  (hValue : 0 <= value) (hBound : decodeDigits digits value < 2^64)
  (hSeparator : invalidDigit separator = true) :
  exec (@readRest arrayIndex2 (arrayType _ environment2) fuel value character)
    (withInput s (digits ++ separator :: tail)) =
  Some ((decodeDigits digits value, separator), withInput s tail).
Proof.
  induction fuel as [| fuel IH] in digits, value, character, hFuel, hDigits, hValue, hBound |- *; [lia |].
  destruct digits as [| digit digits].
  - cbn [app]. rewrite readRest_S, execChar, hSeparator. reflexivity.
  - inversion hDigits as [| d ds hd hds]; subst d ds.
    cbn [app]. rewrite readRest_S, execChar, (digit_valid digit hd).
    assert (nextNonnegative : 0 <= 10 * value + digit - 48) by (unfold decimalDigit in hd; lia).
    pose proof decodeDigits_ge digits (10 * value + digit - 48) hds nextNonnegative as nextBound.
    change (decodeDigits digits (10 * value + digit - 48) < 2^64) in hBound.
    rewrite appendDigit_exact; [| exact hValue | exact hd | lia].
    change (decodeDigits (digit :: digits) value) with (decodeDigits digits (10 * value + digit - 48)).
    apply IH; try assumption; cbn [length] in hFuel; lia.
Qed.

Lemma readFirstExecution fuel digit digits tail separator s
  (hDigit : decimalDigit digit) :
  exec (@readFirst arrayIndex2 (arrayType _ environment2) (S fuel) 0 0)
    (withInput s ((digit :: digits) ++ separator :: tail)) =
  Some ((digit - 48, digit), withInput s (digits ++ separator :: tail)).
Proof.
  cbn [app]. rewrite readFirst_S, execChar, (digit_valid digit hDigit).
  rewrite appendDigit_exact; [| lia | exact hDigit | unfold decimalDigit in hDigit; lia].
  replace (10 * 0 + digit - 48) with (digit - 48) by lia. reflexivity.
Qed.

Lemma readUnsignedExecution digits separator tail s
  (hDigits : Forall decimalDigit digits) (hLength : (length digits <= 20)%nat)
  (hNonempty : digits <> []) (hBound : decodeDigits digits 0 < 2^64)
  (hSeparator : invalidDigit separator = true)
  (hMemory : (0 < length (memory s arraydef_0__input))%nat) :
  exec mappedReader (withInput s (digits ++ separator :: tail)) =
  Some (tt, withMemory (withInput s tail)
    (modifyArray (memory s) arraydef_0__input 0 (decodeDigits digits 0))).
Proof.
  rewrite mappedReaderNormalized. unfold readUnsignedAction.
  destruct digits as [| digit digits]; [contradiction |].
  inversion hDigits as [| d ds hd hds]; subst d ds.
  rewrite exec_bind, (readFirstExecution 19 digit digits tail separator s hd).
  cbn [optionBind fst snd]. rewrite exec_bind.
  rewrite readRestExecution; try assumption.
  - cbn [optionBind fst snd]. cbn [exec step].
    destruct (decide (Nat.lt (Z.to_nat 0) (length (memory (withInput s tail) arraydef_0__input)))) as [bound | bad].
    + cbn [optionBind fst snd]. replace (Z.to_nat 0) with 0%nat by reflexivity. reflexivity.
    + cbn [withInput memory] in bad. lia.
  - unfold decimalDigit in hd. lia.
Qed.

Lemma decimalReaderExecution value separator tail s
  (hValue : (value < 2^64)%nat)
  (hSeparator : invalidDigit separator = true)
  (hMemory : (0 < length (memory s arraydef_0__input))%nat) :
  exec mappedReader (withInput s (decimalBytes value ++ separator :: tail)) =
  Some (tt, withMemory (withInput s tail)
    (modifyArray (memory s) arraydef_0__input 0 (Z.of_nat value))).
Proof.
  rewrite readUnsignedExecution; try assumption.
  - rewrite decimalBytes_decode; [reflexivity | exact hValue].
  - apply decimalBytes_valid.
  - apply decimalBytes_length.
  - apply decimalBytes_nonempty. exact hValue.
  - rewrite decimalBytes_decode; [| exact hValue].
    assert (power : Z.of_nat (2^64)%nat = (2^64)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
    rewrite <- power. lia.
Qed.
