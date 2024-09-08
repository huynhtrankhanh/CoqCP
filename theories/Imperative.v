From CoqCP Require Import Options.
From stdpp Require Import strings.
Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import ZArith.
Require Import Coq.Strings.Ascii.
Open Scope Z_scope.

Record Environment (arrayIndex : Type) := { arrayType: arrayIndex -> Type; arrays: forall (name : arrayIndex), list (arrayType name) }.

Record Locals (variableIndex : Type) := { numbers: variableIndex -> Z; booleans: variableIndex -> bool }.

Inductive Action (effectType : Type) (effectResponse : effectType -> Type) (returnType : Type) :=
| Done (returnValue : returnType)
| Dispatch (effect : effectType) (continuation : effectResponse effect -> Action effectType effectResponse returnType).

Fixpoint identical {effectType effectResponse returnType} (a b : Action effectType effectResponse returnType) : Prop.
Proof.
  case a as [returnValue | effect continuation].
  - case b as [returnValue2 |].
    + exact (returnValue = returnValue2).
    + exact False.
  - case b as [| effect2 continuation2].
    + exact False.
    + pose proof (ltac:(intro hEffect; subst effect; exact (forall response, identical _ _ _ (continuation response) (continuation2 response))) : effect = effect2 -> Prop) as rhs.
      exact (effect = effect2 /\ forall x: effect = effect2, rhs x).
Defined.

Fixpoint bind {effectType effectResponse A B} (a : Action effectType effectResponse A) (f : A -> Action effectType effectResponse B) : Action effectType effectResponse B :=
  match a with
  | Done _ _ _ value => f value
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ effect (fun response => bind (continuation response) f)
  end.

Notation "x >>= f" := (bind x f) (at level 50, left associativity).

Lemma identicalSelf {effectType effectResponse A} (a : Action effectType effectResponse A) (hEffectType : EqDecision effectType) : identical a a.
Proof.
  induction a as [| effect continuation IH]; simpl; try easy. split; try easy. intro no. unfold eq_rect_r. now rewrite <- (eq_rect_eq_dec hEffectType).
Qed.

Lemma leftIdentity {effectType effectResponse A B} (x : A) (f : A -> Action effectType effectResponse B) : bind (Done _ _ _ x) f = f x.
Proof. easy. Qed.

Lemma rightIdentity {effectType effectResponse A} (x : Action effectType effectResponse A) (hEffectType : EqDecision effectType) : identical (bind x (Done _ _ _)) x.
Proof.
  induction x as [| a next IH]; try easy; simpl.
  split; try easy. intros no. unfold eq_rect_r. rewrite <- (eq_rect_eq_dec hEffectType).
  intros h. exact (IH h).
Qed.

Lemma assoc {effectType effectResponse A B C} (x : Action effectType effectResponse A) (hEffectType : EqDecision effectType) (f : A -> Action effectType effectResponse B) (g : B -> Action effectType effectResponse C) : identical (bind x (fun x => bind (f x) g)) (bind (bind x f) g).
Proof.
  induction x as [| a next IH]; try easy; simpl.
  - now apply identicalSelf.
  - split; try easy. intros no. unfold eq_rect_r. rewrite <- (eq_rect_eq_dec hEffectType). intros h. exact (IH h).
Qed.

Definition shortCircuitAnd {effectType effectResponse} (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | false => Done _ _ _ false
  | true => b
  end).

Definition shortCircuitOr {effectType effectResponse} (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | true => Done _ _ _ true
  | false => b
  end).

Inductive BasicEffect :=
| Trap
| Flush
| ReadChar
| WriteChar (value : Z)
| Donate (money : Z) (address : list Z)
| Invoke (money : Z) (address : list Z) (array : list Z)
| GetSender
| GetMoney
| GetCommunicationSize
| ReadByte (index : Z)
| SetByte (index value : Z).

#[export] Instance basicEffectEqualityDecidable : EqDecision BasicEffect := ltac:(solve_decision).

Definition basicEffectReturnValue (effect : BasicEffect): Type :=
  match effect with
  | Trap => False
  | Flush => unit
  | ReadChar => Z
  | WriteChar _ => unit
  | Donate _ _ => unit
  | Invoke _ _ _ => list Z
  | GetSender => list Z
  | GetMoney => Z
  | GetCommunicationSize => Z
  | ReadByte _ => Z
  | SetByte _ _ => unit
  end.

Inductive WithArrays (arrayIndex : Type) (arrayType : arrayIndex -> Type) :=
| DoBasicEffect (effect : BasicEffect)
| Retrieve (arrayName : arrayIndex) (index : Z)
| Store (arrayName : arrayIndex) (index : Z) (value : arrayType arrayName).

#[export] Instance withArraysEqualityDecidable {arrayIndex : Type} {arrayType : arrayIndex -> Type} (hIndexEq : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) : EqDecision (WithArrays arrayIndex arrayType).
Proof.
  intros a b.
  destruct a as [e | a i | a i v]; destruct b as [e1 | a1 i1 | a1 i1 v1]; try ((left; easy) || (right; easy)).
  - destruct (decide (e = e1)) as [h | h]; try subst e1.
    { now left. } { right; intro x; now inversion x. }
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try now left.
    all: right; intro x; now inversion x.
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try (right; intro x; now inversion x).
    destruct (hArrayType a v v1) as [h | h]; try (subst v1; now left). right. intro x. inversion x as [x1]. apply inj_pair2_eq_dec in x1; try easy.
Qed.

Definition withArraysReturnValue {arrayIndex} {arrayType : arrayIndex -> Type} (effect : WithArrays arrayIndex arrayType) : Type :=
  match effect with
  | DoBasicEffect _ _ effect => basicEffectReturnValue effect
  | Retrieve _ _ arrayName _ => arrayType arrayName
  | Store _ _ _ _ _ => unit
  end.

Inductive WithLocalVariables (arrayIndex : Type) (arrayType : arrayIndex -> Type) (variableIndex : Type) :=
| DoWithArrays (effect : WithArrays arrayIndex arrayType)
| BooleanLocalGet (name : variableIndex)
| BooleanLocalSet (name : variableIndex) (value : bool)
| NumberLocalGet (name : variableIndex)
| NumberLocalSet (name : variableIndex) (value : Z)
| AddressLocalGet (name : variableIndex)
| AddressLocalSet (name : variableIndex) (value : list Z).

#[export] Instance withLocalVariablesEqualityDecidable {arrayIndex arrayType variableIndex} (hArrayIndex : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) (hVariableIndex : EqDecision variableIndex) : EqDecision (WithLocalVariables arrayIndex arrayType variableIndex) := ltac:(solve_decision).

Definition withLocalVariablesReturnValue {arrayIndex arrayType variableIndex} (effect : WithLocalVariables arrayIndex arrayType variableIndex) : Type :=
  match effect with
  | DoWithArrays _ _ _ effect => withArraysReturnValue effect
  | BooleanLocalGet _ _ _ _ => bool
  | BooleanLocalSet _ _ _ _ _ => unit
  | NumberLocalGet _ _ _ _ => Z
  | NumberLocalSet _ _ _ _ _ => unit
  | AddressLocalGet _ _ _ _ => list Z
  | AddressLocalSet _ _ _ _ _ => unit
  end.

Inductive LoopOutcome :=
| KeepGoing
| Stop.

Inductive WithinLoop arrayIndex arrayType variableIndex :=
| DoWithLocalVariables (effect : WithLocalVariables arrayIndex arrayType variableIndex)
| DoContinue
| DoBreak.

#[export] Instance withinLoopEqualityDecidable {arrayIndex arrayType variableIndex} (hArrayType : forall name, EqDecision (arrayType name)) (hArrayIndex : EqDecision arrayIndex) (hVariableIndex : EqDecision variableIndex): EqDecision (WithinLoop arrayIndex arrayType variableIndex) := ltac:(solve_decision).

Definition withinLoopReturnValue {arrayIndex arrayType variableIndex} (effect : WithinLoop arrayIndex arrayType variableIndex) : Type :=
  match effect with
  | DoWithLocalVariables _ _ _ effect => withLocalVariablesReturnValue effect
  | DoContinue _ _ _ => false
  | DoBreak _ _ _ => false
  end.

Lemma dropWithinLoop {arrayIndex arrayType variableIndex} (action : Action (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue ()) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome.
Proof.
  induction action as [| effect continuation IH].
  - exact (Done _ _ _ KeepGoing).
  - destruct effect as [effect | |].
    + exact (Dispatch _ _ _ effect IH).
    + exact (Done _ _ _ KeepGoing).
    + exact (Done _ _ _ Stop).
Defined.

Fixpoint loop (n : nat) {arrayIndex arrayType variableIndex} (body : nat -> Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit :=
  match n with
  | O => Done _ _ unit tt
  | S n => bind (body n) (fun outcome => match outcome with
    | KeepGoing => loop n body
    | Stop => Done _ _ unit tt
    end)
  end.

Fixpoint loopString (s : string) {arrayIndex arrayType variableIndex} (body : Z -> Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue LoopOutcome) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit :=
  match s with
  | EmptyString => Done _ _ unit tt
  | String x tail => bind (body (Z.of_N (N_of_ascii x))) (fun outcome =>
    match outcome with
    | KeepGoing => loopString tail body
    | Stop => Done _ _ unit tt
    end)
  end.

Definition update {indexType : Type} {A} (map : indexType -> A) (key : indexType) (value : A) `{EqDecision indexType} := fun x => if decide (x = key) then value else map x.

Lemma eliminateLocalVariables {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (addresses : variableIndex -> list Z) (action : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit.
Proof.
  induction action as [x | effect continuation IH] in bools, numbers, addresses |- *;
  [exact (Done _ _ _ x) |].
  destruct effect as [effect | name | name value | name | name value | name | name value].
  - apply (Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue unit effect).
    simpl in IH, continuation. intro value. exact (IH value bools numbers addresses).
  - simpl in IH, continuation. exact (IH (bools name) bools numbers addresses).
  - simpl in IH, continuation. exact (IH tt (update bools name value) numbers addresses).
  - simpl in IH, continuation. exact (IH (numbers name) bools numbers addresses).
  - simpl in IH, continuation. exact (IH tt bools (update numbers name value) addresses).
  - simpl in IH, continuation. exact (IH (addresses name) bools numbers addresses).
  - simpl in IH, continuation. exact (IH tt bools numbers (update addresses name value)).
Defined.

Definition readChar arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z (DoWithArrays _ _ _ (DoBasicEffect _ _ ReadChar)) (fun x => Done _ _ Z x).

Definition writeChar arrayIndex arrayType variableIndex x := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (WriteChar x))) (fun x => Done _ _ _ x).

Definition flush arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ Flush)) (fun x => Done _ _ _ x).

Definition trap arrayIndex arrayType variableIndex returnType := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue returnType (DoWithArrays _ _ _ (DoBasicEffect _ _ Trap)) (fun x => False_rect _ x).

Definition readByte arrayIndex arrayType variableIndex index := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (ReadByte index))) (fun x => Done _ _ _ x).

Definition setByte arrayIndex arrayType variableIndex index value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (SetByte index value))) (fun x => Done _ _ _ x).

Definition getSender arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ GetSender)) (fun x => Done _ _ _ x).

Definition getMoney arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ GetMoney)) (fun x => Done _ _ _ x).

Definition getCommunicationSize arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ GetCommunicationSize)) (fun x => Done _ _ _ x).

Definition donate arrayIndex arrayType variableIndex money address := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (Donate money address))) (fun x => Done _ _ _ x).

Definition invoke arrayIndex arrayType variableIndex money address array := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (Invoke money address array))) (fun x => Done _ _ _ x).

Definition booleanLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition booleanLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition addressLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (AddressLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition addressLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (AddressLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition numberLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition numberLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition retrieve arrayIndex arrayType variableIndex name index := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Retrieve arrayIndex arrayType name index)) (fun x => Done _ _ _ x).

Definition store arrayIndex arrayType variableIndex name index (value : arrayType name) := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Store _ _ name index value)) (fun x => Done _ _ _ x).

Definition continue arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoContinue _ _ _) (fun x => Done _ _ _ tt).

Definition break arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoBreak _ _ _) (fun x => Done _ _ _ tt).

Definition divIntUnsigned {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (a / b))).
Definition modIntUnsigned {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (a mod b))).

(* Bitwise operations for any bit width *)
Definition andBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.land a b))).
Definition orBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.lor a b))).
Definition xorBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.lxor a b))).

(* Operations for specified bit width *)
Definition shiftLeft {arrayIndex arrayType variableIndex} (bitWidth : Z) (a amount : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind amount (fun amount =>
    if decide (amount >= bitWidth) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (Z.land (Z.shiftl a amount) (Z.ones bitWidth))
  )).

Definition shiftRight {arrayIndex arrayType variableIndex} (bitWidth : Z) (a amount : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind amount (fun amount =>
    if decide (amount >= bitWidth) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (Z.land (Z.shiftr a amount) (Z.ones bitWidth))
  )).

Definition notBits {u v} (bitWidth : Z) (a : Action u v Z) : Action u v Z := bind a (fun a => Done _ _ _ (Z.land (Z.lnot a) (Z.ones bitWidth))).

Definition coerceBool {u v} (a : Action u v bool) : Action u v Z := bind a (fun a =>
  if a then Done _ _ _ 1 else Done _ _ _ 0
).

(* Generic coercion function based on bit width *)
Definition coerceInt (n bitWidth : Z) : Z :=
  n mod (2 ^ bitWidth).

(* Helper function for signed conversion based on bit width *)
Definition toSigned (n bitWidth : Z) : Z :=
  let half := 2 ^ (bitWidth - 1) in
  if decide (n < half) then n else n - 2 ^ bitWidth.

(* Generic arithmetic operations *)
Definition addInt {u v} (bitWidth : Z) (a b : Action u v Z) : Action u v Z :=
  bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt (a + b) bitWidth))).

Definition subInt {u v} (bitWidth : Z) (a b : Action u v Z) : Action u v Z :=
  bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt (a - b) bitWidth))).

Definition multInt {u v} (bitWidth : Z) (a b : Action u v Z) : Action u v Z :=
  bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt (a * b) bitWidth))).

Definition divIntSigned {arrayIndex arrayType variableIndex} (bitWidth : Z) (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind b (fun b =>
    let signedA := toSigned a bitWidth in
    let signedB := toSigned b bitWidth in
    if decide (b = 0) then trap arrayIndex arrayType variableIndex Z
    else if decide (signedA = - (2 ^ (bitWidth - 1)) /\ signedB = -1) then trap arrayIndex arrayType variableIndex Z
    else Done _ _ _ (coerceInt (a / b) bitWidth))).

Fixpoint liftToWithLocalVariables {arrayIndex arrayType variableIndex r} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue r) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r :=
  match x with
  | Done _ _ _ x => Done _ _ _ x
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ (DoWithArrays _ _ _ effect) (fun x => liftToWithLocalVariables (continuation x))
  end.

Fixpoint liftToWithinLoop {arrayIndex arrayType variableIndex r} (x : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue r) : Action (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue r :=
  match x with
  | Done _ _ _ x => Done _ _ _ x
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ (DoWithLocalVariables _ _ _ effect) (fun x => liftToWithinLoop (continuation x))
  end.

Lemma nth_lt {A} (l : list A) (n : nat) (isLess : Nat.lt n (length l)) : A.
Proof.
  destruct l as [| head tail]; simpl in *; (lia || exact (nth n (head :: tail) head)).
Defined.

Lemma nthTrap {A arrayIndex arrayType variableIndex} (l : list A) (n : Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue A.
Proof.
  destruct (decide (Nat.lt (Z.to_nat n) (length l))) as [h |].
  - exact (Done _ _ _ (nth_lt l (Z.to_nat n) h)).
  - exact (trap _ _ _ _).
Defined.

Fixpoint getArray {arrayIndex} {arrayType : arrayIndex -> Type} {variableIndex} (arrayName : arrayIndex) (length : nat) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue (list (arrayType arrayName)) :=
  match length with
  | O => Done _ _ _ []
  | S length => retrieve _ _ _ arrayName (Z.of_nat length) >>= fun x => getArray arrayName length >>= fun y => Done _ _ _ (y ++ [x])
  end.

Fixpoint applyArray {arrayIndex} {arrayType : arrayIndex -> Type} {variableIndex} (arrayName : arrayIndex) (l : list (arrayType arrayName)) (startIndex : Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue () :=
  match l with
  | [] => Done _ _ _ tt
  | head :: tail => store _ _ _ arrayName startIndex head >>= fun x => applyArray arrayName tail (startIndex + 1)
  end.

Definition invokeWithArrays {arrayIndex} {arrayType : arrayIndex -> Type} {variableIndex} (money : Z) (address : list Z) (arrayName : arrayIndex) (length : Z) (hEq : arrayType arrayName = Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue () := getArray arrayName (Z.to_nat length) >>= fun array => invoke arrayIndex arrayType variableIndex money address ltac:(rewrite hEq in *; exact array) >>= fun array => applyArray arrayName ltac:(rewrite hEq in *; exact array) 0.

Lemma getNewArrays {arrayIndex arrayType} `{EqDecision arrayIndex} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (arrays : forall x, list (arrayType x)) : (Action BasicEffect basicEffectReturnValue (forall x, list (arrayType x))).
Proof.
  induction x as [x | effect continuation IH] in arrays |- *.
  - exact (Done _ _ _ arrays).
  - destruct effect as [effect | arrayName index | arrayName index value].
    + exact (Dispatch _ _ _ effect (fun x => (IH ltac:(simpl in *; exact x) arrays))).
    + destruct (decide (Nat.lt (Z.to_nat index) (length (arrays arrayName)))) as [H | H].
      * exact (IH ltac:(simpl in *; exact (nth_lt (arrays arrayName) (Z.to_nat index) H)) arrays).
      * exact (Dispatch _ _ _ Trap (fun _ => Done _ _ _ arrays)).
    + destruct (decide (Nat.lt (Z.to_nat index) (length (arrays arrayName)))) as [H | H].
      * exact (IH tt (fun name => ltac:(destruct (decide (name = arrayName)) as [H' |]; [subst arrayName; exact (<[(Z.to_nat index):=value]>(arrays name)) | exact (arrays name)]))).
      * exact (Dispatch _ _ _ Trap (fun _ => Done _ _ _ arrays)).
Defined.

Lemma withArraysReturnValueDoBasicEffectArrayType arrayIndex1 arrayIndex2 arrayType1 arrayType2 (effect : BasicEffect) : withArraysReturnValue (DoBasicEffect arrayIndex1 arrayType1 effect) = withArraysReturnValue (DoBasicEffect arrayIndex2 arrayType2 effect).
Proof. auto. Qed.

Lemma translateArrays {arrayIndex1 arrayIndex2 arrayType} (x : Action (WithArrays arrayIndex1 arrayType) withArraysReturnValue ()) (destinationArrayType : arrayIndex2 -> Type) (mapping : arrayIndex1 -> arrayIndex2) (hCongruent : forall x, arrayType x = destinationArrayType (mapping x)) : Action (WithArrays arrayIndex2 destinationArrayType) withArraysReturnValue ().
Proof.
  induction x as [x | effect continuation IH].
  - exact (Done _ _ _ tt).
  - destruct effect as [effect | arrayName index | arrayName index value].
    + rewrite (withArraysReturnValueDoBasicEffectArrayType arrayIndex1 arrayIndex2 arrayType destinationArrayType) in IH. exact (Dispatch _ _ _ (DoBasicEffect _ destinationArrayType effect) IH).
    + assert (h : withArraysReturnValue (Retrieve arrayIndex1 arrayType arrayName index) = withArraysReturnValue (Retrieve arrayIndex2 destinationArrayType (mapping arrayName) index)). { simpl; auto. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Retrieve _ destinationArrayType (mapping arrayName) index) IH).
    + assert (h : withArraysReturnValue (Store arrayIndex1 arrayType arrayName index value) = withArraysReturnValue (Store _ destinationArrayType (mapping arrayName) index ltac:(rewrite <- hCongruent; exact value))). { simpl; auto. }
      rewrite h in IH.
      exact (Dispatch _ _ _ (Store _ destinationArrayType (mapping arrayName) index ltac:(rewrite <- hCongruent; exact value)) IH).
Defined.

Lemma modifyArray {arrayIndex} `{EqDecision arrayIndex} {arrayType : arrayIndex -> Type} (arrays : forall x, list (arrayType x)) (toBeModified : arrayIndex) (index : nat) (value : arrayType toBeModified) : forall x, list (arrayType x).
Proof.
  intro arrayName.
  destruct (decide (arrayName = toBeModified)) as [H | H].
  - rewrite <- H in value.
    exact (<[index:=value]>(arrays arrayName)).
  - exact (arrays arrayName).
Defined.

Lemma getAllCharacters {arrayIndex arrayType} (x : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (captured : list Z) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue (list Z).
Proof.
  induction x as [x | effect continuation IH] in captured |- *.
  - exact (Done _ _ _ captured).
  - destruct effect as [effect | arrayName index | arrayName index value].
    + destruct effect as [| | | x | | | | | | |].
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Flush) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar x)) (fun returnValue => IH returnValue (captured ++ [x]))).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => Done _ _ _ captured)).
    + exact (Dispatch _ _ _ (Retrieve _ arrayType arrayName index) (fun x => IH x captured)).
    + exact (Dispatch _ _ _ (Store _ arrayType arrayName index value) (fun x => IH x captured)).
Defined.

Inductive BlockchainAccount :=
| ExternallyOwned (money : Z)
| BlockchainContract (arrayIndex : Type) (arrayIndexEqualityDecidable : EqDecision arrayIndex) (arrayType : arrayIndex -> Type) (arrays : forall (name : arrayIndex), list (arrayType name)) (money : Z) (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()).

Definition BlockchainState := list Z -> BlockchainAccount.

Definition getBalance (x : BlockchainAccount) : Z :=
  match x with
  | ExternallyOwned money => money
  | BlockchainContract _ _ _ _ balance _ => balance
  end.

Definition updateBalance (x : BlockchainAccount) (newBalance : Z) : BlockchainAccount :=
  match x with
  | ExternallyOwned _ => ExternallyOwned newBalance
  | BlockchainContract a b c d _ e => BlockchainContract a b c d newBalance e
  end.

Definition transferMoney (state : BlockchainState) (sender target : list Z) (money : Z) :=
  let intermediateState := update state sender (updateBalance (state sender) (getBalance (state sender) - money)) in
  update intermediateState target (updateBalance (state target) (getBalance (state target) + money)).

(* this assumes the money has already been transferred before the contract gets invoked *)
(* so initially this function doesn't deduct the balance of the sender and credit the balance of the target *)
(* revertTo: state before the money transfer and the subsequent contract invocation, state: current state *)
Fixpoint invokeContractAux (sender target : list Z) (money : Z) (revertTo state : BlockchainState) (communication : list Z) (fuel : nat) : option (list Z * BlockchainState) :=
  match fuel with
  | O => None
  | S fuel => match (state target) with
    | ExternallyOwned money => Some ([], state)
    | BlockchainContract arrayIndex arrayIndexEqualityDecidable arrayType arrays money originalCode =>
      (fix inner (code : Action (WithArrays arrayIndex arrayType) withArraysReturnValue ()) (communication : list Z) (arrays : forall (name : arrayIndex), list (arrayType name)) (state : BlockchainState) :=
        match code with
        | Done _ _ _ _ => Some (communication, update state target (BlockchainContract arrayIndex _ arrayType arrays (getBalance (state target)) originalCode))
        | Dispatch _ _ _ (Retrieve _ _ arrayName index) continuation =>
          match decide (Nat.lt (Z.to_nat index) (length (arrays arrayName))) with
          | left h => inner (continuation (nth_lt (arrays arrayName) (Z.to_nat index) h)) communication arrays state
          | right _ => Some ([], revertTo)
          end
        | Dispatch _ _ _ (Store _ _ arrayName index value) continuation =>
          match decide (Nat.lt (Z.to_nat index) (length (arrays arrayName))) with
          | left h => inner (continuation tt) communication (fun currentName =>
            match decide (currentName = arrayName) with
            | left h => ltac:(rewrite h; exact (<[Z.to_nat index := value]> (arrays arrayName)))
            | right _ => arrays currentName
            end) state
          | right _ => Some ([], revertTo)
          end
          | Dispatch _ _ _ (DoBasicEffect _ _ Trap) continuation => Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ Flush) continuation => Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) continuation => Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar _)) continuation => Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ (Donate money address)) continuation =>
            if decide (money <= getBalance (state target) /\ 0 <= money /\ money < 2^256) then
              inner (continuation tt) communication arrays (transferMoney state target address money)
            else Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ (Invoke money address passedArray)) continuation =>
            if decide (money <= getBalance (state target) /\ 0 <= money /\ money < 2^256) then
              let alteredState := update state target (BlockchainContract arrayIndex _ arrayType arrays (getBalance (state target)) originalCode) in
              match invokeContractAux target address money alteredState (transferMoney alteredState target address money) passedArray fuel with
              | None => None
              | Some (newArray, newState) => inner (continuation newArray) communication arrays newState
              end
            else Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ GetSender) continuation => inner (continuation sender) communication arrays state
          | Dispatch _ _ _ (DoBasicEffect _ _ GetMoney) continuation => inner (continuation money) communication arrays state
          | Dispatch _ _ _ (DoBasicEffect _ _ GetCommunicationSize) continuation => inner (continuation (Z.of_nat (length communication))) communication arrays state
          | Dispatch _ _ _ (DoBasicEffect _ _ (ReadByte index)) continuation =>
            if decide (Nat.lt (Z.to_nat index) (length communication)) then
              inner (continuation (nth (Z.to_nat index) communication 0)) communication arrays state
            else Some ([], revertTo)
          | Dispatch _ _ _ (DoBasicEffect _ _ (SetByte index value)) continuation =>
            if decide (Nat.lt (Z.to_nat index) (length communication)) then
              inner (continuation tt) (<[Z.to_nat index := value]> communication) arrays state
            else Some ([], revertTo)
          end) originalCode communication arrays state
    end
  end.
