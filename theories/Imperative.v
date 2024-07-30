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
| WriteChar (value : Z).

#[export] Instance basicEffectEqualityDecidable : EqDecision BasicEffect := ltac:(solve_decision).

Definition basicEffectReturnValue (effect : BasicEffect): Type :=
  match effect with
  | Trap => False
  | Flush => unit
  | ReadChar => Z
  | WriteChar _ => unit
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
| NumberLocalSet (name : variableIndex) (value : Z).

#[export] Instance withLocalVariablesEqualityDecidable {arrayIndex arrayType variableIndex} (hArrayIndex : EqDecision arrayIndex) (hArrayType : forall name, EqDecision (arrayType name)) (hVariableIndex : EqDecision variableIndex) : EqDecision (WithLocalVariables arrayIndex arrayType variableIndex) := ltac:(solve_decision).

Definition withLocalVariablesReturnValue {arrayIndex arrayType variableIndex} (effect : WithLocalVariables arrayIndex arrayType variableIndex) : Type :=
  match effect with
  | DoWithArrays _ _ _ effect => withArraysReturnValue effect
  | BooleanLocalGet _ _ _ _ => bool
  | BooleanLocalSet _ _ _ _ _ => unit
  | NumberLocalGet _ _ _ _ => Z
  | NumberLocalSet _ _ _ _ _ => unit
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

Lemma eliminateLocalVariables {arrayIndex arrayType variableIndex} `{EqDecision variableIndex} (bools : variableIndex -> bool) (numbers : variableIndex -> Z) (action : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue unit) : Action (WithArrays arrayIndex arrayType) withArraysReturnValue unit.
Proof.
  induction action as [x | effect continuation IH] in bools, numbers |- *;
  [exact (Done _ _ _ x) |].
  destruct effect as [effect | name | name value | name | name value].
  - apply (Dispatch (WithArrays arrayIndex arrayType) withArraysReturnValue unit effect).
    simpl in IH, continuation. intro value. exact (IH value bools numbers).
  - simpl in IH, continuation. exact (IH (bools name) bools numbers).
  - simpl in IH, continuation. exact (IH tt (update bools name value) numbers).
  - simpl in IH, continuation. exact (IH (numbers name) bools numbers).
  - simpl in IH, continuation. exact (IH tt bools (update numbers name value)).
Defined.

Definition readChar arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z (DoWithArrays _ _ _ (DoBasicEffect _ _ ReadChar)) (fun x => Done _ _ Z x).

Definition writeChar arrayIndex arrayType variableIndex x := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ (WriteChar x))) (fun x => Done _ _ _ x).

Definition flush arrayIndex arrayType variableIndex := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (DoBasicEffect _ _ Flush)) (fun x => Done _ _ _ x).

Definition trap arrayIndex arrayType variableIndex returnType := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue returnType (DoWithArrays _ _ _ (DoBasicEffect _ _ Trap)) (fun x => False_rect _ x).

Definition booleanLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition booleanLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (BooleanLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition numberLocalSet arrayIndex arrayType variableIndex name value := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalSet _ _ _ name value) (fun x => Done _ _ _ x).

Definition numberLocalGet arrayIndex arrayType variableIndex name := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (NumberLocalGet _ _ _ name) (fun x => Done _ _ _ x).

Definition retrieve arrayIndex arrayType variableIndex name index := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Retrieve arrayIndex arrayType name index)) (fun x => Done _ _ _ x).

Definition store arrayIndex arrayType variableIndex name index (value : arrayType name) := Dispatch (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue _ (DoWithArrays _ _ _ (Store _ _ name index value)) (fun x => Done _ _ _ x).

Definition continue arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoContinue _ _ _) (fun x => Done _ _ _ tt).

Definition break arrayIndex arrayType variableIndex := Dispatch (WithinLoop arrayIndex arrayType variableIndex) withinLoopReturnValue () (DoBreak _ _ _) (fun x => Done _ _ _ tt).

(* Coercion functions *)
Definition coerceInt8 (n : Z) : Z := n mod 256.
Definition coerceInt16 (n : Z) : Z := n mod 65536.
Definition coerceInt32 (n : Z) : Z := n mod 4294967296.
Definition coerceInt64 (n : Z) : Z := n mod 18446744073709551616.

(* Helper functions for signed conversion *)
Definition toSigned8 (n : Z) : Z :=
  if decide (n < 128) then n else n - 256.

Definition toSigned16 (n : Z) : Z :=
  if decide (n < 32768) then n else n - 65536.

Definition toSigned32 (n : Z) : Z :=
  if decide (n < 2147483648) then n else n - 4294967296.

Definition toSigned64 (n : Z) : Z :=
  if decide (n < 9223372036854775808) then n else n - 18446744073709551616.

Definition divIntUnsigned {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (a / b))).
Definition modIntUnsigned {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (a mod b))).

(* Arithmetic operations for 8-bit integers *)
Definition addInt8 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt8 (a + b)))).
Definition subInt8 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt8 (a - b)))).
Definition multInt8 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt8 (a * b)))).
Definition divInt8Signed {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else if decide (toSigned8 a = -128 /\ toSigned8 b = -1) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (coerceInt8 (a / b)))).

(* Arithmetic operations for 16-bit integers *)
Definition addInt16 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt16 (a + b)))).
Definition subInt16 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt16 (a - b)))).
Definition multInt16 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt16 (a * b)))).
Definition divInt16Signed {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else if decide (toSigned16 a = -32768 /\ toSigned16 b = -1) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (coerceInt16 (a / b)))).

(* Arithmetic operations for 32-bit integers *)
Definition addInt32 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt32 (a + b)))).
Definition subInt32 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt32 (a - b)))).
Definition multInt32 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt32 (a * b)))).
Definition divInt32Signed {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else if decide (toSigned32 a = -2147483648 /\ toSigned32 b = -1) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (coerceInt32 (a / b)))).

(* Arithmetic operations for 64-bit integers *)
Definition addInt64 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt64 (a + b)))).
Definition subInt64 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt64 (a - b)))).
Definition multInt64 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt64 (a * b)))).
Definition divInt64Signed {arrayIndex arrayType variableIndex} (a b : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayIndex arrayType variableIndex) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayIndex arrayType variableIndex Z else if decide (toSigned64 a = -9223372036854775808 /\ toSigned64 b = -1) then trap arrayIndex arrayType variableIndex Z else Done _ _ _ (coerceInt64 (a / b)))).

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
    + destruct effect as [| | | x].
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Trap) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ Flush) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ ReadChar) (fun returnValue => IH returnValue captured)).
      * exact (Dispatch _ _ _ (DoBasicEffect _ _ (WriteChar x)) (fun returnValue => IH returnValue (captured ++ [x]))).
    + exact (Dispatch _ _ _ (Retrieve _ arrayType arrayName index) (fun x => IH x captured)).
    + exact (Dispatch _ _ _ (Store _ arrayType arrayName index value) (fun x => IH x captured)).
Defined.
