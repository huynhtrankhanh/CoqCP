From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import Coq.Logic.Eqdep_dec.
Require Import ZArith.
Require Import Coq.Strings.Ascii.
Open Scope Z_scope.

Record Environment := { arrayType: string -> Type; arrays: forall (name : string), list (arrayType name) }.

Record Locals := { numbers: string -> Z; booleans: string -> bool }.

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

Inductive WithArrays (arrayType : string -> Type) :=
| DoBasicEffect (effect : BasicEffect)
| Retrieve (arrayName : string) (index : Z)
| Store (arrayName : string) (index : Z) (value : arrayType arrayName).

#[export] Instance withArraysEqualityDecidable {arrayType} (hArrayType : forall name, EqDecision (arrayType name)) : EqDecision (WithArrays arrayType).
Proof.
  intros a b.
  destruct a as [e | a i | a i v]; destruct b as [e1 | a1 i1 | a1 i1 v1]; try ((left; easy) || (right; easy)).
  - destruct (decide (e = e1)) as [h | h]; try subst e1.
    { now left. } { right; intro x; now inversion x. }
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try now left.
    all: right; intro x; now inversion x.
  - destruct (decide (a = a1)) as [h | h]; try subst a1; destruct (decide (i = i1)) as [h1 | h1]; try subst i1; try (right; intro x; now inversion x).
    destruct (hArrayType a v v1) as [h | h]; try (subst v1; now left). right. intro x. inversion x as [x1]. apply inj_pair2_eq_dec in x1; try easy. solve_decision.
Qed.

Definition withArraysReturnValue {arrayType} (effect : WithArrays arrayType) : Type :=
  match effect with
  | DoBasicEffect _ effect => basicEffectReturnValue effect
  | Retrieve _ arrayName _ => arrayType arrayName
  | Store _ _ _ _ => unit
  end.

Inductive WithLocalVariables (arrayType : string -> Type) :=
| DoWithArrays (effect : WithArrays arrayType)
| BooleanLocalGet (name : string)
| BooleanLocalSet (name : string) (value : bool)
| NumberLocalGet (name : string)
| NumberLocalSet (name : string) (value : Z).

#[export] Instance withLocalVariablesEqualityDecidable {arrayType} (hArrayType : forall name, EqDecision (arrayType name)) : EqDecision (WithLocalVariables arrayType) := ltac:(solve_decision).

Definition withLocalVariablesReturnValue {arrayType} (effect : WithLocalVariables arrayType) : Type :=
  match effect with
  | DoWithArrays _ effect => withArraysReturnValue effect
  | BooleanLocalGet _ _ => bool
  | BooleanLocalSet _ _ _ => unit
  | NumberLocalGet _ _ => Z
  | NumberLocalSet _ _ _ => unit
  end.

Inductive LoopOutcome :=
| KeepGoing
| Stop.

Fixpoint loop (n : nat) { arrayType } (body : nat -> Action (WithLocalVariables arrayType) withLocalVariablesReturnValue LoopOutcome) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue unit :=
  match n with
  | O => Done _ _ unit tt
  | S n => bind (body n) (fun outcome => match outcome with
    | KeepGoing => loop n body
    | Stop => Done _ _ unit tt
    end)
  end.

Fixpoint loopString (s : string) { arrayType } (body : Z -> Action (WithLocalVariables arrayType) withLocalVariablesReturnValue LoopOutcome) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue unit :=
  match s with
  | EmptyString => Done _ _ unit tt
  | String x tail => bind (body (Z.of_N (N_of_ascii x))) (fun outcome =>
    match outcome with
    | KeepGoing => loopString tail body
    | Stop => Done _ _ unit tt
    end)
  end.

Definition update { A } (map : string -> A) (key : string) (value : A) := fun x => if decide (x = key) then value else map x.

Lemma eliminateLocalVariables { arrayType } (bools : string -> bool) (numbers : string -> Z) (action : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue unit) : Action (WithArrays arrayType) withArraysReturnValue unit.
Proof.
  induction action as [x | effect continuation IH] in bools, numbers |- *;
  [exact (Done _ _ _ x) |].
  destruct effect as [effect | name | name value | name | name value].
  - apply (Dispatch (WithArrays arrayType) withArraysReturnValue unit effect).
    simpl in IH, continuation. intro value. exact (IH value bools numbers).
  - simpl in IH, continuation. exact (IH (bools name) bools numbers).
  - simpl in IH, continuation. exact (IH tt (update bools name value) numbers).
  - simpl in IH, continuation. exact (IH (numbers name) bools numbers).
  - simpl in IH, continuation. exact (IH tt bools (update numbers name value)).
Defined.

Definition readChar arrayType := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue Z (DoWithArrays _(DoBasicEffect _ ReadChar)) (fun x => Done _ _ Z x).

Definition writeChar arrayType x := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (DoWithArrays _(DoBasicEffect _ (WriteChar x))) (fun x => Done _ _ _ x).

Definition flush arrayType := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (DoWithArrays _(DoBasicEffect _ Flush)) (fun x => Done _ _ _ x).

Definition trap arrayType returnType := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue returnType (DoWithArrays _ (DoBasicEffect _ Trap)) (fun x => False_rect _ x).

Definition booleanLocalSet arrayType name value := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (BooleanLocalSet _ name value) (fun x => Done _ _ _ x).

Definition booleanLocalGet arrayType name := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (BooleanLocalGet _ name) (fun x => Done _ _ _ x).

Definition numberLocalSet arrayType name value := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (NumberLocalSet _ name value) (fun x => Done _ _ _ x).

Definition numberLocalGet arrayType name := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (NumberLocalGet _ name) (fun x => Done _ _ _ x).

Definition retrieve arrayType name index := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (DoWithArrays _ (Retrieve arrayType name index)) (fun x => Done _ _ _ x).

Definition store arrayType name index (value : arrayType name) := Dispatch (WithLocalVariables arrayType) withLocalVariablesReturnValue _ (DoWithArrays _ (Store arrayType name index value)) (fun x => Done _ _ _ x).

Definition continue arrayType := Done (WithLocalVariables arrayType) withLocalVariablesReturnValue _ KeepGoing.

Definition break arrayType := Done (WithLocalVariables arrayType) withLocalVariablesReturnValue _ Stop.

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

Definition divIntUnsigned {arrayType} (a b : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayType Z else Done _ _ _ (a / b))).
Definition modIntUnsigned {arrayType} (a b : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayType Z else Done _ _ _ (a mod b))).

(* Arithmetic operations for 8-bit integers *)
Definition addInt8 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt8 (a + b)))).
Definition subInt8 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt8 (a - b)))).
Definition multInt8 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt8 (a * b)))).
Definition divInt8Signed {arrayType} (a b : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayType Z else if decide (toSigned8 a = -128 /\ toSigned8 b = -1) then trap arrayType Z else Done _ _ _ (coerceInt8 (a / b)))).

(* Arithmetic operations for 16-bit integers *)
Definition addInt16 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt16 (a + b)))).
Definition subInt16 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt16 (a - b)))).
Definition multInt16 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt16 (a * b)))).
Definition divInt16Signed {arrayType} (a b : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayType Z else if decide (toSigned16 a = -32768 /\ toSigned16 b = -1) then trap arrayType Z else Done _ _ _ (coerceInt16 (a / b)))).

(* Arithmetic operations for 32-bit integers *)
Definition addInt32 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt32 (a + b)))).
Definition subInt32 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt32 (a - b)))).
Definition multInt32 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt32 (a * b)))).
Definition divInt32Signed {arrayType} (a b : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayType Z else if decide (toSigned32 a = -2147483648 /\ toSigned32 b = -1) then trap arrayType Z else Done _ _ _ (coerceInt32 (a / b)))).

(* Arithmetic operations for 64-bit integers *)
Definition addInt64 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt64 (a + b)))).
Definition subInt64 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt64 (a - b)))).
Definition multInt64 {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (coerceInt64 (a * b)))).
Definition divInt64Signed {arrayType} (a b : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z := bind a (fun a => bind b (fun b => if decide (b = 0) then trap arrayType Z else if decide (toSigned64 a = -9223372036854775808 /\ toSigned64 b = -1) then trap arrayType Z else Done _ _ _ (coerceInt64 (a / b)))).

(* Bitwise operations for any bit width *)
Definition andBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.land a b))).
Definition orBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.lor a b))).
Definition xorBits {u v} (a b : Action u v Z) : Action u v Z := bind a (fun a => bind b (fun b => Done _ _ _ (Z.lxor a b))).

(* Operations for specified bit width *)
Definition shiftLeft {arrayType} (bitWidth : Z) (a amount : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind amount (fun amount =>
    if decide (amount >= bitWidth) then trap _ Z else Done _ _ _ (Z.land (Z.shiftl a amount) (Z.ones bitWidth))
  )).

Definition shiftRight {arrayType} (bitWidth : Z) (a amount : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue Z :=
  bind a (fun a => bind amount (fun amount =>
    if decide (amount >= bitWidth) then trap _ Z else Done _ _ _ (Z.land (Z.shiftr a amount) (Z.ones bitWidth))
  )).

Definition notBits {u v} (bitWidth : Z) (a : Action u v Z) : Action u v Z := bind a (fun a => Done _ _ _ (Z.land (Z.lnot a) (Z.ones bitWidth))).

Definition coerceBool {u v} (a : Action u v bool) : Action u v Z := bind a (fun a =>
  if a then Done _ _ _ 1 else Done _ _ _ 0
).

Fixpoint liftToWithLocalVariables {arrayType r} (x : Action (WithArrays arrayType) withArraysReturnValue r) : Action (WithLocalVariables arrayType) withLocalVariablesReturnValue r :=
  match x with
  | Done _ _ _ x => Done _ _ _ x
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ (DoWithArrays _ effect) (fun x => liftToWithLocalVariables (continuation x))
  end.
