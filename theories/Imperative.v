From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import Coq.Logic.Eqdep_dec.
Require Import ZArith.
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

Definition shortCircuitAnd effectType effectResponse (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | false => Done _ _ _ false
  | true => b
  end).

Definition shortCircuitOr effectType effectResponse (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
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
