From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ZArith.
Open Scope Z_scope.

Record Environment := { arrayType: string -> Type; arrays: forall (name : string), list (arrayType name) }.

Record Locals := { numbers: string -> Z; booleans: string -> bool }.

Inductive Action (effectType : Type) (effectResponse : effectType -> Type) (returnType : Type) :=
| Done (returnValue : returnType)
| Dispatch (effect : effectType) (continuation : effectResponse effect -> Action effectType effectResponse returnType).

Fixpoint bind {effectType effectResponse A B} (a : Action effectType effectResponse A) (f : A -> Action effectType effectResponse B) : Action effectType effectResponse B :=
  match a with
  | Done _ _ _ value => f value
  | Dispatch _ _ _ effect continuation => Dispatch _ _ _ effect (fun response => bind (continuation response) f)
  end.

Lemma leftIdentity {effectType effectResponse A B} (x : A) (f : A -> Action effectType effectResponse B) : bind (Done _ _ _ x) f = f x.
Proof. easy. Qed.

Lemma rightIdentity {effectType effectResponse A} (x : Action effectType effectResponse A) : bind x (Done _ _ _) = x.
Proof.
  pose proof (ltac:(intros T next h; now apply functional_extensionality): forall T next, (forall x, bind (next x) (Done effectType effectResponse A) = next x) -> (fun (x : T) => bind (next x) (Done effectType effectResponse A)) = next) as H.
  induction x as [| a next IH]; try easy; simpl; now (rewrite (H _ _ IH) || rewrite IH).
Qed.

Lemma assoc {effectType effectResponse A B C} (x : Action effectType effectResponse A) (f : A -> Action effectType effectResponse B) (g : B -> Action effectType effectResponse C) : bind x (fun x => bind (f x) g) = bind (bind x f) g.
Proof.
  pose proof (ltac:(intros T next h; now apply functional_extensionality): forall T next, (forall x, bind (next x) (fun x => bind (f x) g) = bind (bind (next x) f) g) -> (fun (x : T) => bind (next x) (fun x => bind (f x) g)) = (fun x => bind (bind (next x) f) g)) as H.
  induction x as [| a next IH]; try easy; simpl; now (rewrite IH || rewrite (H _ _ IH)).
Qed.

Definition shortCircuitAnd effectType effectResponse (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | false => Done _ _ _ false
  | true => b
  end).

Definition shortCircuitOr effectType effectResponse (a b : Action effectType effectResponse bool) := bind a (fun x => match x with
  | true => Done _ _ _ true
  | false => b
  end).

Inductive BasicEffects (arrayType : string -> Type) :=
| Trap
| Flush
| ReadChar
| WriteChar (value : Z)
| Retrieve (arrayName : string) (index : Z)
| Store (arrayName : string) (index : Z) (value : arrayType arrayName).

Definition basicEffectsReturnValue {arrayType} (effect : BasicEffects arrayType) : Type :=
  match effect with
  | Trap _ => False
  | Flush _ => unit
  | ReadChar _ => Z
  | WriteChar _ _ => unit
  | Retrieve _ arrayName _ => arrayType arrayName
  | Store _ _ _ _ => unit
  end.

Inductive WithLocalVariables (arrayType : string -> Type) :=
| BasicEffect (effect : BasicEffects arrayType)
| BooleanLocalGet (name : string)
| BooleanLocalSet (name : string) (value : bool)
| NumberLocalGet (name : string)
| NumberLocalSet (name : string) (value : Z).

Definition withLocalVariablesReturnValue {arrayType} (effect : WithLocalVariables arrayType) : Type :=
  match effect with
  | BasicEffect _ effect => basicEffectsReturnValue effect
  | BooleanLocalGet _ _ => bool
  | BooleanLocalSet _ _ _ => unit
  | NumberLocalGet _ _ => Z
  | NumberLocalSet _ _ _ => unit
  end.

Inductive WithLoopControl (arrayType : string -> Type) :=
| WithLocalVariablesEffect (effect : WithLocalVariables arrayType)
| Continue
| Break.

Definition withLoopControlReturnValue {arrayType} (effect : WithLoopControl arrayType) : Type :=
  match effect with
  | WithLocalVariablesEffect _ effect => withLocalVariablesReturnValue effect
  | Continue _ => False
  | Break _ => False
  end.
