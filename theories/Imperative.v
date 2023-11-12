From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ZArith.
Open Scope Z_scope.

Record Environment := { arrayType: string -> Type; arrays: forall (name : string), list (arrayType name) }.

Record Locals := { numbers: string -> Z; booleans: string -> bool }.

Inductive Action (arrayType : string -> Type) (effectType : Type) (effectResponse : effectType -> Type) (returnType : Type) :=
| Done (returnValue : returnType)
| Dispatch (effect : effectType) (continuation : effectResponse effect -> Action arrayType effectType effectResponse returnType).

Fixpoint bind {arrayType effectType effectResponse A B} (a : Action arrayType effectType effectResponse A) (f : A -> Action arrayType effectType effectResponse B) : Action arrayType effectType effectResponse B :=
  match a with
  | Done _ _ _ _ value => f value
  | Dispatch _ _ _ _ effect continuation => Dispatch _ _ _ _ effect (fun response => bind (continuation response) f)
  end.

Lemma leftIdentity {arrayType effectType effectResponse A B} (x : A) (f : A -> Action arrayType effectType effectResponse B) : bind (Done _ _ _ _ x) f = f x.
Proof. easy. Qed.

Lemma rightIdentity {arrayType effectType effectResponse A} (x : Action arrayType effectType effectResponse A) : bind x (Done _ _ _ _) = x.
Proof.
  pose proof (ltac:(intros T next h; now apply functional_extensionality): forall T next, (forall x, bind (next x) (Done arrayType effectType effectResponse A) = next x) -> (fun (x : T) => bind (next x) (Done arrayType effectType effectResponse A)) = next) as H.
  induction x as [| a next IH]; try easy; simpl; now (rewrite (H _ _ IH) || rewrite IH).
Qed.

Lemma assoc {arrayType effectType effectResponse A B C} (x : Action arrayType effectType effectResponse A) (f : A -> Action arrayType effectType effectResponse B) (g : B -> Action arrayType effectType effectResponse C) : bind x (fun x => bind (f x) g) = bind (bind x f) g.
Proof.
  pose proof (ltac:(intros T next h; now apply functional_extensionality): forall T next, (forall x, bind (next x) (fun x => bind (f x) g) = bind (bind (next x) f) g) -> (fun (x : T) => bind (next x) (fun x => bind (f x) g)) = (fun x => bind (bind (next x) f) g)) as H.
  induction x as [| a next IH]; try easy; simpl; now (rewrite IH || rewrite (H _ _ IH)).
Qed.

Definition shortCircuitAnd arrayType effectType effectResponse (a b : Action arrayType effectType effectResponse bool) := bind a (fun x => match x with
  | false => Done _ _ _ _ false
  | true => b
  end).

Definition shortCircuitOr arrayType effectType effectResponse (a b : Action arrayType effectType effectResponse bool) := bind a (fun x => match x with
  | true => Done _ _ _ _ true
  | false => b
  end).
