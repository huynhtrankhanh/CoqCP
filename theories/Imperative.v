From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ZArith.
Open Scope Z_scope.

Record Environment := { arrayType: string -> Type; arrays: forall (name : string), list (arrayType name) }.

Record Locals := { numbers: string -> Z; booleans: string -> bool }.

Inductive Action (arrayType : string -> Type) (returnType : Type) :=
| Done (returnValue : returnType)
| Store (arrayName : string) (index : Z) (value : arrayType arrayName) : Action _ _ -> Action _ _
| Retrieve (arrayName : string) (index : Z) : (arrayType arrayName -> Action _ _) -> Action _ _
| NumberLocalSet (variableName : string) (value : Z) : Action _ _ ->  Action _ _
| NumberLocalGet (variableName : string) : (Z -> Action _ _) -> Action _ _
| BooleanLocalSet (variableName : string) (value : bool) : Action _ _ -> Action _ _
| BooleanLocalGet (variableName : string) : (bool -> Action _ _) -> Action _ _
| WriteChar (output : Z) : Action _ _ -> Action _ _
| ReadChar : (Z -> Action _ _) -> Action _ _
| Flush : Action _ _ -> Action _ _.

Fixpoint bind {arrayType A B} (a : Action arrayType A) (f : A -> Action arrayType B) : Action arrayType B :=
  match a with
  | Done _ _ value => f value
  | Store _ _ a b c next => Store _ _ a b c (bind next f)
  | Retrieve _ _ a b next => Retrieve _ _ a b (fun x => bind (next x) f)
  | NumberLocalSet _ _ a b next => NumberLocalSet _ _ a b (bind next f)
  | NumberLocalGet _ _ a next => NumberLocalGet _ _ a (fun x => bind (next x) f)
  | BooleanLocalSet _ _ a b next => BooleanLocalSet _ _ a b (bind next f)
  | BooleanLocalGet _ _ a next => BooleanLocalGet _ _ a (fun x => bind (next x) f)
  | WriteChar _ _ a next => WriteChar _ _  a (bind next f)
  | ReadChar _ _ next => ReadChar _ _ (fun x => bind (next x) f)
  | Flush _ _ next => Flush _ _ (bind next f)
  end.

Lemma leftIdentity {arrayType A B} (x : A) (f : A -> Action arrayType B) : bind (Done _ _ x) f = f x.
Proof. easy. Qed.

Lemma rightIdentity {arrayType A} (x : Action arrayType A) : bind x (Done _ _) = x.
Proof.
  pose proof (ltac:(intros T next h; now apply functional_extensionality): forall T next, (forall x, bind (next x) (Done arrayType A) = next x) -> (fun (x : T) => bind (next x) (Done arrayType A)) = next) as H.
  induction x as [| a b c next IH | a b next IH | a b next IH | a next IH | a b next IH | a next IH | a next IH | next IH | next IH]; try easy; simpl; now (rewrite (H _ _ IH) || rewrite IH).
Qed.

Lemma assoc {arrayType A B C} (x : Action arrayType A) (f : A -> Action arrayType B) (g : B -> Action arrayType C) : bind x (fun x => bind (f x) g) = bind (bind x f) g.
Proof.
  pose proof (ltac:(intros T next h; now apply functional_extensionality): forall T next, (forall x, bind (next x) (fun x => bind (f x) g) = bind (bind (next x) f) g) -> (fun (x : T) => bind (next x) (fun x => bind (f x) g)) = (fun x => bind (bind (next x) f) g)) as H.
  induction x as [| a b c next IH | a b next IH | a b next IH | a next IH | a b next IH | a next IH | a next IH | next IH | next IH]; try easy; simpl; now (rewrite IH || rewrite (H _ _ IH)).
Qed.

Inductive LoopControl :=
| KeepGoing
| Stop.

Fixpoint rangeLoop {arrayType} (n : nat) (f : nat -> Action arrayType LoopControl) : Action arrayType unit :=
  match n with
  | O => Done _ _ tt
  | S n => bind (f n) (fun control => match control with
    | Stop => Done _ _ tt
    | KeepGoing => rangeLoop n f
    end)
  end.

Definition noArrays := fun (_ : string) => False.

Definition readChar arrayType := ReadChar arrayType Z (fun x => Done arrayType Z x).

Definition retrieve arrayType name index := Retrieve arrayType (arrayType name) name index (fun x => Done _ _ x).

Definition numberLocalGet arrayType name := NumberLocalGet arrayType Z name (fun x => Done _ _ x).

Definition booleanLocalGet arrayType name := BooleanLocalGet arrayType bool name (fun x => Done _ _ x).

Definition exampleLoop := rangeLoop 5 (fun _ => bind (readChar noArrays) (fun value => if Z.eqb value (5 : Z) then Done _ _ Stop else Done _ _ KeepGoing)).
