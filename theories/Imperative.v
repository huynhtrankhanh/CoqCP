From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import ZArith.
Open Scope Z_scope.

Record Environment := { arrayType: string -> Type; arrays: forall (name : string), list (arrayType name) }.

Record Locals := { numbers: string -> Z; booleans: string -> bool }.

Inductive Action (arrayType : string -> Type) :=
| Done
| Store (arrayName : string) (index : Z) (value : arrayType arrayName) : Action _ -> Action _
| Retrieve (arrayName : string) (index : Z) : (arrayType arrayName -> Action _) -> Action _
| NumberLocalSet (variableName : string) (value : Z) : Action _ ->  Action _
| NumberLocalGet (variableName : string) : (Z -> Action _) -> Action _
| BooleanLocalSet (variableName : string) (value : bool) : Action _ -> Action _
| BooleanLocalGet (variableName : string) : (bool -> Action _) -> Action _
| WriteChar (output : Z) : Action _ -> Action _
| ReadChar : (Z -> Action _) -> Action _
| Flush : Action _ -> Action _.

Fixpoint join {arrayType} (a z : Action arrayType) :=
  match a with
  | Done _ => z
  | Store _ a b c next => Store _ a b c (join next z)
  | Retrieve _ a b next => Retrieve _ a b (fun x => join (next x) z)
  | NumberLocalSet _ a b next => NumberLocalSet _ a b (join next z)
  | NumberLocalGet _ a next => NumberLocalGet _ a (fun x => join (next x) z)
  | BooleanLocalSet _ a b next => BooleanLocalSet _ a b (join next z)
  | BooleanLocalGet _ a next => BooleanLocalGet _ a (fun x => join (next x) z)
  | WriteChar _ a next => WriteChar _ a (join next z)
  | ReadChar _ next => ReadChar _ (fun x => join (next x) z)
  | Flush _ next => Flush _ (join next z)
  end.

Lemma joinAssoc {arrayType} (a b c :  Action arrayType) : join a (join b c) = join (join a b) c.
Proof.
  induction a in b, c |- *.
  (* so many cases! I could plow through, but what's the most efficient and maintainable way? *)
Admitted.
