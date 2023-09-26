From CoqCP Require Import Options.
From stdpp Require Import strings.
Require Import ZArith.
Open Scope Z_scope.

Record Environment := { arrayType: string -> Type; arrays: forall (name : string), list (arrayType name) }.

Record Locals := { numbers: string -> Z; booleans: string -> bool }.

Inductive Action (environment : Environment) (locals : Locals) :=
| Done
| Store (arrayName : string) (index : Z) (value : arrayType environment arrayName) : (Action _ _) -> (Action _ _)
| Retrieve (arrayName : string) (index : Z) : (arrayType environment arrayName -> (Action _ _)) -> (Action _ _)
| NumberLocalSet (variableName : string) (value : Z) : (Action _ _) ->  (Action _ _)
| NumberLocalGet (variableName : string) : (Z -> (Action _ _)) -> (Action _ _)
| BooleanLocalGet (variableName : string) (value : bool) : (Action _ _) -> (Action _ _)
| BooleanLocalSet (variableName : string) : (bool -> (Action _ _)) -> (Action _ _)
| WriteInt8 (output : Z) : (Action _ _) -> (Action _ _)
| ReadInt8 : (Z -> (Action _ _)) -> (Action _ _).
