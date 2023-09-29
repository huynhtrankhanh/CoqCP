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
| BooleanLocalGet (variableName : string) (value : bool) : Action _ -> Action _
| BooleanLocalSet (variableName : string) : (bool -> Action _) -> Action _
| WriteInt8 (output : Z) : Action _ -> Action _
| ReadInt8 : (Z -> Action _) -> Action _
| Flush : Action _ -> Action _.
