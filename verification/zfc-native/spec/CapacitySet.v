From CoqCP Require Import Options.
From Trusted Require Import Protocol.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

(** Evaluator-owned pure resource schedule for the flat, set-valued schema
    fragment. It depends only on the request language, never on the submitted
    implementation or its execution. *)
Module CapacitySet.
Definition maximum : Z := 18446744073709551615.
Definition formula_bound : Z := 9223372036854775807.
Record caps := Caps { formulas:nat; classes:nat; history:nat; bindings:nat; expressions:nat; names:nat }.
Definition initial := Caps 1 0 0 0 0 0.
Definition formula_target request formula_cap expression_cap := match Protocol.opcode request with
 | 24%nat=>(formula_cap+42*(expression_cap*expression_cap))%nat
 | 11%nat=>(formula_cap+42)%nat | 22%nat=>formula_cap | _=>S formula_cap end.
Definition expression_increment request := if Nat.eqb (Protocol.opcode request) 22 then 1%nat else 0%nat.
Definition expression_target request expression_cap := (expression_cap+expression_increment request)%nat.
Definition step request before := Caps (formula_target request (formulas before) (expressions before))
 (S (classes before)) (S (history before)) (S (bindings before))
 (expression_target request (expressions before)) (names before+1024).
Definition basic opcode := existsb (Nat.eqb opcode) [1;2;3;4;5;6;9;10;12;13;15;16;17;18;19;20;21;23;25;26]%nat.
Definition uses_rename tag := existsb (Nat.eqb tag) [3;4;15;16]%nat.
Definition schema_flat kind tag := existsb (Nat.eqb kind) [0;1;2;4;5;6;8;9;11]%nat &&
 (negb (Nat.eqb kind 8) || negb (uses_rename tag)).
Definition admissible request := if basic (Protocol.opcode request) then
 negb (Nat.eqb (Protocol.opcode request) 6) else match Protocol.opcode request,Protocol.arguments request with
 | 0%nat,_=>true | 11%nat,[tag;_;_;_]=>negb (uses_rename tag)
 | 22%nat,[kind;tag;_;_;_]=>schema_flat kind tag | 24%nat,_=>true | _,_=>false end.
Definition head_check before request := admissible request && Nat.leb (Protocol.opcode request) 26 &&
 Z.leb (Z.of_nat (formulas before)) formula_bound &&
 Z.leb (Z.of_nat (formulas (step request before))) formula_bound &&
 Z.leb (Z.of_nat (S (classes before))) maximum && Z.leb (Z.of_nat (S (history before))) maximum &&
 Z.leb (Z.of_nat (S (bindings before))) maximum && Z.leb (Z.of_nat (S (expressions before))) maximum &&
 Z.leb (Z.of_nat (names before+1024)) maximum.
Fixpoint check before requests := match requests with
 | []=>true | request::tail=>if Nat.eqb (Protocol.opcode request) 0 then true else
 head_check before request && check (step request before) tail end.
Definition domain requests := check initial requests=true.
End CapacitySet.
