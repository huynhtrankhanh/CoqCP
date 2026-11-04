From CoqCP Require Import Options.
From Trusted Require Import Protocol.
From Stdlib Require Import Lists.List Arith.PeanoNat ZArith.ZArith Bool.Bool.
From stdpp Require Import numbers list.
Import ListNotations.
Open Scope Z_scope.
Module CapacityGeneral.
Definition wordmax : Z := 18446744073709551615.
Definition signedmax : Z := 9223372036854775807.
Definition axiom_cost (tag root:nat) : nat := (match tag with
| 0=>2 | 1=>6 | 2=>3 | 3=>S root*S root+2 | 4=>S root*S root+5
| 5=>1 | 6 | 7 | 8=>5 | 9=>10 | 10=>15 | 11=>8 | 12=>10 | 13=>9 | 14=>33
| 15=>S root*S root+14 | 16=>3*(S root*S root)+21 | 17=>42 | _=>0 end)%nat.
Definition axiom_bound capacity tag := axiom_cost tag (capacity-1).
Definition formula_next capacity := (capacity+3*(capacity*capacity)+42)%nat.
Definition index_next E N bound := (2*bound+E+3*N+4)%nat.
Fixpoint formula_after initial count := match count with O=>initial | S count=>formula_next(formula_after initial count) end.
Fixpoint index_after E N initial count := match count with O=>initial | S count=>index_next E N (index_after E N initial count) end.
Definition slots E := (E*E)%nat.
Definition formula_target request capacity := match Protocol.opcode request with
 | 1%nat|2%nat|3%nat|4%nat|13%nat=>S capacity
 | 7%nat|8%nat=>(capacity+2*(capacity*capacity)+13)%nat
 | 11%nat=>match Protocol.arguments request with tag::_=>(capacity+axiom_bound capacity tag)%nat|_=>capacity end
 | 14%nat=>(capacity+capacity*capacity+10)%nat | _=>capacity end.
Definition index_target request bound N := match Protocol.opcode request with
 | 7%nat|14%nat=>(bound+2)%nat |8%nat=>(2*bound+3)%nat |11%nat=>(bound+3*N+4)%nat
 |22%nat=>bound|_=>Nat.max bound N end.
Definition formula_end request F E := if Nat.eqb(Protocol.opcode request)24 then formula_after F (slots E) else formula_target request F.
Definition index_end request B N E := if Nat.eqb(Protocol.opcode request)24 then index_after E N B (slots E) else index_target request B N.
Definition class_end request C E := if Nat.eqb(Protocol.opcode request)24 then (C+slots E)%nat else S C.
Definition expression_end request E := if Nat.eqb(Protocol.opcode request)22 then S E else E.
Definition guard arena index fuel := Z.leb(Z.of_nat arena)signedmax && Z.leb(Z.of_nat(5*(fuel*fuel)+1))wordmax && Z.leb(Z.of_nat index)wordmax.
Definition resources request F B C E N := match Protocol.opcode request,Protocol.arguments request with
 | 7%nat,[_;_]=>guard (F+2*(F*F)+6) (B+2) F
 | 8%nat,[_;_]=>guard (F+2*(F*F)+13) (2*B+3) F
 | 11%nat,[tag;_;_;_]=>guard (F+axiom_bound F tag) (B+N+2) F
 | 14%nat,[_]=>guard (F+F*F+10) (B+2) F
 | 24%nat,_=>guard (formula_after F (slots E)) (index_after E N B (slots E)) (formula_after F (slots E)) && Z.leb(Z.of_nat(C+slots E+1))wordmax
 | _,_=>true end.
Fixpoint numbers_max values := match values with []=>0%nat|value::rest=>Nat.max value (numbers_max rest) end.
Fixpoint maximum requests := match requests with []=>0%nat | request::rest=>Nat.max (numbers_max(Protocol.arguments request)) (maximum rest) end.
Record caps := Caps { formulas:nat; indices:nat; classes:nat; history:nat; bindings:nat; expressions:nat; names:nat }.
Definition initial N := Caps 1 (Nat.max 3 N) 0 0 0 0 0.
Definition step N request before := Caps (formula_end request (formulas before) (expressions before))
 (index_end request (indices before) N (expressions before)) (class_end request (classes before) (expressions before))
 (S(history before)) (S(bindings before)) (expression_end request (expressions before)) (names before+1024).
Definition common N before request := Z.leb (Z.of_nat(formulas before)) signedmax && Z.leb (Z.of_nat(formulas(step N request before))) signedmax &&
 Z.leb (Z.of_nat(indices(step N request before))) wordmax && Z.leb(Z.of_nat(S(classes before)))wordmax &&
 Z.leb(Z.of_nat(S(history before)))wordmax && Z.leb(Z.of_nat(S(bindings before)))wordmax &&
 Z.leb(Z.of_nat(S(expressions before)))wordmax && Z.leb(Z.of_nat(names before+1024))wordmax.
Definition head_check N before request := Nat.leb(Protocol.opcode request)26 && Nat.leb(numbers_max(Protocol.arguments request)) N &&
 common N before request && resources request (formulas before) (indices before) (classes before) (expressions before) N.
Fixpoint check N before requests := match requests with []=>true | request::tail=>if Nat.eqb(Protocol.opcode request)0 then true else
 head_check N before request && check N (step N request before) tail end.
Definition domain requests := let N:=maximum requests in check N (initial N) requests=true.
End CapacityGeneral.
