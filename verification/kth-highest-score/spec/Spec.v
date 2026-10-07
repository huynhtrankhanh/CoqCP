From CoqCP Require Import Options Imperative Execution.
From Generated Require Import KthHighestScore.
From stdpp Require Import numbers list.
From Stdlib Require Import Arith.PeanoNat.
Local Open Scope nat_scope.

Fixpoint above (f : nat -> nat) (n s : nat) : nat :=
  match n with
  | 0 => 0
  | S n => above f n s + if s <? f (S n) then 1 else 0
  end.

Definition ceiling := S 1000000000.

Definition country_valid (n : nat) (f : nat -> nat) :=
  f 0 = ceiling /\ f (S n) = 0 /\
  (forall x y, x < y -> y <= S n -> f y < f x).

Definition kth_highest n k (F S : nat -> nat) score :=
  ((exists i, (1 <= i <= n)%nat /\ F i = score) \/
   (exists j, (1 <= j <= n)%nat /\ S j = score)) /\
  (above F n score + above S n score = k - 1)%nat.

Open Scope Z_scope.
Definition QueryProcedure :=
  (varsfuncdef_0__query -> bool) -> (varsfuncdef_0__query -> Z) ->
  Action (WithArrays arrayIndex2 (arrayType _ environment2)) withArraysReturnValue unit.

Definition mainWithQuery : QueryProcedure ->
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue unit := ltac:(
  let code := eval unfold funcdef_0__main_body in funcdef_0__main_body in
  let code := eval pattern funcdef_0__query in code in
  lazymatch code with ?f funcdef_0__query => exact f end).

Definition generatedSearchLoop (query : QueryProcedure) :
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue unit := ltac:(
  let code := eval cbv beta delta [mainWithQuery] in (mainWithQuery query) in
  lazymatch code with context [(Done _ _ _ 17%Z >>= ?cont)] =>
    let body := eval cbn [bind] in (Done _ _ _ 17%Z >>= cont) in exact body
  end).

Definition oracleQuery (F S : nat -> nat) : QueryProcedure :=
  fun _ nums => Dispatch _ _ _
    (Store _ _ arraydef_0__reply 0
      (Z.of_nat ((if bool_decide (nums vardef_0__query_country = 70) then F else S)
        (Z.to_nat (nums vardef_0__query_index)))))
    (fun _ => Done _ _ _ tt).

Definition kernelArrays (reply : Z) : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__input => [0]
  | arraydef_0__reply => [reply]
  | arraydef_0__printBuffer => repeat 0 20
  end.

Definition kernelMachine reply : Machine :=
  {| memory := kernelArrays reply; stdin := []; stdout := [] |}.

Definition mainNums (n k lo hi mid j f s a : nat) : varsfuncdef_0__main -> Z :=
  fun name => Z.of_nat (match name with
  | vardef_0__main_n => n | vardef_0__main_k => k
  | vardef_0__main_lo => lo | vardef_0__main_hi => hi
  | vardef_0__main_mid => mid | vardef_0__main_j => j
  | vardef_0__main_f => f | vardef_0__main_s => s | vardef_0__main_answer => a
  end).

(* Generated search-loop refinement with truthful queries; excludes decimal I/O. *)
Definition Program := QueryProcedure ->
  Action (WithLocalVariables arrayIndex2 (arrayType _ environment2) varsfuncdef_0__main)
    withLocalVariablesReturnValue unit.
Definition required (program : Program) : Prop :=
  program = generatedSearchLoop /\
  forall n k F S, (1 <= n)%nat -> (1 <= k <= 2*n)%nat -> (n <= 100000)%nat ->
    country_valid n F -> country_valid n S ->
    (forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> F i <> S j) ->
    exists final,
      execLocal (program (oracleQuery F S))
        {| machine := kernelMachine 0; bools := fun _ => false;
           nums := mainNums n k (k-n) (Nat.min k n) 0 0 0 0 0 |} = Some (tt, final) /\
      kth_highest n k F S
        (Nat.min (F (Z.to_nat (nums final vardef_0__main_lo)))
          (S (k - Z.to_nat (nums final vardef_0__main_lo))%nat)).

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
