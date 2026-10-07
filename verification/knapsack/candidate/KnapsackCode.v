From CoqCP Require Import Options Imperative DecimalEncoding.
From CoqCP Require Import DecimalEncoding Optimality ArrayExecution.
From Submission Require Import Knapsack.
From Generated Require Import Knapsack.
Require Export Trusted.Spec.
From stdpp Require Import numbers list strings.
Require Import Stdlib.Numbers.DecimalString.
Require Import Stdlib.Strings.Ascii.

Fixpoint stdinBytes (text : string) : list Z :=
  match text with
  | EmptyString => []
  | String character tail => Z.of_nat (nat_of_ascii character) :: stdinBytes tail
  end.


Definition start items limit := runProgram (arrays _ environment2)
  (funcdef_0__main (fun _ => false) (fun _ => 0%Z)) (generateData items limit).

Definition extractAnswer (result : option ((forall name, list (arrayType _ environment2 name)) * list Z * list Z)) : Z :=
  match result with
  | None => 0%Z
  | Some (_, _, output) => fold_left (fun value digit => (10 * value + digit - 48)%Z) (take (length output - 1) output) 0%Z
  end.

Definition knapsackArrays (items : list (nat * nat)) (dp : list Z) (message : Z)
  (input printBuffer : list Z) : forall name, list (arrayType _ environment2 name) :=
  fun name => match name with
  | arraydef_0__dp => dp
  | arraydef_0__weights => map (fun item => Z.of_nat (fst item)) items
  | arraydef_0__values => map (fun item => Z.of_nat (snd item)) items
  | arraydef_0__message => [message]
  | arraydef_0__n => [Z.of_nat (length items)]
  | arraydef_0__input => input
  | arraydef_0__printBuffer => printBuffer
  end.
