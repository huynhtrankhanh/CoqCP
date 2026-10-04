From CoqCP Require Import Options Imperative Knapsack.
From Generated Require Import Knapsack.
From stdpp Require Import numbers list strings.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.Ascii.

Fixpoint stdinBytes (text : string) : list Z :=
  match text with
  | EmptyString => []
  | String character tail => Z.of_nat (nat_of_ascii character) :: stdinBytes tail
  end.

Fixpoint littleDigits (fuel : nat) (value : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel => if decide (value = 0)%Z then []
      else (value mod 10 + 48)%Z :: littleDigits fuel (value / 10)%Z
  end.
Definition decimalBytes (value : nat) :=
  if decide (value = 0)%nat then [48%Z] else reverse (littleDigits 20 (Z.of_nat value)).

Definition generateData (items : list (nat * nat)) (limit : nat) : list Z :=
  decimalBytes (length items) ++ [32%Z] ++ decimalBytes limit ++ [10%Z] ++
  concat (map (fun item => decimalBytes (fst item) ++ [32%Z] ++ decimalBytes (snd item) ++ [10%Z]) items).

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
