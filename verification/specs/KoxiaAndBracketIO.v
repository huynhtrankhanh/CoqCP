From CoqCP Require Import Options Imperative Execution.
From Generated Require Import KoxiaAndBracket.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat.
Import ListNotations.
Local Open Scope nat_scope.

(* A true bit is '('; a false bit is ')'. Each position has its own mask
   bit, even when two retained strings happen to have identical characters. *)
Fixpoint masks (n : nat) : list (list bool) :=
  match n with
  | O => [[]]
  | S n => map (cons false) (masks n) ++ map (cons true) (masks n)
  end.

Fixpoint retain (s mask : list bool) : list bool :=
  match s, mask with
  | ch :: s, keep :: mask => if keep then ch :: retain s mask else retain s mask
  | _, _ => []
  end.

Fixpoint balance (s : list bool) : Z :=
  match s with
  | [] => 0%Z
  | ch :: s => ((if ch then 1 else -1) + balance s)%Z
  end.

(* The mathematical Dyck condition, including the empty sequence. *)
Definition balanced (s : list bool) : bool :=
  Z.eqb (balance s) 0 &&
  forallb (fun i => Z.leb 0 (balance (firstn i s))) (seq 0 (S (length s))).

Definition feasible (s : list bool) : list (list bool) :=
  filter (fun mask => balanced (retain s mask)) (masks (length s)).

Definition longest (s : list bool) : nat :=
  fold_right Nat.max 0 (map (fun mask => length (retain s mask)) (feasible s)).

Definition optimalMasks (s : list bool) : list (list bool) :=
  filter (fun mask => Nat.eqb (length (retain s mask)) (longest s)) (feasible s).

Definition answer (s : list bool) : nat :=
  Z.to_nat ((Z.of_nat (length (optimalMasks s)) mod 998244353)%Z).

Definition input (s : list bool) : list Z :=
  map (fun ch : bool => if ch then 40%Z else 41%Z) s ++ [10%Z].

Fixpoint decimal (fuel value : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel =>
      if value <? 10 then [(Z.of_nat value + 48)%Z]
      else decimal fuel (value / 10) ++ [(Z.of_nat (value mod 10) + 48)%Z]
  end.

Definition output (s : list bool) : list Z := decimal 10 (answer s) ++ [10%Z].

Definition Program := Action
  (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue unit.

(* Existence of successful execution is mandatory. Input bounds, input bytes,
   initial storage, exact output, and full input consumption live here.
   No algorithm, DP recurrence, polynomial routine, or existing problem spec
   is used to define the required answer. *)
Definition required (program : Program) : Prop :=
  program = funcdef_0__main (fun _ => false) (fun _ => 0%Z) /\
  forall s : list bool, 1 <= length s <= 500000 ->
    exists final,
      exec program {| memory := arrays _ environment1; stdin := input s; stdout := [] |}
        = Some (tt, final) /\
      stdout final = output s /\ stdin final = [].

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
