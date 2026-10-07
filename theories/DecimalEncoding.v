From CoqCP Require Import Options.
From stdpp Require Import numbers list.

(* Shared decimal wire encoding; independent of any generated program. *)
Fixpoint littleDigits (fuel : nat) (value : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel => if decide (value = 0)%Z then []
      else (value mod 10 + 48)%Z :: littleDigits fuel (value / 10)%Z
  end.
Definition decimalBytes (value : nat) :=
  if decide (value = 0)%nat then [48%Z] else reverse (littleDigits 20 (Z.of_nat value)).
