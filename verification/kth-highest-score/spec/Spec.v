From Stdlib Require Import Arith.PeanoNat.
Local Open Scope nat_scope.

(* Number of real scores strictly greater than s. *)
Fixpoint above (f : nat -> nat) (n s : nat) : nat :=
  match n with
  | 0 => 0
  | S n => above f n s + if s <? f (S n) then 1 else 0
  end.

Definition kth_highest n k (F S : nat -> nat) score :=
  ((exists i, (1 <= i <= n)%nat /\ F i = score) \/
   (exists j, (1 <= j <= n)%nat /\ S j = score)) /\
  (above F n score + above S n score = k - 1)%nat.

Definition valid_scores n (scores : nat -> nat) :=
  (forall i, (1 <= i <= n)%nat -> (1 <= scores i <= 1000000000)%nat) /\
  (forall i j, (1 <= i)%nat -> (i < j)%nat -> (j <= n)%nat -> scores j < scores i).

Definition Program := nat -> nat -> (nat -> nat) -> (nat -> nat) -> nat.

(* The task contract: return the k-th largest score among the two countries. *)
Definition required (program : Program) : Prop :=
  forall n k F S,
    (1 <= n)%nat -> (1 <= k <= 2*n)%nat -> (n <= 100000)%nat ->
    valid_scores n F -> valid_scores n S ->
    (forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> F i <> S j) ->
    kth_highest n k F S (program n k F S).

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
