From CoqCP Require Import Options Imperative Execution InteractiveExecution DecimalEncoding.
From Generated Require Import KthHighestScore.
From Stdlib Require Import Arith.PeanoNat Bool.Bool.
From stdpp Require Import list.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope Z_scope.

(* The mathematical postcondition on the final decimal answer. *)
Fixpoint above (f : nat -> nat) (n s : nat) : nat :=
  match n with
  | 0%nat => 0%nat
  | S n => Nat.add (above f n s) (if Nat.ltb s (f (S n)) then 1%nat else 0%nat)
  end.

Definition kth_highest n k (F S : nat -> nat) score :=
  ((exists i, (1 <= i <= n)%nat /\ F i = score) \/
   (exists j, (1 <= j <= n)%nat /\ S j = score)) /\
  (above F n score + above S n score = k - 1)%nat.

Definition valid_scores n (scores : nat -> nat) :=
  (forall i, (1 <= i <= n)%nat -> (1 <= scores i <= 1000000000)%nat) /\
  (forall i j, (1 <= i)%nat -> (i < j)%nat -> (j <= n)%nat -> (scores j < scores i)%nat).

(* A truthful judge supplies one decimal response for every emitted query.
   The contract permits any legal strategy within the query budget. *)
Inductive ProtocolCountry := ProtocolFinland | ProtocolSweden.
Definition ProtocolQuery := (ProtocolCountry * nat)%type.
Definition legalQuery n (q : ProtocolQuery) := (1 <= snd q <= n)%nat.

Definition expectedQueryLine (q : ProtocolQuery) : list Z :=
  (match fst q with ProtocolFinland => [70] | ProtocolSweden => [83] end) ++ [32] ++
  decimalBytes (snd q) ++ [10].
Definition expectedResponseLine (q : ProtocolQuery) (F S : nat -> nat) : list Z :=
  decimalBytes ((match fst q with ProtocolFinland => F | ProtocolSweden => S end) (snd q)) ++ [10].
Definition expectedResponses qs F S := concat (map (fun q => expectedResponseLine q F S) qs).
Definition expectedRequests qs := concat (map expectedQueryLine qs).
Fixpoint expectedQueryFlushes qs F S prefix :=
  match qs with
  | [] => []
  | q :: rest =>
      {| flushedOutput := prefix ++ expectedQueryLine q;
         unreadInput := expectedResponses (q :: rest) F S |} ::
      expectedQueryFlushes rest F S (prefix ++ expectedQueryLine q)
  end.
Definition inputBytes n k qs F S :=
  decimalBytes n ++ [32] ++ decimalBytes k ++ [10] ++ expectedResponses qs F S.
Definition outputBytes qs score :=
  expectedRequests qs ++ [33;32] ++ decimalBytes score ++ [10].
Definition flushes qs F S score :=
  expectedQueryFlushes qs F S [] ++
  [{| flushedOutput := outputBytes qs score; unreadInput := [] |}].
Definition initial n k qs F S : @Machine arrayIndex2 (arrayType _ environment2) :=
  {| memory := arrays _ environment2; stdin := inputBytes n k qs F S; stdout := [] |}.
Definition program := funcdef_0__main (fun _ => false) (fun _ => 0).
Definition Program := Action (WithArrays arrayIndex2 (arrayType _ environment2))
  withArraysReturnValue unit.

(* The trace witnesses the program's chosen strategy. Replies are fixed by F/S;
   each query flush must leave its reply unread. Termination, complete output,
   full input consumption, and the final flush are mandatory. *)
Definition required (candidate : Program) : Prop :=
  candidate = program /\
  forall n k F S,
    (1 <= n)%nat -> (1 <= k <= 2*n)%nat -> (n <= 100000)%nat ->
    valid_scores n F -> valid_scores n S ->
    (forall i j, (1 <= i <= n)%nat -> (1 <= j <= n)%nat -> F i <> S j) ->
    exists qs score,
      Forall (legalQuery n) qs /\ (length qs <= 36)%nat /\
      kth_highest n k F S score /\
      endToEnd candidate (initial n k qs F S)
        (outputBytes qs score) (flushes qs F S score).

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
