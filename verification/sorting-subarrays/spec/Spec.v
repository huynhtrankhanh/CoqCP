From CoqCP Require Import Options Imperative DecimalEncoding.
From Stdlib Require Import Lists.List ZArith.ZArith.
From stdpp Require Import sorting.
Import ListNotations.

(* Public indices are one based, and both query endpoints are inclusive. *)
Definition query := (nat * nat)%type.
Definition valid_query (n : nat) (q : query) : Prop :=
  1 <= fst q /\ fst q <= snd q /\ snd q <= n.

Definition sort_subarray (a : list Z) (q : query) : list Z :=
  let l := Nat.pred (fst q) in
  let len := snd q - l in
  firstn l a ++ merge_sort Z.le (firstn len (skipn l a)) ++ skipn (snd q) a.

Fixpoint execute (a : list Z) (queries : list query) : list Z :=
  match queries with
  | [] => a
  | q :: qs => execute (sort_subarray a q) qs
  end.

Definition valid_input (a : list Z) (k : nat) (qs : list query) : Prop :=
  1 <= length a <= 200000 /\ 1 <= k <= length a /\
  1 <= length qs <= 200000 /\
  Forall (fun x => (-1000000000 <= x <= 1000000000)%Z /\ x <> 0%Z) a /\
  Forall (valid_query (length a)) qs.

Definition required_solver (program : list Z -> nat -> list query -> Z) : Prop :=
  forall a k qs, valid_input a k qs ->
    program a k qs = nth (Nat.pred k) (execute a qs) 0%Z.

(* The wire contract specifies bytes independently of the submitted parser.
   Public indices are still one based, and each input line ends with LF. *)
Definition signed_bytes (x : Z) : list Z :=
  if (x <? 0)%Z then 45%Z :: decimalBytes (Z.to_nat (-x))
  else decimalBytes (Z.to_nat x).
Definition word (x sep : Z) := signed_bytes x ++ [sep].
Fixpoint array_input (a : list Z) : list Z :=
  match a with
  | [] => []
  | x :: xs => word x (match xs with [] => 10%Z | _ => 32%Z end) ++ array_input xs
  end.
Definition query_input (q : query) := word (Z.of_nat (fst q)) 32%Z ++ word (Z.of_nat (snd q)) 10%Z.
Definition input_bytes a k qs :=
  word (Z.of_nat (length a)) 32%Z ++ word (Z.of_nat k) 32%Z ++
  word (Z.of_nat (length qs)) 10%Z ++ array_input a ++ concat (map query_input qs).
Definition output_bytes a k qs := signed_bytes (nth (Nat.pred k) (execute a qs) 0%Z) ++ [10%Z].
Definition Program := Action BasicEffect basicEffectReturnValue unit.

(* Successful execution of the submitted byte-stream entry point, exact entire
   stdout, and full consumption of the specified stdin are all mandatory. *)
Definition required (program : Program) : Prop :=
  forall a k qs, valid_input a k qs ->
    runIO program (input_bytes a k qs) [] = Some (tt, [], output_bytes a k qs).

Module Type SOLUTION.
  Parameter program : Program.
  Parameter correct : required program.
End SOLUTION.
