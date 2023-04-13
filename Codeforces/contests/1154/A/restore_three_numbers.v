From CoqCP Require Import Options.
Require Import Relations.
From stdpp Require Import numbers.
From stdpp Require Import list.
From stdpp Require Import sorting.

Open Scope Z_scope.

(* Define general properties (move to shared file?)*)
Lemma z_permutation_by_merge_sort:
  forall (x y : list Z), (merge_sort Z.le x = merge_sort Z.le y) -> Permutation x y.
Proof.
  intros x y H.
  assert (Hx: Permutation (merge_sort Z.le x) x). {
    apply merge_sort_Permutation.
  }
  assert (Hy: Permutation (merge_sort Z.le y) y). {
    apply merge_sort_Permutation.
  }
  rewrite <- H in Hy.
  apply Permutation_sym in Hx.
  apply (Permutation_trans Hx Hy).
Qed.

(* Define the inputs *)

Definition valid_input_list(l : list Z) : Prop :=
  (forall x, In x l -> 2 <= x <= 1000000000)
  /\
  exists a : Z, 
  exists b : Z, 
  exists c : Z, 
  (a >= 1)
  /\ (b >= 1)
  /\ (c >= 1)
  /\ Permutation [a+b; a+c; b+c; a+b+c] l.

Record input_list : Type := {
    value : list Z;
    constraints : valid_input_list(value)
}.

(* Define the algorithm *)
Definition restore_a_b_c_aux(l : list Z) :=
  let s := merge_sort Z.le l in
  let a := (nth 3 s 0) - (nth 0 s 0) in
  let b := (nth 3 s 0) - (nth 1 s 0) in
  let c := (nth 3 s 0) - (nth 2 s 0) in
  [a; b; c].

Definition restore_a_b_c (l : input_list) : list Z :=
  restore_a_b_c_aux(value l).

(* Test with input examples *)

Ltac valid_input_list_tactic a b c :=
  unfold valid_input_list;
  split;
  [ intros x H; 
    repeat (destruct H as [H1 | H]; try lia);
    contradiction
  | exists a, b, c; 
    repeat (split; try lia); 
    apply z_permutation_by_merge_sort;
    reflexivity
  ].


(* Example 1 *)

Definition input_list_example_1 : input_list :=
  {| 
    value := [3; 6; 5; 4];
    constraints := ltac:(valid_input_list_tactic 2 1 3)
  |}.

Example restore_a_b_c_example_1: restore_a_b_c(input_list_example_1) = [3; 2; 1].
Proof.
  reflexivity.
Qed.

(* Example 2 *)
Definition input_list_example_2 : input_list :=
  {|
    value := [40; 40; 40; 60];
    constraints := ltac:(valid_input_list_tactic 20 20 20)
  |}.

Example restore_a_b_c_example_2: restore_a_b_c(input_list_example_2) = [20; 20; 20].
Proof.
  reflexivity.
Qed.

(* Example 3 *)
Definition input_list_example_3 : input_list :=
  {|
    value := [201; 101; 101; 200];
    constraints := ltac:(valid_input_list_tactic 1 100 100)
  |}.

Example restore_a_b_c_example_3: restore_a_b_c(input_list_example_3) = [100; 100; 1].
Proof.
  reflexivity.
Qed.

(* Prove the algorithm *)

Definition is_answer_valid(l : input_list): Prop :=
  let answer := restore_a_b_c(l) in
  let a := (nth 3 answer 0) - (nth 0 answer 0) in
  let b := (nth 3 answer 0) - (nth 1 answer 0) in
  let c := (nth 3 answer 0) - (nth 2 answer 0) in
  let sums := [a+b; a+c; b+c; a+b+c] in
  length answer = Z.to_nat 3 
  /\ Permutation sums (value l).

Theorem solution_is_correct: forall input_l : input_list, is_answer_valid(input_l).
Proof.
  intro l'.
  destruct l' as [l H].
  unfold is_answer_valid.
  split.
  - reflexivity.
  -  
  
  
Qed.