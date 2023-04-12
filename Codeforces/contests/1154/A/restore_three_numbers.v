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

Record input_x : Type := {
    input_x_value : Z;
    input_x_constraints : 2 <= input_x_value <= 1000000000
}.

Definition valid_input_list(values : list Z) : Prop :=
  forall (fun x => 2 <= x <= 1000000000) values
  /\
  exists a : Z, 
  exists b : Z, 
  exists c : Z, 
  (a >= 1)
  /\ (b >= 1)
  /\ (c >= 1)
  /\ Permutation [a+b; a+c; b+c; a+b+c] values.

Record input_list : Type := {
    value : list Z;
    constraints : valid_input_list(value)
}.

(* Define the algorithm *)
Definition restore_a_b_c_aux(values : list Z) :=
  let s := merge_sort Z.le values in
  let a := (nth 3 s 0) - (nth 0 s 0) in
  let b := (nth 3 s 0) - (nth 1 s 0) in
  let c := (nth 3 s 0) - (nth 2 s 0) in
  [a; b; c].

Definition raw_list(values : input_list): list Z :=
  (map input_x_value (input_list_value values)).

Definition restore_a_b_c (values : input_list) : list Z :=
  restore_a_b_c_aux(raw_list values).

(* Test with input examples *)

(* Example 1 *)
Lemma input_list_example_1_constraints_proof : 
  valid_input_list [3; 6; 5; 4].
Proof.
  exists 2, 1, 3.
  repeat split; try lia.
  apply z_permutation_by_merge_sort.
  reflexivity.
Qed.

Definition input_list_example_1 : input_list :=
  {| input_list_value := [
    {|input_x_value:=3 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=6 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=5 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=4 ; input_x_constraints := ltac:(lia) |}
  ];
  input_list_constraints := input_list_example_1_constraints_proof
  |}.

Example restore_a_b_c_example_1: restore_a_b_c(input_list_example_1) = [3; 2; 1].
Proof.
  reflexivity.
Qed.

(* Example 2 *)
Lemma input_list_example_2_constraints_proof : 
  valid_input_list [40; 40; 40; 60].
Proof.
  exists 20, 20, 20.
  repeat split; try lia.
  apply z_permutation_by_merge_sort.
  reflexivity.
Qed.

Definition input_list_example_2 : input_list :=
  {| input_list_value := [
    {|input_x_value:=40 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=40 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=40 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=60 ; input_x_constraints := ltac:(lia) |}
  ];
  input_list_constraints := input_list_example_2_constraints_proof
  |}.

Example restore_a_b_c_example_2: restore_a_b_c(input_list_example_2) = [20; 20; 20].
Proof.
  reflexivity.
Qed.

(* Example 3 *)
Lemma input_list_example_3_constraints_proof : 
  valid_input_list [201; 101; 101; 200].
Proof.
  exists 1, 100, 100.
  repeat split; try lia.
  apply z_permutation_by_merge_sort.
  reflexivity.
Qed.

Definition input_list_example_3 : input_list :=
  {| input_list_value := [
    {|input_x_value:=201 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=101 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=101 ; input_x_constraints := ltac:(lia) |};
    {|input_x_value:=200 ; input_x_constraints := ltac:(lia) |}
  ];
  input_list_constraints := input_list_example_3_constraints_proof
  |}.

Example restore_a_b_c_example_3: restore_a_b_c(input_list_example_3) = [100; 100; 1].
Proof.
  reflexivity.
Qed.

(* Prove the algorithm *)

Definition is_answer_valid(values : input_list): Prop :=
  let answer := restore_a_b_c(values) in
  let a := (nth 3 answer 0) - (nth 0 answer 0) in
  let b := (nth 3 answer 0) - (nth 1 answer 0) in
  let c := (nth 3 answer 0) - (nth 2 answer 0) in
  let sums := [a+b; a+c; b+c; a+b+c] in
  length answer = Z.to_nat 3 
  /\ Permutation sums (map input_x_value (input_list_value values)).

Theorem solution_is_correct: forall input_l : input_list, is_answer_valid(input_l).
Proof.
  intro values.
  assert 
  
  
Qed.