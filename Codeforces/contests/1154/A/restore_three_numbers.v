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
Definition restore_a_b_c_aux(l : list Z): option (list Z) :=
  let total := (foldr Z.add 0 l)/3 in
  let modified_l := map (fun x => total - x) l in
  let index_of_zero := list_find (fun x => x =? 0) modified_l in
  match index_of_zero with
  | Some (index, _) => Some(list_delete index modified_l)
  | None => None
  end.

Definition restore_a_b_c (l : input_list) : option(list Z) :=
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

Example restore_a_b_c_example_1: restore_a_b_c(input_list_example_1) = Some([3; 1; 2]).
Proof.
  reflexivity.
Qed.

(* Example 2 *)
Definition input_list_example_2 : input_list :=
  {|
    value := [40; 40; 40; 60];
    constraints := ltac:(valid_input_list_tactic 20 20 20)
  |}.

Example restore_a_b_c_example_2: restore_a_b_c(input_list_example_2) = Some([20; 20; 20]).
Proof.
  reflexivity.
Qed.

(* Example 3 *)
Definition input_list_example_3 : input_list :=
  {|
    value := [201; 101; 101; 200];
    constraints := ltac:(valid_input_list_tactic 1 100 100)
  |}.

Example restore_a_b_c_example_3: restore_a_b_c(input_list_example_3) = Some([100; 100; 1]).
Proof.
  reflexivity.
Qed.


(* Prove the algorithm *)

Definition is_answer_valid(l : input_list): Prop :=
  let opt_answer := restore_a_b_c(l) in
  match opt_answer with
  | None => False
  | Some (answer) =>
    if Nat.eqb (length answer) (Z.to_nat 3) then
      let opt_a := answer !! Z.to_nat 0 in
      let opt_b := answer !! Z.to_nat 1 in
      let opt_c := answer !! Z.to_nat 2 in
      match opt_a, opt_b, opt_c with 
      | Some(a), Some(b), Some(c) =>
        let sums := [a+b; a+c; b+c; a+b+c] in
        Permutation sums (value l)
      | _, _, _ => False
      end
    else False
  end.


Lemma sum_permutation (l1 l2 : list Z) :
  Permutation l1 l2 -> foldr Z.add 0 l1 = foldr Z.add 0 l2.
Proof.
  apply foldr_permutation.
Qed.




Lemma sum_elements_lemma : forall (l : list Z) (a b c : Z),
  Permutation [a+b; a+c; b+c; a+b+c] l ->
  foldr Z.add 0 l = 3 * (a + b + c).
Proof.
  intros l a b c H_permutation.
  assert (H_sum: foldr Z.add 0 [a+b; a+c; b+c; a+b+c] = 3 * (a + b + c)). {
    simpl.
    lia.
  }

  rewrite <- H_sum.
  apply Permutation_foldr_Z_add.
  assumption.
Qed.


Theorem solution_is_correct: forall input_l : input_list, is_answer_valid(input_l).
Proof.
  intro l'.
  destruct l' as [l H].
  destruct H as [H1 H2].
  destruct H2 as [a [b [c H2]]].
  unfold is_answer_valid.
  unfold restore_a_b_c.
  simpl.
  unfold restore_a_b_c_aux.
  
  
Qed.