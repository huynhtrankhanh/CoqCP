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

Lemma eq_sum_for_permutation (l1 l2 : list Z) :
  Permutation l1 l2 -> foldr Z.add 0 l1 = foldr Z.add 0 l2.
Proof.
  apply (foldr_permutation Z.eq Z.add 0).
  intros j1 a1 j2 a2 b.
  assert (H: (a1 + (a2 + b)) = (a2 + (a1 + b))).
  {
    lia.
  }
  auto.
Qed.

Lemma filter_permutation : forall (A : Type) (P : A -> bool) (l1 l2 : list A),
  Permutation l1 l2 -> Permutation (filter P l1) (filter P l2).
Proof.
  intros A P l1 l2 Hperm.
  rewrite Hperm.
  reflexivity.
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
Definition restore_a_b_c_aux(l : list Z): list Z :=
  let total := (foldr Z.add 0 l)/3 in
  let modified_l := map (fun x => total - x) l in
  filter (fun x => negb(x =? 0)) modified_l.

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

Example restore_a_b_c_example_1: restore_a_b_c(input_list_example_1) = [3; 1; 2].
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
  (length answer) = (Z.to_nat 3)
  /\
  let opt_a := answer !! Z.to_nat 0 in
  let opt_b := answer !! Z.to_nat 1 in
  let opt_c := answer !! Z.to_nat 2 in
  match opt_a, opt_b, opt_c with 
  | Some(a), Some(b), Some(c) =>
    let sums := [a+b; a+c; b+c; a+b+c] in
    Permutation sums (value l)
  | _, _, _ => False
  end.

Lemma sum_elements_lemma : forall (l : list Z) (a b c : Z),
  Permutation [a+b; a+c; b+c; a+b+c] l ->
  foldr Z.add 0 l = (a + b + c) * 3.
Proof.
  intros l a b c H.
  assert (H1: foldr Z.add 0 [a+b; a+c; b+c; a+b+c] = foldr Z.add 0 l).
  {
    apply eq_sum_for_permutation.
    assumption.
  }
  assert (H2: foldr Z.add 0 [a+b; a+c; b+c; a+b+c] = (a+b+c)*3).
  {
    simpl.
    lia.
  }
  lia.
Qed.

Lemma map_subtract_lemma: forall (l : list Z) (a b c : Z),
  (map (fun x => a+b+c - x) [a+b; a+c; b+c; a+b+c]) = [c;b;a;0].
Proof.
  intros l a b c.
  simpl.
  repeat (f_equal; try lia).
Qed.

Theorem solution_is_correct: forall input_l : input_list, is_answer_valid(input_l).
Proof.
  intro l'.
  destruct l' as [l H].
  destruct H as [H1 H2].
  destruct H2 as [a [b [c H2]]].
  destruct H2 as [H2 [H3 [H4 H5]]].
  unfold is_answer_valid.
  unfold restore_a_b_c.
  simpl.
  assert (Hfoldr: foldr Z.add 0 l = (a + b + c) * 3).
  {
    apply sum_elements_lemma.
    assumption.
  }
  unfold restore_a_b_c_aux.
  rewrite Hfoldr.
  clear Hfoldr.
  rewrite Z.div_mul.
  - assert (Hmap : Permutation [c;b;a;0] (map (fun x => a+b+c-x) l)).
    {
      rewrite <- map_subtract_lemma.
      - apply Permutation_map.
        assumption.
      - auto.
    }
    assert (Hfilter : (filter (fun x => negb(x =? 0)) [c;b;a;0]) = [c;b;a]).
    {
      assert (Hc : negb (c =? 0) = true).
      {
        destruct (c =? 0) eqn:E.
        - lia. 
        - simpl.
          lia.
      }
      assert (Hb : negb (b =? 0) = true).
      {
        destruct (b =? 0) eqn:E.
        - lia. 
        - simpl.
          lia.
      }
      assert (Ha : negb (a =? 0) = true).
      {
        destruct (a =? 0) eqn:E.
        - lia. 
        - simpl.
          lia.
      }
      unfold filter.
      simpl.
      rewrite Hc.
      simpl.
      unfold filter.
      simpl.
      rewrite Hb.
      simpl.
      unfold filter.
      simpl.
      rewrite Ha.
      reflexivity.      
    }
    split.
    + rewrite <- Hmap.
      rewrite Hfilter.
      reflexivity.
    + rewrite <- Hmap.
    rewrite filter_permutation.
    
  apply (Permutation_map (fun x => a+b+c -x) H5 ).
    apply map_subtract_lemma.
  unfold restore_a_b_c_aux.
  
  
Qed.