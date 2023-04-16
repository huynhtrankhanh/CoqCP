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

(* Define the inputs *)

Definition valid_input_list(l : list Z) (a b c : Z) : Prop :=
  (forall x, In x l -> 2 <= x <= 1000000000)
  /\ (a >= 1)
  /\ (b >= 1)
  /\ (c >= 1)
  /\ Permutation [a + b; a + c; b + c; a + b + c] l.

Record input_list : Type := {
    value : list Z;
    inner_a : Z;
    inner_b : Z;
    inner_c : Z;
    constraints : valid_input_list value inner_a inner_b inner_c
}.

(* Define the algorithm *)
Definition restore_a_b_c_aux(l : list Z): list Z :=
  let total := (foldr Z.add 0 l) / 3 in
  let modified_l := map (fun x => total - x) l in
  filter (fun x => negb(x =? 0)) modified_l.

Definition restore_a_b_c (l : input_list) : list Z :=
  restore_a_b_c_aux(value l).

(* Test with input examples *)

Ltac valid_input_list_tactic :=
  unfold valid_input_list;
  split;
  [ intros x H;
    repeat (destruct H as [H1 | H]; try lia);
    contradiction
  | repeat (split; try lia);
    apply z_permutation_by_merge_sort;
    reflexivity
  ].

(* Example 1 *)

Definition input_list_example_1 : input_list :=
  {|
    value := [3; 6; 5; 4];
    inner_a := 2;
    inner_b := 1;
    inner_c := 3;
    constraints := ltac:(valid_input_list_tactic)
  |}.

Example restore_a_b_c_example_1: restore_a_b_c(input_list_example_1) = [3; 1; 2].
Proof.
  reflexivity.
Qed.

(* Example 2 *)
Definition input_list_example_2 : input_list :=
  {|
    value := [40; 40; 40; 60];
    inner_a := 20;
    inner_b := 20;
    inner_c := 20;
    constraints := ltac:(valid_input_list_tactic)
  |}.

Example restore_a_b_c_example_2: restore_a_b_c(input_list_example_2) = [20; 20; 20].
Proof.
  reflexivity.
Qed.

(* Example 3 *)
Definition input_list_example_3 : input_list :=
  {|
    value := [201; 101; 101; 200];
    inner_a := 1;
    inner_b := 100;
    inner_c := 100;
    constraints := ltac:(valid_input_list_tactic)
  |}.

Example restore_a_b_c_example_3: restore_a_b_c(input_list_example_3) = [100; 100; 1].
Proof.
  reflexivity.
Qed.

(* Prove the algorithm *)

Definition is_answer_valid(l : input_list): Prop :=
  let a := inner_a l in
  let b := inner_b l in
  let c := inner_c l in
  (* This condition is sufficient but it not proven to be necessary
  (although it is, we don't need to prove it)*)
  Permutation (restore_a_b_c l) [a; b; c].

Lemma sum_elements_lemma : forall (l : list Z) (a b c : Z),
  Permutation [a + b; a + c; b + c; a + b + c] l ->
  foldr Z.add 0 l = (a + b + c) * 3.
Proof.
  intros l a b c H.
  assert (H1: foldr Z.add 0 [a + b; a + c; b + c; a + b + c] = foldr Z.add 0 l).
  {
    apply eq_sum_for_permutation.
    assumption.
  }
  assert (H2: foldr Z.add 0 [a + b; a + c; b + c; a + b + c] = (a + b + c) * 3).
  {
    simpl.
    lia.
  }
  lia.
Qed.

Lemma map_subtract_lemma: forall (l : list Z) (a b c : Z),
  (map (fun x => a + b + c - x) [a + b; a + c; b + c; a + b + c]) = [c; b; a; 0].
Proof.
  intros l a b c.
  simpl.
  repeat (f_equal; try lia).
Qed.

Theorem solution_is_correct: forall input_l : input_list, is_answer_valid(input_l).
Proof.
  intro l'.
  destruct l' as [l a b c H].
  destruct H as [H1 [H2 [H3 [H4 H5]]]].
  unfold is_answer_valid.
  simpl.
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
  - assert (Hmap : Permutation [c;b;a;0] (map (fun x => a + b + c - x) l)).
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
    rewrite <- Hmap.
    rewrite Hfilter.
    apply Permutation_rev.
  - lia.
Qed.