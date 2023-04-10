From CoqCP Require Import Options.
From stdpp Require Import numbers.

(* Define general properties (move to shared file?)*)

Definition is_positive (x : nat) : Prop :=
  x >= 1.

(* Define the inputs *)
Record input_w : Type := {
  value : nat;
  constraints : 1 <= value <= 100
}.

(* Define the algorithm *)

Definition is_division_possible (total_weight : input_w): bool :=
  (4 <=? total_weight.(value)) && Nat.even total_weight.(value).

(* Test in example *)
Definition input_w_with_8_value : input_w :=
  {| value := 8;
     constraints := ltac:(lia)
  |}.

Example input_w_with_8_value_example: is_division_possible(input_w_with_8_value) = true.
Proof.
  reflexivity.
Qed.

(* Prove the algorithm *)

Definition valid_division (w1 w2 : nat) (total_weight : input_w) : Prop :=
  is_positive w1 
  /\ is_positive w2
  /\ Nat.Even w1
  /\ Nat.Even w2
  /\ ((w1 + w2) = (total_weight.(value))).

Theorem solution_is_correct: forall total_weight : input_w ,
 (is_division_possible total_weight
 <-> exists w1:nat, exists w2:nat, valid_division w1 w2 total_weight).
Proof.
  intro total_weight.
  split.
  - intro H.
    unfold is_division_possible in H.
    apply Is_true_eq_true in H.
    apply andb_prop in H.
    destruct H as [H1 H2].
    apply Nat.leb_le in H1.
    apply Nat.even_spec in H2.
    exists 2, (total_weight.(value)-2).
    unfold valid_division.
    split.
    * unfold is_positive.
      lia.
    * split.
      + unfold is_positive.
        lia.
      + split.
        ++ unfold Nat.Even.
           exists 1.
           lia.
        ++ split.
          ** destruct H2 as [k Hk].
              rewrite -> Hk.
              unfold Nat.Even.
              exists (k-1).
              lia.
          ** lia.
  - intro H.
    unfold is_division_possible.
    destruct H as [x H1].
    destruct H1 as [y H1'].
    destruct H1' as [P1 [P2 [P3 [P4 P5]]]].
    assert (Px: x>=2).
    {
      unfold is_positive in P1.
      destruct P3 as [k Hk].
      lia.
    }    
    assert (Py: y>=2).
    {
      unfold is_positive in P2.
      destruct P4 as [k Hk].
      lia.
    }
    assert (Psum: 4 <= x+y).
    {
      lia.
    }
    rewrite P5 in Psum.
    assert (Peven: Nat.Even(total_weight.(value))).
    {
      destruct P3 as [a Ha].
      destruct P4 as [b Hb].
      rewrite Ha in P5.
      rewrite Hb in P5.
      unfold Nat.Even.
      exists (a+b).
      lia.
    }
    apply Nat.leb_le in Psum.
    apply Nat.even_spec in Peven.
    assert (H: ((4 <=? value total_weight) &&
    Nat.even (value total_weight))=true).
    {
      apply andb_true_iff.
      split.
      - apply Psum.
      - apply Peven.
    }
    apply Is_true_true in H.
    exact H.
Qed.
