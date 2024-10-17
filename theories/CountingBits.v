Require Import List.
Require Import NArith.
Require Import Lia.
Import ListNotations.

Fixpoint to_binary_positive (n : positive) := match n with
  | xI a => to_binary_positive a ++ [true]
  | xO a => to_binary_positive a ++ [false]
  | xH => [true]
  end.

Definition to_binary_N (n : N) := match n with
  | N0 => [false]
  | Npos x => to_binary_positive x
  end.

(* Helper function to convert natural number to list of bools representing binary digits *)
Definition to_binary (n : nat) : list bool :=
  to_binary_N (N.of_nat n).

(* Definition of popcount (population count) *)
Fixpoint popcount (l : list bool) : nat :=
  match l with
  | [] => 0
  | true :: the_rest => 1 + popcount the_rest
  | false :: the_rest => popcount the_rest
  end.

(* Definition of total_popcount *)
Fixpoint total_popcount (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => total_popcount n' + popcount (to_binary n')
  end.

(* Hypothesis 1: H_even (placeholder proof) *)
Lemma H_even : forall n : nat, total_popcount (2 * n) = n + 2 * total_popcount n.
Proof.
  intro n. induction n as [| n IH]. { easy. }
  rewrite (ltac:(lia) : 2 * S n = S (S (2 * n))), !(ltac:(simpl; reflexivity) : total_popcount (S _) = _).
  unfold to_binary. rewrite Nat2N.inj_double, Nat2N.inj_succ_double. unfold N.double. unfold N.succ_double.
  remember (N.of_nat n) as x eqn:hX. symmetry in hX. destruct x as [| x].
  - rewrite IH.
    assert (h : n = 0). { destruct n. { reflexivity. } cbv in hX. easy. }
    subst n. easy.
  - rewrite IH. unfold to_binary_N. rewrite (ltac:(simpl; reflexivity) : to_binary_positive x~0 = _). rewrite (ltac:(simpl; reflexivity) : to_binary_positive x~1 = _).
    assert (h1 : forall v, popcount (v ++ [false]) = popcount v).
    { clear. intro v. induction v as [| head tail IH]. { easy. }
      simpl. rewrite IH. reflexivity. }
    rewrite h1.
    assert (h2 : forall v, popcount (v ++ [true]) = S (popcount v)).
    { clear. intro v. induction v as [| head tail IH]. { easy. }
      simpl. rewrite IH. destruct head; lia. }
    rewrite h2. lia.
Qed.

(* Hypothesis 2: H_odd (placeholder proof) *)
Lemma H_odd : forall n : nat, total_popcount (2 * n + 1) = total_popcount (2 * n) + popcount (to_binary (2 * n)).
Proof.
  intro n. rewrite (ltac:(lia) : 2 * n + 1 = S (2 * n)). easy.
Qed.
