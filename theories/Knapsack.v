From stdpp Require Import numbers list.
From CoqCP Require Import Options.

Fixpoint knapsack (l : list (nat * nat)) (limit : nat) :=
  match l with
  | [] => 0
  | (weight, value) :: tail =>
    if decide (limit < weight) then knapsack tail limit
    else knapsack tail limit `max` (value + knapsack tail (limit - weight))
  end.

Fixpoint knapsack_elements (l : list (nat * nat)) (limit : nat) : list (nat * nat) :=
  match l with
  | [] => []
  | (weight, value) :: tail =>
    if decide (limit < weight) then knapsack_elements tail limit
    else
      let without := knapsack_elements tail limit in
      let with_item := (weight, value) :: knapsack_elements tail (limit - weight) in
      if decide ((fold_right (fun x acc => snd x + acc) 0 without) < (fold_right (fun x acc => snd x + acc) 0 with_item))
      then with_item
      else without
  end.

Lemma knapsackElementsSublist (l : list (nat * nat)) (limit : nat) : sublist (knapsack_elements l limit) l.
Proof.
  revert limit.
  induction l as [| head tail IH]. { easy. }
  simpl. intro limit.
  simpl.
  destruct head as [weight value]. case_decide as h1.
  - apply sublist_cons. apply IH.
  - case_decide as h2.
    + apply sublist_skip. apply IH.
    + apply sublist_cons. apply IH.
Qed.

Lemma foldrSum9 (l : list (nat * nat)) (a b : nat) : fold_right (fun x acc => snd x + acc) 0 ((a, b) :: l) = b + fold_right (fun x acc => snd x + acc) 0 l.
Proof.
  unfold foldr. simpl. reflexivity.
Qed.

Lemma foldrSum11 (l : list (nat * nat)) (a b : nat) : fold_right (fun x acc => fst x + acc) 0 ((a, b) :: l) = a + fold_right (fun x acc => fst x + acc) 0 l.
Proof.
  unfold foldr. simpl. reflexivity.
Qed.

Lemma knapsackElementsSum (l : list (nat * nat)) (limit : nat) : fold_right (fun x acc => snd x + acc) 0 (knapsack_elements l limit) = knapsack l limit.
Proof.
  revert limit.
  induction l as [| head tail IH]. { easy. }
  destruct head as [weight value]. simpl.
  intro limit. case_decide as h1.
  - apply IH.
  - case_decide as h2.
    + rewrite !IH in h2. rewrite (ltac:(lia) : knapsack tail limit `max` (value + knapsack tail (limit - weight)) = value + knapsack tail (limit - weight)), foldrSum9, IH. reflexivity.
    + rewrite !IH in h2. rewrite (ltac:(lia) : knapsack tail limit `max` (value + knapsack tail (limit - weight)) = knapsack tail limit), IH. reflexivity.
Qed.

Lemma knapsackElementsLimit (l : list (nat * nat)) (limit : nat) : fold_right (fun x acc => fst x + acc) 0 (knapsack_elements l limit) <= limit.
Proof.
  revert limit. induction l as [| head tail IH].
  { simpl. lia. }
  intro limit. destruct head as [weight value].
  simpl. case_decide as h1. { apply IH. }
  case_decide as h2.
  { rewrite foldrSum11. pose proof IH (limit - weight). lia. }
  pose proof IH limit. lia.
Qed.

Definition isMaximum (x : nat) (predicate : nat -> Prop) := predicate x /\ ∀ y, predicate y → y ≤ x.

Lemma knapsackMax (l : list (nat * nat)) (limit : nat) : isMaximum (knapsack l limit) (fun x => exists choice, sublist choice l /\ fold_right (fun x acc => snd x + acc) 0 choice = x /\ fold_right (fun x acc => fst x + acc) 0 choice <= limit).
Proof.
  revert limit.
  induction l as [| head tail IH].
  { intro a. constructor.
    - exists []. simpl. constructor. { easy. } lia.
    - intros b c. destruct c as [choice [h1 [h2 h3]]].
      rewrite sublist_nil_r in h1. rewrite h1 in h2. simpl in h2. subst b.
      simpl. trivial. }
  intro limit. constructor.
  - exists (knapsack_elements (head :: tail) limit).
    constructor; [| constructor]; [apply knapsackElementsSublist | apply knapsackElementsSum | apply knapsackElementsLimit].
  - intros score h. destruct h as [l1 [hl [hs hS]]].
    destruct head as [weight value].
    simpl. case_decide as h1.
    + pose proof IH limit as [aa bb].
      rewrite sublist_cons_r in hl.
      destruct hl as [hl | hl].
      * exact (bb score (ex_intro _ l1 (conj hl (conj hs hS)))).
      * destruct hl as [l2 [hl hL]].
        rewrite hl, foldrSum11 in hS.
        lia.
    + rewrite sublist_cons_r in hl.
      destruct hl as [hl | hl].
      * pose proof IH limit as [aa bb].
        pose proof bb score (ex_intro _ l1 (conj hl (conj hs hS))). lia.
      * destruct hl as [l [hl hL]].
        pose proof IH (limit - weight) as [aa bb].
        rewrite hl, foldrSum9 in hs.
        rewrite hl, foldrSum11 in hS.
        epose proof bb (score - value) (ex_intro _ l (conj hL (conj _ _))). lia.
        Unshelve. { lia. } { lia. }
Qed.
