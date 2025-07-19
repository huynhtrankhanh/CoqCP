-- Knapsack problem implementation and properties in Lean 4
-- Translated from Coq

import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

-- Basic function definitions
def knapsack : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (weight, value) :: tail, limit =>
    if limit < weight then
      knapsack tail limit
    else
      max (knapsack tail limit) (value + knapsack tail (limit - weight))

def knapsack_elements : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | (weight, value) :: tail, limit =>
    if limit < weight then
      knapsack_elements tail limit
    else
      let without := knapsack_elements tail limit
      let with_item := (weight, value) :: knapsack_elements tail (limit - weight)
      if (without.foldr (fun x acc => x.2 + acc) 0) < (with_item.foldr (fun x acc => x.2 + acc) 0) then
        with_item
      else
        without

-- Lemma: knapsack_elements always returns a sublist of the input
theorem knapsackElementsSublist : ∀ (l : List (Nat × Nat)) (limit : Nat), List.Sublist (knapsack_elements l limit) l
  | [], _ => by simp [knapsack_elements]
  | head :: tail, limit => by
    unfold knapsack_elements
    obtain ⟨weight, value⟩ := head
    by_cases h1 : limit < weight
    · rw [if_pos h1]
      exact List.Sublist.cons (weight, value) (knapsackElementsSublist tail limit)
    · rw [if_neg h1]
      let without := knapsack_elements tail limit
      let with_item := (weight, value) :: knapsack_elements tail (limit - weight)
      by_cases h2 : without.foldr (fun x acc => x.2 + acc) 0 < with_item.foldr (fun x acc => x.2 + acc) 0
      · -- Choose with_item
        rw [if_pos h2]
        exact List.Sublist.cons₂ (weight, value) (knapsackElementsSublist tail (limit - weight))
      · -- Choose without
        rw [if_neg h2]
        exact List.Sublist.cons (weight, value) (knapsackElementsSublist tail limit)

-- Helper lemmas for foldr with snd and fst projections
theorem foldrSum9 (l : List (Nat × Nat)) (a b : Nat) :
  List.foldr (fun x acc => x.2 + acc) 0 ((a, b) :: l) = b + List.foldr (fun x acc => x.2 + acc) 0 l := by
  simp [List.foldr]

theorem foldrSum11 (l : List (Nat × Nat)) (a b : Nat) :
  List.foldr (fun x acc => x.1 + acc) 0 ((a, b) :: l) = a + List.foldr (fun x acc => x.1 + acc) 0 l := by
  simp [List.foldr]

-- Lemma: sum of values in knapsack_elements equals knapsack value
theorem knapsackElementsSum : ∀ (l : List (Nat × Nat)) (limit : Nat),
  List.foldr (fun x acc => x.2 + acc) 0 (knapsack_elements l limit) = knapsack l limit
  | [], _ => by simp [knapsack_elements, knapsack]
  | head :: tail, limit => by
    unfold knapsack_elements knapsack
    obtain ⟨weight, value⟩ := head
    by_cases h1 : limit < weight
    · rw [if_pos h1, if_pos h1]
      exact knapsackElementsSum tail limit
    · rw [if_neg h1, if_neg h1]
      let without := knapsack_elements tail limit
      let with_item := (weight, value) :: knapsack_elements tail (limit - weight)
      have ih1 := knapsackElementsSum tail limit
      have ih2 := knapsackElementsSum tail (limit - weight)
      by_cases h2 : without.foldr (fun x acc => x.2 + acc) 0 < with_item.foldr (fun x acc => x.2 + acc) 0
      · rw [if_pos h2]
        rw [foldrSum9, ih2]
        rw [ih1] at h2
        rw [foldrSum9, ih2] at h2
        simp only [Prod.snd, Prod.fst]
        rw [max_def]
        rw [if_pos (Nat.le_of_lt h2)]
      · rw [if_neg h2]
        rw [ih1]
        push_neg at h2
        rw [ih1, foldrSum9, ih2] at h2
        simp only [Prod.snd, Prod.fst]
        exact (max_eq_left h2).symm

-- Lemma: sum of weights in knapsack_elements is within limit
theorem knapsackElementsLimit : ∀ (l : List (Nat × Nat)) (limit : Nat),
  List.foldr (fun x acc => x.1 + acc) 0 (knapsack_elements l limit) ≤ limit
  | [], _ => by simp [knapsack_elements]
  | head :: tail, limit => by
    unfold knapsack_elements
    obtain ⟨weight, value⟩ := head
    by_cases h1 : limit < weight
    · rw [if_pos h1]
      exact knapsackElementsLimit tail limit
    · rw [if_neg h1]
      let without := knapsack_elements tail limit
      let with_item := (weight, value) :: knapsack_elements tail (limit - weight)
      by_cases h2 : without.foldr (fun x acc => x.2 + acc) 0 < with_item.foldr (fun x acc => x.2 + acc) 0
      · rw [if_pos h2]
        rw [foldrSum11]
        have ih := knapsackElementsLimit tail (limit - weight)
        have hle : weight ≤ limit := Nat.le_of_not_lt h1
        simp only [Prod.fst]
        have h_sub : weight + (limit - weight) = limit := Nat.add_sub_cancel' hle
        linarith [ih, h_sub]
      · rw [if_neg h2]
        exact knapsackElementsLimit tail limit

-- Definition of maximum with respect to a predicate
def isMaximum (x : Nat) (predicate : Nat → Prop) : Prop :=
  predicate x ∧ ∀ y, predicate y → y ≤ x

-- Main theorem: knapsack value is maximum among all valid choices
theorem knapsackMax (l : List (Nat × Nat)) (limit : Nat) :
  isMaximum (knapsack l limit) (fun val => ∃ choice,
    List.Sublist choice l ∧
    List.foldr (fun item acc => item.2 + acc) 0 choice = val ∧
    List.foldr (fun item acc => item.1 + acc) 0 choice ≤ limit) := by
  constructor
  · -- Show that knapsack value satisfies the predicate
    use knapsack_elements l limit
    constructor
    · exact knapsackElementsSublist l limit
    constructor
    · exact knapsackElementsSum l limit
    · exact knapsackElementsLimit l limit
  · -- Show that knapsack value is maximal
    intro score h
    obtain ⟨choice, hsublist, hsum, hlimit⟩ := h
    rw [← hsum]
    -- Use strong induction on the list structure
    revert limit score choice hsublist hsum hlimit
    induction l with
    | nil =>
      -- Base case: empty list
      intro limit score choice hsublist hsum hlimit
      -- Any sublist of [] must be []
      have hchoice_nil : choice = [] := List.eq_nil_of_sublist_nil hsublist
      rw [hchoice_nil] at hsum
      -- List.foldr on empty list is 0
      have foldr_nil : List.foldr (fun x acc => x.2 + acc) 0 ([] : List (ℕ × ℕ)) = 0 := by rfl
      rw [foldr_nil] at hsum
      -- So score = 0
      have score_zero : score = 0 := hsum.symm

      rw [hchoice_nil]
      -- knapsack [] limit = 0
      have knapsack_nil : knapsack [] limit = 0 := by rfl
      rw [knapsack_nil]; simp
    | cons head tail ih =>
      intro limit score choice hsublist hsum hlimit
      obtain ⟨weight, value⟩ := head
      simp only [knapsack]
      by_cases h1 : limit < weight
      · -- Case: limit < weight, so we skip this item
        rw [if_pos h1]
        -- Any valid choice from head::tail either doesn't include head, or does include head
        rw [List.sublist_cons_iff] at hsublist
        cases hsublist with
        | inl h_tail =>
          -- Choice doesn't include head, so it's a valid choice from tail
          exact ih limit score choice h_tail hsum hlimit
        | inr h_head =>
          -- Choice includes head
          obtain ⟨r, hchoice_eq, hr_sublist⟩ := h_head
          rw [hchoice_eq] at hsum hlimit
          rw [foldrSum9] at hsum
          rw [foldrSum11] at hlimit
          -- But head has weight > limit, so this choice violates weight constraint
          -- hlimit says weight + List.foldr (fun x acc => x.1 + acc) 0 r ≤ limit
          -- But we know weight > limit, so weight + r_weight > limit, contradiction
          have weight_too_big : weight > limit := h1
          have : weight ≤ weight + List.foldr (fun x acc => x.1 + acc) 0 r := Nat.le_add_right _ _
          linarith [this, hlimit, weight_too_big]
      · -- Case: limit ≥ weight, so we have two choices
        rw [if_neg h1]
        -- Apply the inductive hypothesis appropriately
        rw [List.sublist_cons_iff] at hsublist
        cases hsublist with
        | inl h_tail =>
          -- Choice doesn't include head
          have ih_applied := ih limit score choice h_tail hsum hlimit
          -- knapsack tail limit ≤ max (knapsack tail limit) (value + knapsack tail (limit - weight))
          exact Nat.le_trans ih_applied (Nat.le_max_left _ _)
        | inr h_head =>
          -- Choice includes head
          obtain ⟨r, hchoice_eq, hr_sublist⟩ := h_head
          rw [hchoice_eq] at hsum hlimit
          rw [foldrSum9] at hsum
          rw [foldrSum11] at hlimit
          -- Now score = value + (sum of values in r)
          -- and weight + (sum of weights in r) ≤ limit
          -- So sum of weights in r ≤ limit - weight
          have r_weight_bound : List.foldr (fun x acc => x.1 + acc) 0 r ≤ limit - weight := by
            have hle : weight ≤ limit := Nat.le_of_not_lt h1
            -- hlimit: weight + r_weight ≤ limit, so r_weight ≤ limit - weight
            have h_add_sub : weight + (limit - weight) = limit := Nat.add_sub_cancel' hle
            linarith [hlimit, h_add_sub]
          -- Apply inductive hypothesis to r with reduced limit
          have r_foldr_eq : List.foldr (fun x acc => x.2 + acc) 0 r = score - value := by
            -- hsum: value + r_value = score, so r_value = score - value
            have h_score_eq : value + List.foldr (fun x acc => x.2 + acc) 0 r = score := hsum
            omega
          have ih_applied := ih (limit - weight) (score - value) r hr_sublist r_foldr_eq r_weight_bound
          -- Now score ≤ value + knapsack tail (limit - weight)
          have score_bound : List.foldr (fun x acc => x.2 + acc) 0 choice ≤ value + knapsack tail (limit - weight) := by
            rw [hchoice_eq, foldrSum9]
            have h_r_bound : List.foldr (fun x acc => x.2 + acc) 0 r ≤ knapsack tail (limit - weight) := ih_applied
            linarith [h_r_bound]
          -- value + knapsack tail (limit - weight) ≤ max (knapsack tail limit) (value + knapsack tail (limit - weight))
          exact Nat.le_trans score_bound (Nat.le_max_right _ _)
