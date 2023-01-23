From stdpp Require Import numbers list.
From CoqCP Require Import RegularBracketString.

Fixpoint fillLeftToRight (withBlanks : list (option Bracket)) (toFill : list Bracket) : list Bracket :=
  match withBlanks, toFill with
  | [], _ => []
  | (None :: tail), (toFill :: remaining) => toFill :: fillLeftToRight tail remaining
  | (None :: tail), [] => [BracketClose]
  | (Some stuff :: tail), remaining => stuff :: fillLeftToRight tail remaining
  end.

Definition possibleToFill (withBlanks : list (option Bracket)) := exists toFill, isBalanced (fillLeftToRight withBlanks toFill).

#[export] Instance optionBracketEqualityDecidable : EqDecision (option Bracket).
Proof. solve_decision. Defined.

Definition possibleToFillBool (withBlanks : list (option Bracket)) :=
  let count := length withBlanks / 2 in
  let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
  let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
  isBalancedBool (fillLeftToRight withBlanks (repeat BracketOpen remainingOpenCount ++ repeat BracketClose remainingCloseCount)).

Lemma possibleToFillIffPossibleToFillBool (withBlanks : list (option Bracket)) : possibleToFill withBlanks <-> possibleToFillBool withBlanks.
Proof.
  (* dear the Coq community, I can't prove this *)
  (* can you help me out? pretty please with a cherry on top *)
Admitted.
