From stdpp Require Import numbers list.
From CoqCP Require Import RegularBracketString.

Fixpoint fillLeftToRight (withBlanks : list (option Bracket)) (toFill : list Bracket) : list (option Bracket) :=
  match withBlanks, toFill with
  | [], _ => []
  | (None :: tail), (toFill :: remaining) => Some toFill :: fillLeftToRight tail remaining
  | (None :: tail), [] => None :: fillLeftToRight tail []
  | (Some stuff :: tail), remaining => Some stuff :: fillLeftToRight tail remaining
  end.

Fixpoint stripOptions (toBeCoerced : list (option Bracket)) : list Bracket :=
  match toBeCoerced with
  | [] => []
  | None :: tail => BracketOpen :: stripOptions tail
  | Some stuff :: tail => stuff :: stripOptions tail
  end.

Definition possibleToFill (withBlanks : list (option Bracket)) := exists toFill, isBalanced (stripOptions (fillLeftToRight withBlanks toFill)).

#[export] Instance optionBracketEqualityDecidable : EqDecision (option Bracket).
Proof. solve_decision. Defined.

Definition possibleToFillBool (withBlanks : list (option Bracket)) :=
  let count := length withBlanks / 2 in
  let remainingOpenCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) in
  let remainingCloseCount := count - count_occ optionBracketEqualityDecidable withBlanks (Some BracketClose) in
  isBalancedBool (stripOptions (fillLeftToRight withBlanks (repeat BracketOpen remainingOpenCount ++ repeat BracketClose remainingCloseCount))).

Definition decideSymbol (withBlanks : list (option Bracket)) :=
  match bool_decide (count_occ optionBracketEqualityDecidable withBlanks (Some BracketOpen) < length withBlanks / 2) with
  | true => BracketOpen
  | false => BracketClose
  end.

Fixpoint fillSingle (withBlanks : list (option Bracket)) (symbol : Bracket) :=
  match withBlanks with
  | Some stuff :: tail => Some stuff :: fillSingle tail symbol
  | None :: tail => Some symbol :: tail
  | [] => []
  end.

Definition advance (withBlanks : list (option Bracket)) := fillSingle withBlanks (decideSymbol withBlanks).

Lemma advancingIsAlwaysOk (withBlanks : list (option Bracket)) : possibleToFill withBlanks -> possibleToFill (advance withBlanks).
Proof.
  (* dear the Coq community, I can't prove this *)
  (* can you help me out? pretty please with a cherry on top *)
Admitted.
