From CoqCP Require Import Options KoxiaPolynomial.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat Lia
  Logic.FunctionalExtensionality.
Import ListNotations.
Local Open Scope nat_scope.

(* Every occurrence in this list represents one history of keep/delete
   choices, rather than one distinct resulting state. Duplicates must count. *)
Definition nextStates (special : bool) (height : nat) : list nat :=
  if special then
    match height with O => [0] | S h => [h; S h] end
  else [height; S height].

Definition advanceStates (special : bool) (states : list nat) : list nat :=
  flat_map (nextStates special) states.

Fixpoint pathStates (events : list bool) (states : list nat) : list nat :=
  match events with
  | [] => states
  | special :: events => pathStates events (advanceStates special states)
  end.

Definition indicator (x y : nat) : nat := if Nat.eq_dec x y then 1 else 0.
Definition occurrences (states : list nat) (height : nat) : nat :=
  count_occ Nat.eq_dec states height.

Lemma nextStates_special h j : occurrences (nextStates true h) j =
  indicator h j + indicator h (S j).
Proof.
  unfold occurrences, nextStates, indicator. destruct h as [| h]; destruct j as [| j];
    cbn -[Nat.eq_dec].
  all: repeat match goal with |- context[Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y) end;
    lia.
Qed.

Lemma nextStates_ordinary_zero h : occurrences (nextStates false h) 0 = indicator h 0.
Proof.
  unfold occurrences, nextStates, indicator. cbn -[Nat.eq_dec].
  repeat match goal with |- context[Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y) end; lia.
Qed.

Lemma nextStates_ordinary_positive h j : occurrences (nextStates false h) (S j) =
  indicator h (S j) + indicator h j.
Proof.
  unfold occurrences, nextStates, indicator. cbn -[Nat.eq_dec].
  repeat match goal with |- context[Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y) end; lia.
Qed.

Lemma occurrences_cons h states j : occurrences (h :: states) j =
  indicator h j + occurrences states j.
Proof.
  unfold occurrences, indicator. cbn -[Nat.eq_dec]. destruct (Nat.eq_dec h j); lia.
Qed.

Lemma advance_special states j : occurrences (advanceStates true states) j =
  occurrences states j + occurrences states (S j).
Proof.
  induction states as [| h states IH]; [reflexivity |].
  unfold advanceStates in *. cbn [flat_map].
  unfold occurrences at 1. rewrite count_occ_app. fold (occurrences (nextStates true h) j).
  fold (occurrences (flat_map (nextStates true) states) j).
  rewrite nextStates_special, IH, !occurrences_cons. lia.
Qed.

Lemma advance_ordinary_zero states : occurrences (advanceStates false states) 0 =
  occurrences states 0.
Proof.
  induction states as [| h states IH]; [reflexivity |].
  unfold advanceStates in *. cbn [flat_map].
  unfold occurrences at 1. rewrite count_occ_app. fold (occurrences (nextStates false h) 0).
  fold (occurrences (flat_map (nextStates false) states) 0).
  rewrite nextStates_ordinary_zero, IH, occurrences_cons. lia.
Qed.

Lemma advance_ordinary_positive states j : occurrences (advanceStates false states) (S j) =
  occurrences states (S j) + occurrences states j.
Proof.
  induction states as [| h states IH]; [reflexivity |].
  unfold advanceStates in *. cbn [flat_map].
  unfold occurrences at 1. rewrite count_occ_app. fold (occurrences (nextStates false h) (S j)).
  fold (occurrences (flat_map (nextStates false) states) (S j)).
  rewrite nextStates_ordinary_positive, IH, !occurrences_cons. lia.
Qed.

Local Open Scope Z_scope.
Definition pathCoefficients (states : list nat) : Coefficients :=
  fun j => if j <? 0 then 0 else Z.of_nat (occurrences states (Z.to_nat j)).

Lemma pathCoefficients_negative states j : j < 0 -> pathCoefficients states j = 0.
Proof. intro h. unfold pathCoefficients. apply Z.ltb_lt in h. rewrite h. reflexivity. Qed.
Lemma pathCoefficients_nonnegative states j : 0 <= j ->
  pathCoefficients states j = Z.of_nat (occurrences states (Z.to_nat j)).
Proof. intro h. unfold pathCoefficients. apply Z.ltb_ge in h. rewrite h. reflexivity. Qed.

Lemma advance_coefficients special states :
  pathCoefficients (advanceStates special states) = boundaryStep special (pathCoefficients states).
Proof.
  apply functional_extensionality. intro j.
  unfold boundaryStep. destruct (j <? 0) eqn:hj.
  - apply pathCoefficients_negative. apply Z.ltb_lt. exact hj.
  - apply Z.ltb_ge in hj. rewrite pathCoefficients_nonnegative by exact hj.
    unfold unrestrictedStep. destruct special.
    + rewrite !pathCoefficients_nonnegative by lia. rewrite advance_special.
      rewrite Nat2Z.inj_add. replace (Z.to_nat (j+1)) with (S (Z.to_nat j)) by lia.
      reflexivity.
    + destruct (Z.eq_dec j 0) as [zero | positive].
      * subst j. rewrite pathCoefficients_nonnegative by lia.
        rewrite pathCoefficients_negative by lia. rewrite Z.add_0_r.
        cbn [Z.to_nat]. rewrite advance_ordinary_zero. reflexivity.
      * rewrite !pathCoefficients_nonnegative by lia.
        replace (Z.to_nat j) with (S (Z.to_nat (j-1))) by lia.
        rewrite advance_ordinary_positive, Nat2Z.inj_add. reflexivity.
Qed.

Theorem run_counts_paths events states :
  run events (pathCoefficients states) = pathCoefficients (pathStates events states).
Proof.
  induction events as [| b events IH] in states |- *; [reflexivity |].
  cbn [run pathStates]. rewrite <- advance_coefficients. apply IH.
Qed.

Theorem accelerated_counts_paths tree states :
  accelerated tree (pathCoefficients states) = pathCoefficients (pathStates (treeEvents tree) states).
Proof. rewrite accelerated_correct, run_counts_paths. reflexivity. Qed.

Theorem modular_counts_paths events modulus states : modulus <> 0 ->
  modularRun modulus events (pathCoefficients states) 0 =
  (Z.of_nat (occurrences (pathStates events states) 0) mod modulus).
Proof.
  intro hm. rewrite modularRun_correct by exact hm. rewrite run_counts_paths.
  unfold reduce. rewrite pathCoefficients_nonnegative by lia. reflexivity.
Qed.

Local Open Scope nat_scope.

(* Independently scan the retained balance when every opening bracket is
   kept, and every closing bracket offers keep/delete choices. *)
Definition closeChoices (height : nat) : list nat :=
  match height with O => [0] | S h => [h; S h] end.
Definition bracketAdvance (opening : bool) (heights : list nat) : list nat :=
  if opening then map S heights else flat_map closeChoices heights.
Fixpoint bracketPaths (s : list bool) (heights : list nat) : list nat :=
  match s with
  | [] => heights
  | opening :: s => bracketPaths s (bracketAdvance opening heights)
  end.

(* The greedy retained balance supplies the moving coordinate origin. *)
Fixpoint eventsFrom (s : list bool) (height : nat) : list bool :=
  match s with
  | [] => []
  | true :: s => eventsFrom s (S height)
  | false :: s =>
      match height with
      | O => true :: eventsFrom s 0
      | S h => false :: eventsFrom s h
      end
  end.
Fixpoint greedyHeight (s : list bool) (height : nat) : nat :=
  match s with
  | [] => height
  | true :: s => greedyHeight s (S height)
  | false :: s =>
      match height with O => greedyHeight s 0 | S h => greedyHeight s h end
  end.

Lemma bracketAdvance_open origin states :
  bracketAdvance true (map (Nat.add origin) states) = map (Nat.add (S origin)) states.
Proof.
  unfold bracketAdvance. rewrite map_map. apply map_ext. intro h. lia.
Qed.

Lemma closeChoices_origin_zero h : closeChoices h = nextStates true h.
Proof. reflexivity. Qed.

Lemma closeChoices_origin_positive origin h :
  closeChoices (S origin + h) = map (Nat.add origin) (nextStates false h).
Proof.
  cbn [Nat.add closeChoices nextStates map].
  replace (origin + S h) with (S (origin+h)) by lia. reflexivity.
Qed.

Lemma bracketAdvance_close origin states :
  bracketAdvance false (map (Nat.add origin) states) =
  match origin with
  | O => advanceStates true states
  | S origin => map (Nat.add origin) (advanceStates false states)
  end.
Proof.
  destruct origin as [| origin].
  - change (flat_map closeChoices (map (Nat.add 0) states) = flat_map (nextStates true) states).
    replace (map (Nat.add 0) states) with states.
    + reflexivity.
    + symmetry. change (map (fun x : nat => x) states = states). apply map_id.
  - induction states as [| h states IH]; [reflexivity |].
    cbn [map bracketAdvance flat_map advanceStates] in *.
    rewrite closeChoices_origin_positive, map_app. rewrite IH. reflexivity.
Qed.

Theorem moving_origin_correct s origin states :
  bracketPaths s (map (Nat.add origin) states) =
  map (Nat.add (greedyHeight s origin)) (pathStates (eventsFrom s origin) states).
Proof.
  induction s as [| opening s IH] in origin, states |- *; [reflexivity |].
  cbn [bracketPaths]. destruct opening.
  - rewrite bracketAdvance_open. apply IH.
  - rewrite bracketAdvance_close. destruct origin as [| origin].
    + change (bracketPaths s (advanceStates true states) =
        map (Nat.add (greedyHeight s 0)) (pathStates (eventsFrom s 0) (advanceStates true states))).
      replace (advanceStates true states) with (map (Nat.add 0) (advanceStates true states)) at 1.
      * apply IH.
      * change (map (fun x : nat => x) (advanceStates true states) = advanceStates true states).
        apply map_id.
    + apply IH.
Qed.

Theorem half_count_correct s : greedyHeight s 0 = 0 ->
  run (eventsFrom s 0) (pathCoefficients [0]) 0%Z =
  Z.of_nat (occurrences (bracketPaths s [0]) 0).
Proof.
  intro hg. rewrite run_counts_paths, pathCoefficients_nonnegative by lia.
  cbn [Z.to_nat].
  pose proof (moving_origin_correct s 0 [0]) as same.
  rewrite hg in same. cbn [map Nat.add] in same.
  rewrite map_id in same.
  rewrite same. reflexivity.
Qed.
