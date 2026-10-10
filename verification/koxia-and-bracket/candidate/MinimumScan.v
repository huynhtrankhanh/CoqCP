From CoqCP Require Import Options Imperative Execution.
From Submission Require Import KoxiaInput KoxiaIntegers.
From Generated Require Import KoxiaAndBracket.
Require Trusted.Spec Submission.SpecProperties Submission.OptimalSplit Submission.FullCounting.
From Stdlib Require Import Lists.List Bool.Bool ZArith.ZArith Arith.PeanoNat Lia.
From stdpp Require Import numbers.
Import ListNotations Trusted.Spec Submission.SpecProperties Submission.OptimalSplit.
Local Open Scope Z_scope.

(* Compute closed unary bounds once with the original VM. Ordinary conversion
   at each [change] traverses the entire half-million-successor numeral. *)
Lemma input_capacity_integer : Z.of_nat 500000 = 500000.
Proof. vm_compute. reflexivity. Qed.
Lemma input_fuel_integer : Z.of_nat 500001 = 500001.
Proof. vm_compute. reflexivity. Qed.

Record MinimumState := {
  currentBalance : Z;
  currentMinimum : Z;
  selectedIndex : nat;
  consumed : nat
}.
Definition initialMinimumState := {| currentBalance := 0; currentMinimum := 0; selectedIndex := 0; consumed := 0 |}.
Definition minimumStep state ch :=
  let next := currentBalance state + delta ch in
  if Z.ltb next (currentMinimum state)
  then {| currentBalance := next; currentMinimum := next;
          selectedIndex := S (consumed state); consumed := S (consumed state) |}
  else {| currentBalance := next; currentMinimum := currentMinimum state;
          selectedIndex := selectedIndex state; consumed := S (consumed state) |}.
Fixpoint minimumScan s state :=
  match s with [] => state | ch :: s => minimumScan s (minimumStep state ch) end.
Definition minimumInvariant s state :=
  currentBalance state = balance s /\ consumed state = length s /\
  (selectedIndex state <= length s)%nat /\
  balance (firstn (selectedIndex state) s) = currentMinimum state /\
  forall i, (i <= length s)%nat -> currentMinimum state <= balance (firstn i s).

Lemma firstn_app_prefix {A} i (a b : list A) : (i <= length a)%nat -> firstn i (a++b)=firstn i a.
Proof.
  intro bound. rewrite firstn_app. replace (i-length a)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Lemma minimumInvariant_initial : minimumInvariant [] initialMinimumState.
Proof. unfold minimumInvariant, initialMinimumState; cbn. repeat split; intros; rewrite ?firstn_nil; cbn [balance]; lia. Qed.

Lemma minimumInvariant_step prefix state ch : minimumInvariant prefix state ->
  minimumInvariant (prefix ++ [ch]) (minimumStep state ch).
Proof.
  intros [level [count [selected [attained minimal]]]].
  assert (whole : length (prefix++[ch]) = S (length prefix)) by (rewrite length_app; cbn; lia).
  assert (total : balance (prefix++[ch]) = currentBalance state + delta ch).
  { rewrite balance_app, level. cbn [balance delta]. destruct ch; cbn; lia. }
  unfold minimumStep, minimumInvariant. destruct (Z.ltb (currentBalance state+delta ch) (currentMinimum state)) eqn:lower;
    cbn [currentBalance currentMinimum selectedIndex consumed].
  - apply Z.ltb_lt in lower. split; [exact (eq_sym total) |]. split; [lia |]. split; [lia |]. split.
    + rewrite count, <- whole, firstn_all. exact total.
    + intros i bound. destruct (le_dec i (length prefix)) as [before | after].
      * rewrite firstn_app_prefix by exact before. specialize (minimal i before). lia.
      * assert (last : i = length (prefix++[ch])) by lia. subst i. rewrite firstn_all. lia.
  - apply Z.ltb_ge in lower. split; [exact (eq_sym total) |]. split; [lia |]. split; [lia |]. split.
    + rewrite firstn_app_prefix by exact selected. exact attained.
    + intros i bound. destruct (le_dec i (length prefix)) as [before | after].
      * rewrite firstn_app_prefix by exact before. exact (minimal i before).
      * assert (last : i = length (prefix++[ch])) by lia. subst i. rewrite firstn_all. lia.
Qed.

Theorem minimumScan_invariant s prefix state : minimumInvariant prefix state ->
  minimumInvariant (prefix++s) (minimumScan s state).
Proof.
  induction s as [| ch s IH] in prefix,state |- *; cbn [minimumScan].
  - rewrite app_nil_r. auto.
  - intro invariant. replace (prefix++ch::s) with ((prefix++[ch])++s) by (rewrite <- app_assoc; reflexivity).
    apply IH, minimumInvariant_step. exact invariant.
Qed.
Definition globalMinimumState s := minimumScan s initialMinimumState.
Theorem globalMinimum_correct s : minimumInvariant s (globalMinimumState s).
Proof. exact (minimumScan_invariant s [] initialMinimumState minimumInvariant_initial). Qed.
Definition minimumIndex s := selectedIndex (globalMinimumState s).
Theorem minimumIndex_correct s :
  MinimumCut (firstn (minimumIndex s) s) (skipn (minimumIndex s) s).
Proof.
  intros i bound. rewrite firstn_skipn in bound. rewrite firstn_skipn.
  pose proof (globalMinimum_correct s) as [_ [_ [_ [attained minimal]]]].
  unfold minimumIndex. rewrite attained. apply minimal. exact bound.
Qed.

Theorem computed_abstract_solver_correct s :
  Submission.FullCounting.abstractAnswer (firstn (minimumIndex s) s) (skipn (minimumIndex s) s) =
  Z.of_nat (answer s).
Proof.
  rewrite Submission.FullCounting.abstract_solver_correct by apply minimumIndex_correct.
  rewrite firstn_skipn. reflexivity.
Qed.

Definition stateInputNums state ch := inputNums (Z.of_nat (consumed state)) ch
  (coerceInt (currentBalance state) 64) (coerceInt (currentMinimum state) 64)
  (Z.of_nat (selectedIndex state)).

Lemma minimum_state_bounds prefix state : minimumInvariant prefix state ->
  (- Z.of_nat (length prefix) <= currentBalance state <= Z.of_nat (length prefix)) /\
  (- Z.of_nat (length prefix) <= currentMinimum state <= 0).
Proof.
  intros [level [_ [selected [attained minimal]]]].
  pose proof (balance_bounds prefix) as range.
  pose proof (balance_bounds (firstn (selectedIndex state) prefix)) as minrange.
  rewrite length_firstn, Nat.min_l in minrange by exact selected.
  specialize (minimal 0%nat ltac:(lia)). rewrite firstn_O in minimal. cbn [balance] in minimal. lia.
Qed.

Lemma inputNums_minimum_step prefix state (ch : bool) :
  minimumInvariant prefix state -> (length prefix < 500000)%nat ->
  nextInputNums (Z.of_nat (consumed state)) (if ch then 40 else 41)
    (coerceInt (currentBalance state) 64) (coerceInt (currentMinimum state) 64)
    (Z.of_nat (selectedIndex state)) = stateInputNums (minimumStep state ch) (if ch then 40 else 41).
Proof.
  intros invariant limit. pose proof (minimum_state_bounds prefix state invariant) as [levels minima].
  pose proof invariant as [_ [count _]].
  apply Nat2Z.inj_lt in limit. rewrite input_capacity_integer in limit.
  unfold nextInputNums, nextBalance, stateInputNums, minimumStep.
  assert (count_fit : coerceInt (Z.of_nat (consumed state)+1) 64 = Z.of_nat (S (consumed state))).
  { rewrite coerce64_small; [lia |]. change (0 <= Z.of_nat (consumed state)+1 < 18446744073709551616). lia. }
  rewrite count_fit. destruct ch; cbn [delta].
  - rewrite (bool_decide_true (40=40)) by reflexivity. rewrite coerce64_add.
    rewrite !signed64_coerce by (cbn; lia).
    destruct (Z.ltb (currentBalance state+1) (currentMinimum state)) eqn:lower.
    + apply Z.ltb_lt in lower. rewrite bool_decide_true by exact lower. reflexivity.
    + apply Z.ltb_ge in lower. rewrite bool_decide_false by lia. reflexivity.
  - rewrite (bool_decide_false (41=40)) by discriminate. rewrite coerce64_sub.
    rewrite !signed64_coerce by (cbn; lia).
    replace (currentBalance state + -1) with (currentBalance state-1) by lia.
    destruct (Z.ltb (currentBalance state-1) (currentMinimum state)) eqn:lower.
    + apply Z.ltb_lt in lower. rewrite bool_decide_true by exact lower. reflexivity.
    + apply Z.ltb_ge in lower. rewrite bool_decide_false by lia. reflexivity.
Qed.

Definition bracketBytes (s : list bool) := map (fun ch : bool => if ch then 40 else 41) s.
Lemma bracketBytes_valid s : Forall (fun ch => ch=40 \/ ch=41) (bracketBytes s).
Proof. induction s as [|ch s IH]; cbn [bracketBytes]; constructor; [destruct ch; auto|exact IH]. Qed.
Lemma bracketBytes_length s : length (bracketBytes s)=length s.
Proof. apply length_map. Qed.

Theorem scanInputNums_minimum s prefix state old : minimumInvariant prefix state ->
  (length prefix+length s <= 500000)%nat ->
  scanInputNums (bracketBytes s) (stateInputNums state old) =
    stateInputNums (minimumScan s state) 10.
Proof.
  induction s as [|ch s IH] in prefix,state,old |- *.
  - intros invariant limit. cbn [bracketBytes scanInputNums minimumScan].
    unfold stateInputNums. apply inputNums_ch.
  - intros invariant limit.
    change (scanInputNums (bracketBytes s)
      (nextInputNums (Z.of_nat (consumed state)) (if ch then 40 else 41)
        (coerceInt (currentBalance state) 64) (coerceInt (currentMinimum state) 64)
        (Z.of_nat (selectedIndex state))) =
      stateInputNums (minimumScan s (minimumStep state ch)) 10).
    apply Nat2Z.inj_le in limit. rewrite Nat2Z.inj_add, input_capacity_integer in limit.
    change (Z.of_nat (length prefix)+Z.of_nat (S (length s)) <= 500000) in limit.
    rewrite Nat2Z.inj_succ in limit.
    rewrite (inputNums_minimum_step prefix state ch invariant
      ltac:(apply Nat2Z.inj_lt; rewrite input_capacity_integer; lia)).
    apply (IH (prefix++[ch])).
    + apply minimumInvariant_step. exact invariant.
    + apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, length_app, Nat2Z.inj_add, input_capacity_integer.
      change (Z.of_nat (length prefix)+1+Z.of_nat (length s) <= 500000). lia.
Qed.

Theorem initial_scanInputNums s : (length s <= 500000)%nat ->
  scanInputNums (bracketBytes s) (inputNums 0 0 0 0 0) =
    stateInputNums (globalMinimumState s) 10.
Proof.
  intro limit. change (scanInputNums (bracketBytes s) (stateInputNums initialMinimumState 0) =
    stateInputNums (minimumScan s initialMinimumState) 10).
  apply (scanInputNums_minimum s [] initialMinimumState 0 minimumInvariant_initial). exact limit.
Qed.

Theorem inputAction_globalMinimum s state : (length s <= 500000)%nat ->
  stdin state=input s ->
  memory state arraydef_0__sequence=repeat 0 500000 ->
  exists final,
    exec (inputAction 500001 (inputNums 0 0 0 0 0)) state =
      Some (stateInputNums (globalMinimumState s) 10, final) /\
    stdin final=[] /\ stdout final=stdout state /\
    memory final arraydef_0__sequence=bracketBytes s++repeat 0 (500000-length s) /\
    (forall name, name<>arraydef_0__sequence -> memory final name=memory state name).
Proof.
  intros limit incoming storage.
  assert (fuel : (length (bracketBytes s)<500001)%nat).
  { rewrite bracketBytes_length. apply Nat2Z.inj_lt.
    rewrite input_fuel_integer.
    apply Nat2Z.inj_le in limit. rewrite input_capacity_integer in limit.
    change (Z.of_nat (length s)<500001). lia. }
  assert (width : Z.of_nat (length ([] : list Z)+length (bracketBytes s)) < 18446744073709551616).
  { rewrite bracketBytes_length. apply Nat2Z.inj_le in limit.
    rewrite input_capacity_integer in limit.
    change (Z.of_nat (length s)<18446744073709551616). lia. }
  destruct (inputAction_execution (bracketBytes s) 500001 [] 500000 (inputNums 0 0 0 0 0)
    state (bracketBytes_valid s) fuel ltac:(rewrite bracketBytes_length; exact limit)
    width eq_refl incoming storage) as [final [executed [empty [out [loaded other]]]]].
  exists final. rewrite initial_scanInputNums in executed by exact limit.
  split; [exact executed|]. repeat split; try assumption.
  rewrite bracketBytes_length in loaded. exact loaded.
Qed.
