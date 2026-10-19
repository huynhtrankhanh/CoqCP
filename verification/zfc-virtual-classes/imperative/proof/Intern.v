From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

Module InternExecution.
Import IndexExecution.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern)
  withLocalVariablesReturnValue R.

(* Select the scan from the generated definition, rather than substituting a
   handwritten loop for it. The count is the value read from metadata slot 1. *)
Definition after_count (count : Z) : LocalAction unit := ltac:(
  let code := eval cbn [funcdef_0__intern_body bind numberLocalSet retrieve] in funcdef_0__intern_body in
  lazymatch code with
  | Dispatch _ _ _ (NumberLocalSet _ _ _ _ _) ?after_set =>
    let code := eval cbn [bind] in (after_set tt) in
    lazymatch code with
    | Dispatch _ _ _ (DoWithArrays _ _ _ (Retrieve _ _ arraydef_0__meta 1%Z)) ?after_read =>
      exact (after_read count)
    end
  end).
Definition scan_body (count : Z) : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold after_count in (after_count count) in
  lazymatch code with loop _ ?body >>= _ => exact body end).
Definition after_scan : LocalAction unit := ltac:(
  let code := eval unfold after_count in (after_count 0%Z) in
  lazymatch code with loop _ _ >>= ?tail => exact (tail tt) end).

Lemma split_scan count :
  after_count count = (loop (Z.to_nat count) (scan_body count) >>= fun _ => after_scan).
Proof. reflexivity. Qed.

Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern.
Definition sought (f : Frame) :=
  (nums f vardef_0__intern_tag, nums f vardef_0__intern_a, nums f vardef_0__intern_b).
Definition found_frame (f : Frame) index :=
  setNum (setMachine f (store_meta (machine f) 0 (Z.of_nat index))) vardef_0__intern_found 1.

Theorem scan_step (f : Frame) count remaining index x y z :
  count - Z.of_nat remaining - 1 = Z.of_nat index ->
  (index < length (memory (machine f) arraydef_0__formulas))%nat ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) = (x,y,z) ->
  execLocal (scan_body count remaining) f =
    if bool_decide ((x,y,z) = sought f) then Some (Stop, found_frame f index)
    else Some (KeepGoing, f).
Proof.
  intros Hindex Hbound Hmeta Hentry. destruct f as [s bs ns].
  cbn [machine sought nums] in *.
  change (@List.nth (Z * Z * Z)%type index (memory s arraydef_0__formulas) (0,0,0) = (x,y,z)) in Hentry.
  destruct (Z.eq_dec x (ns vardef_0__intern_tag));
    destruct (Z.eq_dec y (ns vardef_0__intern_a));
    destruct (Z.eq_dec z (ns vardef_0__intern_b)).
  all: unfold scan_body; cbn zeta.
  all: replace (count - Z.of_nat remaining - 1) with (Z.of_nat index) by lia.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break
    execLocal localStep step optionBind fst snd nums machine setNum setMachine].
  all: repeat first [rewrite Nat2Z.id | rewrite nth_lt_default with (default := (0,0,0))
    | rewrite Hentry
    | match goal with |- context [bool_decide ?P] =>
        first [rewrite (bool_decide_true P) by congruence
          | rewrite (bool_decide_false P) by congruence]
      end
    | progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
        shortCircuitAnd retrieve numberLocalGet numberLocalSet store break
        execLocal localStep step optionBind fst snd nums bools machine setNum setMachine sought]
    | case_decide; [|lia]].
  all: unfold found_frame.
  all: reflexivity.
Qed.

Fixpoint find_from (f : Frame) start fuel : option nat :=
  match fuel with
  | 0%nat => None
  | S fuel => if bool_decide
      (List.nth start (memory (machine f) arraydef_0__formulas) (0,0,0) = sought f)
      then Some start else find_from f (S start) fuel
  end.

Theorem scan_loop (f : Frame) size start fuel :
  size = (start + fuel)%nat ->
  (size <= length (memory (machine f) arraydef_0__formulas))%nat ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocal (loop fuel (scan_body (Z.of_nat size))) f =
    match find_from f start fuel with
    | Some index => Some (tt, found_frame f index)
    | None => Some (tt, f)
    end.
Proof.
  induction fuel as [|fuel IH] in start |- *.
  - intros. reflexivity.
  - intros Hsize Hbound Hmeta. rewrite loop_S, execLocal_bind.
    destruct (List.nth start (memory (machine f) arraydef_0__formulas) (0,0,0))
      as [[x y] z] eqn:Hentry.
    rewrite (scan_step f (Z.of_nat size) fuel start x y z).
    2: rewrite Hsize, Nat2Z.inj_add, Nat2Z.inj_succ; lia.
    2: lia.
    2: exact Hmeta.
    2: exact Hentry.
    cbn [find_from]. rewrite Hentry.
    case_bool_decide as Hmatch.
    + rewrite bool_decide_true by exact Hmatch. reflexivity.
    + rewrite bool_decide_false by exact Hmatch.
      cbn [optionBind fst snd]. apply IH; try assumption. lia.
Qed.

Theorem find_from_sound f start fuel index : find_from f start fuel = Some index ->
  (start <= index < start + fuel)%nat /\
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) = sought f.
Proof.
  induction fuel as [|fuel IH] in start |- *; cbn [find_from]; [discriminate |].
  case_bool_decide as Heq.
  - intro H. injection H as <-. split; [lia | exact Heq].
  - intro H. destruct (IH _ H) as [Hrange Hnode]. split; [lia | exact Hnode].
Qed.

Theorem find_from_none f start fuel : find_from f start fuel = None ->
  forall index, (start <= index < start + fuel)%nat ->
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) <> sought f.
Proof.
  induction fuel as [|fuel IH] in start |- *; cbn [find_from]; [intros; lia |].
  case_bool_decide as Heq; [discriminate |].
  intros H index Hrange. destruct (Nat.eq_dec index start) as [-> | Hneq]; [exact Heq |].
  apply (IH _ H index). lia.
Qed.

Theorem find_from_first f start fuel index : find_from f start fuel = Some index ->
  forall earlier, (start <= earlier < index)%nat ->
  List.nth earlier (memory (machine f) arraydef_0__formulas) (0,0,0) <> sought f.
Proof.
  induction fuel as [|fuel IH] in start |- *; cbn [find_from]; [discriminate |].
  case_bool_decide as Heq.
  - intro H. injection H as <-. intros; lia.
  - intros H earlier Hrange. destruct (Nat.eq_dec earlier start) as [-> | Hneq]; [exact Heq |].
    apply (IH _ H earlier). lia.
Qed.

Theorem after_scan_found (f : Frame) : nums f vardef_0__intern_found = 1 ->
  execLocal after_scan f = Some (tt, f).
Proof.
  intro Hfound. destruct f as [s bs ns]. cbn [nums] in Hfound. unfold after_scan.
  cbv beta iota zeta delta [shortCircuitAnd numberLocalGet bind execLocal
    localStep optionBind nums fst snd].
  rewrite bool_decide_false by (rewrite Hfound; discriminate).
  reflexivity.
Qed.

Definition start_frame (s : Machine) bs ns : Frame :=
  setNum {| machine := s; bools := bs; nums := ns |} vardef_0__intern_found 0.

Lemma intern_after_count s bs ns count :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = count ->
  exec (funcdef_0__intern bs ns) s =
    optionBind (execLocal (after_count count) (start_frame s bs ns))
      (fun response => Some (fst response, machine (snd response))).
Proof.
  intros Hlength Hcount.
  change (@List.nth Z (Z.to_nat 1) (memory s arraydef_0__meta) 0 = count) in Hcount.
  unfold funcdef_0__intern. rewrite exec_eliminate.
  unfold funcdef_0__intern_body.
  cbv beta iota zeta delta [numberLocalSet retrieve bind execLocal localStep step
    optionBind setNum setMachine machine nums fst snd].
  case_decide; [|lia].
  rewrite nth_lt_default with (default := 0%Z), Hcount.
  reflexivity.
Qed.

Theorem intern_existing s bs ns count index :
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 1 (memory s arraydef_0__meta) 0 = Z.of_nat count ->
  (count <= length (memory s arraydef_0__formulas))%nat ->
  find_from (start_frame s bs ns) 0 count = Some index ->
  exec (funcdef_0__intern bs ns) s = Some (tt, store_meta s 0 (Z.of_nat index)).
Proof.
  intros Hlength Hcount Hbound Hfind.
  rewrite (intern_after_count s bs ns (Z.of_nat count) Hlength Hcount).
  rewrite split_scan, execLocal_bind, Nat2Z.id.
  rewrite (scan_loop (start_frame s bs ns) count 0 count).
  2: reflexivity.
  2: exact Hbound.
  2: exact (Nat.lt_trans 0 8 _ ltac:(lia) Hlength).
  rewrite Hfind. cbn [optionBind fst snd].
  rewrite after_scan_found.
  2: reflexivity.
  reflexivity.
Qed.
End InternExecution.
