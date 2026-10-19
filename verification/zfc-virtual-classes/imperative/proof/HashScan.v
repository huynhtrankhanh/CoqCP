From CoqCP Require Import Options Imperative Execution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index ArrayFacts.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
Open Scope Z_scope.

Module HashScanExecution.
Import IndexExecution.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern)
  withLocalVariablesReturnValue R.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__intern.

(* This is the collision-chain loop selected from the generated interner.
   Its range binder is unused; the current link is an explicit local variable. *)
Definition scan_body : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__intern_body in funcdef_0__intern_body in
  let code := eval cbn zeta in code in
  lazymatch code with context [loop _ ?body] =>
    let body := eval cbn zeta in body in exact body
  end).
Definition sought (f : Frame) :=
  (nums f vardef_0__intern_tag, nums f vardef_0__intern_a, nums f vardef_0__intern_b).
Definition advance (f : Frame) index := setNum f vardef_0__intern_current (Z.of_nat index).
Definition found_frame (f : Frame) index :=
  setNum (setMachine (advance f index) (store_meta (machine f) 0 (Z.of_nat index)))
    vardef_0__intern_found 1.
Definition next_frame (f : Frame) index link :=
  setNum (advance f index) vardef_0__intern_current link.

Theorem scan_empty (f : Frame) remaining : nums f vardef_0__intern_current = 0 ->
  execLocal (scan_body remaining) f = Some (Stop,f).
Proof.
  destruct f as [s bs ns]. cbn [nums]. intro Hcurrent.
  unfold scan_body. cbn zeta.
  cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break
    execLocal localStep step optionBind fst snd nums machine setNum setMachine].
  rewrite Hcurrent, bool_decide_true by reflexivity. reflexivity.
Qed.

Theorem scan_step (f : Frame) remaining index x y z link :
  nums f vardef_0__intern_current = Z.of_nat (S index) ->
  Z.of_nat (S index) <= maximum ->
  (index < length (memory (machine f) arraydef_0__formulas))%nat ->
  (index < length (memory (machine f) arraydef_0__formulaLinks))%nat ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) = (x,y,z) ->
  List.nth index (memory (machine f) arraydef_0__formulaLinks) 0 = link ->
  execLocal (scan_body remaining) f =
    if bool_decide ((x,y,z) = sought f) then Some (Stop,found_frame f index)
    else Some (KeepGoing,next_frame f index link).
Proof.
  intros Hcurrent Hlimit Hformula Hlinks Hmeta Hentry Hlink.
  destruct f as [s bs ns]. cbn [machine nums sought] in *.
  change (@List.nth (Z*Z*Z)%type index (memory s arraydef_0__formulas) (0,0,0) = (x,y,z)) in Hentry.
  change (@List.nth Z index (memory s arraydef_0__formulaLinks) 0 = link) in Hlink.
  destruct (Z.eq_dec x (ns vardef_0__intern_tag));
    destruct (Z.eq_dec y (ns vardef_0__intern_a));
    destruct (Z.eq_dec z (ns vardef_0__intern_b)).
  all: unfold scan_body; cbn zeta.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__intern varsfuncdef_0__intern_rec].
  all: repeat first [rewrite Hcurrent
    |rewrite (coerce_word (Z.of_nat (S index) - 1)) by (unfold word, maximum in *; lia)
    |progress replace (Z.of_nat (S index) - 1) with (Z.of_nat index) by lia
    |rewrite Nat2Z.id
    |rewrite nth_lt_default with (default := (0,0,0))
    |rewrite nth_lt_default with (default := 0)
    |rewrite Hentry |rewrite Hlink
    |match goal with |- context [bool_decide ?P] =>
        first [rewrite (bool_decide_true P) by congruence
          |rewrite (bool_decide_false P) by (first [congruence|lia])]
      end
    |progress cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
        shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
        execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
        Imperative.update decide decide_rel
        variableIndexEqualityDecidablevarsfuncdef_0__intern varsfuncdef_0__intern_rec sought]
    |match goal with |- context [Nat.lt_dec ?i ?n] =>
        destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |case_decide; [|lia]
  ].
  all: reflexivity.
Qed.

Definition table_valid (s : Machine) n :=
  (n <= length (memory s arraydef_0__formulas))%nat /\
  (n <= length (memory s arraydef_0__formulaLinks))%nat /\
  forall i, (i < n)%nat -> 0 <= List.nth i (memory s arraydef_0__formulaLinks) 0 <= Z.of_nat i.
Definition checked_result (initial final : Frame) n :=
  nums final vardef_0__intern_found = 0 \/
  exists i, (i < n)%nat /\ nums final vardef_0__intern_found = 1 /\
    List.nth 0 (memory (machine final) arraydef_0__meta) 0 = Z.of_nat i /\
    List.nth i (memory (machine initial) arraydef_0__formulas) (0,0,0) = sought initial.
Definition preserves_storage (initial final : Frame) :=
  (forall name, name <> arraydef_0__meta -> memory (machine final) name = memory (machine initial) name) /\
  (forall i, i <> 0%nat -> List.nth i (memory (machine final) arraydef_0__meta) 0 =
    List.nth i (memory (machine initial) arraydef_0__meta) 0) /\
  stdin (machine final) = stdin (machine initial) /\ stdout (machine final) = stdout (machine initial).
Lemma found_preserves f i : preserves_storage f (found_frame f i).
Proof.
  split; [intros; now apply store_meta_other|]. split.
  - intros j H. unfold found_frame, advance, store_meta.
    cbn [machine setMachine setNum withMemory memory]. rewrite modify_meta.
    now apply ArrayFacts.nth_insert_other.
  - split; reflexivity.
Qed.
Lemma next_sought f i link : sought (next_frame f i link) = sought f.
Proof. destruct f. reflexivity. Qed.
Lemma next_found f i link : nums (next_frame f i link) vardef_0__intern_found =
  nums f vardef_0__intern_found.
Proof. destruct f. reflexivity. Qed.
Lemma found_flag f i : nums (found_frame f i) vardef_0__intern_found = 1.
Proof. destruct f. reflexivity. Qed.
(* Every finite collision scan terminates. A reported match denotes precisely
   the sought tuple, irrespective of the seed and of any bucket collisions. *)
Theorem scan_loop_checked fuel (f : Frame) n pointer :
  table_valid (machine f) n -> Z.of_nat n <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_current = Z.of_nat pointer -> (pointer <= n)%nat ->
  nums f vardef_0__intern_found = 0 ->
  exists final, execLocal (loop fuel scan_body) f = Some (tt,final) /\
    preserves_storage f final /\ checked_result f final n.
Proof.
  induction fuel as [|fuel IH] in f, pointer |- *.
  - intros Hvalid Hlimit Hmeta Hpointer Hbound Hfound.
    exists f. split; [reflexivity|]. split.
    + repeat split; reflexivity.
    + now left.
  - intros [Hformulas [Hlinks Hdescending]] Hlimit Hmeta Hpointer Hbound Hfound.
    rewrite loop_S, execLocal_bind.
    destruct pointer as [|i].
    + rewrite scan_empty by exact Hpointer. cbn [optionBind fst snd].
      exists f. split; [reflexivity|]. split.
      * repeat split; reflexivity.
      * now left.
    + destruct (List.nth i (memory (machine f) arraydef_0__formulas) (0,0,0))
        as [[x y] z] eqn:Hentry.
      set (link := List.nth i (memory (machine f) arraydef_0__formulaLinks) 0).
      rewrite (scan_step f fuel i x y z link Hpointer) by (try assumption; try reflexivity; lia).
      case_bool_decide as Hmatch.
      * cbn [optionBind fst snd]. exists (found_frame f i). split; [reflexivity|].
        split; [apply found_preserves|]. right. exists i. split; [lia|].
        split; [apply found_flag|]. split.
        -- apply store_result_read. exact Hmeta.
        -- now rewrite Hentry.
      * cbn [optionBind fst snd].
        assert (Hlink : 0 <= link <= Z.of_nat i) by (apply Hdescending; lia).
        destruct (IH (next_frame f i link) (Z.to_nat link)) as [final [Hrun [Hstorage Hchecked]]].
        -- split; [exact Hformulas|]. split; assumption.
        -- exact Hlimit.
        -- exact Hmeta.
        -- change (link = Z.of_nat (Z.to_nat link)). rewrite Z2Nat.id by lia. reflexivity.
        -- pose proof (Z2Nat.id link ltac:(lia)). lia.
        -- now rewrite next_found.
        -- exists final. split; [exact Hrun|]. split; [exact Hstorage|].
           unfold checked_result in *. rewrite next_sought in Hchecked. exact Hchecked.
Qed.

Inductive in_chain (s : Machine) : nat -> nat -> Prop :=
| chain_head i : in_chain s (S i) i
| chain_tail i j :
    in_chain s (Z.to_nat (List.nth i (memory s arraydef_0__formulaLinks) 0)) j ->
    in_chain s (S i) j.

Lemma in_chain_preserved s t pointer index :
  memory t arraydef_0__formulaLinks = memory s arraydef_0__formulaLinks ->
  in_chain s pointer index -> in_chain t pointer index.
Proof.
  intros Hlinks Hchain. induction Hchain.
  - constructor.
  - apply chain_tail. now rewrite Hlinks.
Qed.
Lemma table_valid_preserved s t n :
  memory t arraydef_0__formulas = memory s arraydef_0__formulas ->
  memory t arraydef_0__formulaLinks = memory s arraydef_0__formulaLinks ->
  table_valid s n -> table_valid t n.
Proof. intros Hfs Hlinks. unfold table_valid. now rewrite Hfs, Hlinks. Qed.

Lemma in_chain_index_bound s pointer index n :
  table_valid s n -> (pointer <= n)%nat -> in_chain s pointer index ->
  (index < pointer)%nat.
Proof.
  intros [_ [_ Hdescending]] Hbound Hchain.
  induction Hchain as [i | i j Hchain IH] in Hbound |- *; [lia|].
  pose proof (Hdescending i ltac:(lia)) as Hlink.
  pose proof (Z2Nat.id (List.nth i (memory s arraydef_0__formulaLinks) 0) ltac:(lia)) as Hcast.
  specialize (IH ltac:(lia)). lia.
Qed.

Theorem scan_loop_complete fuel (f : Frame) n pointer index :
  table_valid (machine f) n -> Z.of_nat n <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_current = Z.of_nat pointer -> (pointer <= n)%nat ->
  (pointer <= fuel)%nat -> in_chain (machine f) pointer index ->
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) = sought f ->
  exists final, execLocal (loop fuel scan_body) f = Some (tt,final) /\
    nums final vardef_0__intern_found = 1.
Proof.
  induction fuel as [|fuel IH] in f, pointer |- *.
  - intros Hvalid Hlimit Hmeta Hpointer Hbound Hfuel Hchain Htarget.
    assert (pointer = 0%nat) by lia. subst pointer. inversion Hchain.
  - intros [Hformulas [Hlinks Hdescending]] Hlimit Hmeta Hpointer Hbound Hfuel Hchain Htarget.
    destruct pointer as [|i]; [inversion Hchain|].
    rewrite loop_S, execLocal_bind.
    destruct (List.nth i (memory (machine f) arraydef_0__formulas) (0,0,0))
      as [[x y] z] eqn:Hentry.
    set (link := List.nth i (memory (machine f) arraydef_0__formulaLinks) 0).
    rewrite (scan_step f fuel i x y z link Hpointer) by (try assumption; try reflexivity; lia).
    case_bool_decide as Hmatch.
    + cbn [optionBind fst snd]. exists (found_frame f i). split; [reflexivity|apply found_flag].
    + cbn [optionBind fst snd].
      assert (Hlink : 0 <= link <= Z.of_nat i) by (apply Hdescending; lia).
      assert (Hchain' : in_chain (machine f) (Z.to_nat link) index).
      { inversion Hchain; subst.
        - rewrite Hentry in Htarget. contradiction.
        - assumption. }
      apply (IH (next_frame f i link) (Z.to_nat link)).
      * split; [exact Hformulas|]. split; assumption.
      * exact Hlimit.
      * exact Hmeta.
      * change (link = Z.of_nat (Z.to_nat link)). rewrite Z2Nat.id by lia. reflexivity.
      * pose proof (Z2Nat.id link ltac:(lia)). lia.
      * pose proof (Z2Nat.id link ltac:(lia)). lia.
      * exact Hchain'.
      * now rewrite next_sought.
Qed.

Theorem scan_lookup_complete (f : Frame) n pointer index :
  table_valid (machine f) n -> Z.of_nat n <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__intern_current = Z.of_nat pointer -> (pointer <= n)%nat ->
  nums f vardef_0__intern_found = 0 -> in_chain (machine f) pointer index ->
  List.nth index (memory (machine f) arraydef_0__formulas) (0,0,0) = sought f ->
  exists final i, execLocal (loop n scan_body) f = Some (tt,final) /\
    preserves_storage f final /\ (i < n)%nat /\ nums final vardef_0__intern_found = 1 /\
    List.nth 0 (memory (machine final) arraydef_0__meta) 0 = Z.of_nat i /\
    List.nth i (memory (machine f) arraydef_0__formulas) (0,0,0) = sought f.
Proof.
  intros Hvalid Hlimit Hmeta Hpointer Hbound Hfound Hchain Htarget.
  destruct (scan_loop_checked n f n pointer Hvalid Hlimit Hmeta Hpointer Hbound Hfound)
    as [final [Hrun [Hstorage Hchecked]]].
  destruct (scan_loop_complete n f n pointer index Hvalid Hlimit Hmeta Hpointer Hbound
    Hbound Hchain Htarget) as [other [Hrun' Hmatched]].
  rewrite Hrun in Hrun'. injection Hrun' as <-.
  destruct Hchecked as [Hzero|[i [Hi [Hflag [Hresult Htuple]]]]]; [congruence|].
  exists final,i. split; [exact Hrun|]. split; [exact Hstorage|].
  repeat split; assumption.
Qed.
End HashScanExecution.
