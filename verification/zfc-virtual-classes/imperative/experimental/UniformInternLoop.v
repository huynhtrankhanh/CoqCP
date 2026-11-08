From CoqCP Require Import Options Imperative Execution.
From UniformInternFixture Require Import UniformInternProgram UniformInternModel.
From stdpp Require Import numbers list.
From Stdlib Require Import Lists.List ZArith.ZArith Logic.Eqdep_dec Lia.
Open Scope Z_scope.

(* Generated experimental interner scan. Does not prove hashing, insertion,
   resizing, or the full interner procedure. *)
Module UniformInternLoop.
Definition Machine := @Execution.Machine arrayIndex1 (arrayType _ environment1).
Definition store_meta (s : Machine) slot value :=
  withMemory s (modifyArray (memory s) arraydef_0__meta slot value).
Definition maximum : Z := 18446744073709551615.
Definition word x := 0 <= x <= maximum.
Lemma coerce_word x : word x -> coerceInt x 64 = x.
Proof. intros H. unfold coerceInt. apply Z.mod_small. unfold word, maximum in H. lia. Qed.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformIntern)
  withLocalVariablesReturnValue R.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformIntern.

(* This is the collision-chain loop selected from the generated interner.
   Its range binder is unused; the current link is an explicit local variable. *)
Definition scan_body : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformIntern_body in funcdef_0__uniformIntern_body in
  let code := eval cbn zeta in code in
  lazymatch code with context [loop _ ?body] =>
    let body := eval cbn zeta in body in exact body
  end).
Definition sought (f : Frame) :=
  (nums f vardef_0__uniformIntern_tag, nums f vardef_0__uniformIntern_a, nums f vardef_0__uniformIntern_b).
Definition advance (f : Frame) index := setNum f vardef_0__uniformIntern_current (Z.of_nat index).
Definition found_frame (f : Frame) index :=
  setNum (setMachine (advance f index) (store_meta (machine f) 0 (Z.of_nat index)))
    vardef_0__uniformIntern_found 1.
Definition next_frame (f : Frame) index link :=
  setNum (advance f index) vardef_0__uniformIntern_current link.

Theorem scan_empty (f : Frame) remaining : nums f vardef_0__uniformIntern_current = 0 ->
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
  nums f vardef_0__uniformIntern_current = Z.of_nat (S index) ->
  Z.of_nat (S index) <= maximum ->
  (index < length (memory (machine f) arraydef_0__uniformNodes))%nat ->
  (index < length (memory (machine f) arraydef_0__uniformLinks))%nat ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  List.nth index (memory (machine f) arraydef_0__uniformNodes) (0,0,0) = (x,y,z) ->
  List.nth index (memory (machine f) arraydef_0__uniformLinks) 0 = link ->
  execLocal (scan_body remaining) f =
    if bool_decide ((x,y,z) = sought f) then Some (Stop,found_frame f index)
    else Some (KeepGoing,next_frame f index link).
Proof.
  intros Hcurrent Hlimit Hformula Hlinks Hmeta Hentry Hlink.
  destruct f as [s bs ns]. cbn [machine nums sought] in *.
  change (@List.nth (Z*Z*Z)%type index (memory s arraydef_0__uniformNodes) (0,0,0) = (x,y,z)) in Hentry.
  change (@List.nth Z index (memory s arraydef_0__uniformLinks) 0 = link) in Hlink.
  destruct (Z.eq_dec x (ns vardef_0__uniformIntern_tag));
    destruct (Z.eq_dec y (ns vardef_0__uniformIntern_a));
    destruct (Z.eq_dec z (ns vardef_0__uniformIntern_b)).
  all: unfold scan_body; cbn zeta.
  all: cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
    shortCircuitAnd retrieve numberLocalGet numberLocalSet store break subInt
    execLocal localStep step optionBind fst snd nums bools machine setNum setMachine
    Imperative.update decide decide_rel
    variableIndexEqualityDecidablevarsfuncdef_0__uniformIntern varsfuncdef_0__uniformIntern_rec].
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
        variableIndexEqualityDecidablevarsfuncdef_0__uniformIntern varsfuncdef_0__uniformIntern_rec sought]
    |match goal with |- context [Nat.lt_dec ?i ?n] =>
        destruct (Nat.lt_dec i n); [|exfalso; lia] end
    |case_decide; [|lia]
  ].
  all: reflexivity.
Qed.


(* Bounds on one-based links and on the actual node/link arrays. The links need
   not be acyclic: finite fuel bounds the generated loop independently. *)
Definition entries_valid (f : Frame) count :=
  (count <= length (memory (machine f) arraydef_0__uniformNodes))%nat /\
  (count <= length (memory (machine f) arraydef_0__uniformLinks))%nat /\
  forall i, (i < count)%nat ->
    0 <= List.nth i (memory (machine f) arraydef_0__uniformLinks) 0 <= Z.of_nat count.

Fixpoint scan_index (f : Frame) fuel pointer : option Z :=
  match fuel,pointer with
  | O,_ | _,O => None
  | S rest,S i =>
    if bool_decide (List.nth i (memory (machine f) arraydef_0__uniformNodes) (0,0,0) = sought f)
    then Some (Z.of_nat i)
    else scan_index f rest (Z.to_nat (List.nth i (memory (machine f) arraydef_0__uniformLinks) 0))
  end.

Definition observed_result (f : Frame) : option Z :=
  if bool_decide (nums f vardef_0__uniformIntern_found = 1)
  then Some (List.nth 0 (memory (machine f) arraydef_0__meta) 0) else None.

Lemma next_observed f i link : observed_result (next_frame f i link) = observed_result f.
Proof. destruct f. reflexivity. Qed.
Lemma next_sought f i link : sought (next_frame f i link) = sought f.
Proof. destruct f. reflexivity. Qed.
Lemma next_scan f i link fuel pointer : scan_index (next_frame f i link) fuel pointer = scan_index f fuel pointer.
Proof.
  induction fuel as [|fuel IH] in pointer |- *; [reflexivity|]. destruct pointer as [|pointer]; [reflexivity|].
  cbn [scan_index]. rewrite next_sought.
  change (memory (machine (next_frame f i link)) arraydef_0__uniformNodes) with
    (memory (machine f) arraydef_0__uniformNodes).
  change (memory (machine (next_frame f i link)) arraydef_0__uniformLinks) with
    (memory (machine f) arraydef_0__uniformLinks).
  destruct (bool_decide (List.nth pointer (memory (machine f) arraydef_0__uniformNodes) (0,0,0) = sought f)); [reflexivity|].
  apply IH.
Qed.
Lemma hit_observed f i :
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  observed_result (found_frame f i) = Some (Z.of_nat i).
Proof.
  destruct f as [s bs ns]. cbn [machine nums]. intro Hlen.
  unfold observed_result, found_frame, advance, store_meta.
  cbn [machine setMachine setNum withMemory memory].
  rewrite bool_decide_true by reflexivity.
  unfold modifyArray. destruct (decide (arraydef_0__meta = arraydef_0__meta)) as [Heq|Hne]; [|contradiction].
  assert (Heq = eq_refl) as -> by (apply Eqdep_dec.UIP_dec; decide equality).
  destruct (memory s arraydef_0__meta); [cbn in Hlen; lia|reflexivity].
Qed.

(* The actual generated loop agrees with a full-tuple scan for arbitrary
   finite chains and fuel. Hashing, growth and insertion are separate. *)
Theorem scan_loop_refines fuel (f : Frame) count pointer :
  entries_valid f count -> Z.of_nat count <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__uniformIntern_current = Z.of_nat pointer -> (pointer <= count)%nat ->
  observed_result f = None ->
  exists final, execLocal (loop fuel scan_body) f = Some (tt,final) /\
    observed_result final = scan_index f fuel pointer.
Proof.
  induction fuel as [|fuel IH] in f, pointer |- *.
  - intros Hvalid Hlimit Hmeta Hpointer Hbound Hinitial. exists f. cbn [loop scan_index]. auto.
  - intros [Hnodes [Hlinks Hbounded]] Hlimit Hmeta Hpointer Hbound Hinitial.
    rewrite loop_S, execLocal_bind.
    destruct pointer as [|i].
    + rewrite scan_empty by exact Hpointer. cbn [optionBind fst snd scan_index]. exists f. auto.
    + destruct (List.nth i (memory (machine f) arraydef_0__uniformNodes) (0,0,0)) as [[x y] z] eqn:Hentry.
      set (link := List.nth i (memory (machine f) arraydef_0__uniformLinks) 0).
      rewrite (scan_step f fuel i x y z link Hpointer) by (try assumption; try reflexivity; lia).
      case_bool_decide as Hmatch.
      * cbn [optionBind fst snd scan_index]. rewrite Hentry, bool_decide_true by exact Hmatch.
        exists (found_frame f i). split; [reflexivity|]. now apply hit_observed.
      * cbn [optionBind fst snd scan_index]. rewrite Hentry, bool_decide_false by exact Hmatch.
        assert (Hlink : 0 <= link <= Z.of_nat count) by (apply Hbounded; lia).
        destruct (IH (next_frame f i link) (Z.to_nat link)) as [final [Hrun Hresult]].
        -- split; [exact Hnodes|]. split; assumption.
        -- exact Hlimit.
        -- exact Hmeta.
        -- change (link = Z.of_nat (Z.to_nat link)). rewrite Z2Nat.id by lia. reflexivity.
        -- pose proof (Z2Nat.id link ltac:(lia)). lia.
        -- now rewrite next_observed.
        -- exists final. split; [exact Hrun|]. now rewrite next_scan in Hresult.
Qed.

(* Regardless of collisions or cycles, a reported hit is an in-bounds row
   equal to all three components of the query. *)
Theorem scan_index_sound fuel (f : Frame) count pointer result :
  entries_valid f count -> (pointer <= count)%nat ->
  scan_index f fuel pointer = Some result ->
  exists i, (i < count)%nat /\ result = Z.of_nat i /\
    nth_error (memory (machine f) arraydef_0__uniformNodes) i = Some (sought f).
Proof.
  induction fuel as [|fuel IH] in pointer |- *; [discriminate|].
  destruct pointer as [|i]; [discriminate|].
  intros Hvalid Hpointer. destruct Hvalid as [Hnodes [Hlinks Hbounded]].
  cbn [scan_index].
  destruct (bool_decide (List.nth i (memory (machine f) arraydef_0__uniformNodes)
    (0,0,0) = sought f)) eqn:Hmatch.
  - intro Hresult. inversion Hresult; subst result. exists i. split; [lia|].
    split; [reflexivity|]. apply bool_decide_eq_true in Hmatch.
    rewrite <- Hmatch. apply nth_error_nth'. lia.
  - intro Hresult. eapply IH; [split; [exact Hnodes|split; [exact Hlinks|exact Hbounded]]| |exact Hresult].
    pose proof (Hbounded i ltac:(lia)) as Hlink.
    pose proof (Z2Nat.id (List.nth i (memory (machine f) arraydef_0__uniformLinks) 0) ltac:(lia)). lia.
Qed.

Corollary generated_loop_hit_sound fuel (f : Frame) count pointer :
  entries_valid f count -> Z.of_nat count <= maximum ->
  (0 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums f vardef_0__uniformIntern_current = Z.of_nat pointer -> (pointer <= count)%nat ->
  observed_result f = None ->
  exists final, execLocal (loop fuel scan_body) f = Some (tt,final) /\
    (forall result, observed_result final = Some result ->
      exists i, (i < count)%nat /\ result = Z.of_nat i /\
        nth_error (memory (machine f) arraydef_0__uniformNodes) i = Some (sought f)).
Proof.
  intros Hvalid Hlimit Hmeta Hpointer Hbound Hinitial.
  destruct (scan_loop_refines fuel f count pointer Hvalid Hlimit Hmeta Hpointer Hbound Hinitial)
    as [final [Hrun Hresult]]. exists final. split; [exact Hrun|].
  intros result Hhit. rewrite Hresult in Hhit.
  eapply scan_index_sound; eauto.
Qed.
End UniformInternLoop.
