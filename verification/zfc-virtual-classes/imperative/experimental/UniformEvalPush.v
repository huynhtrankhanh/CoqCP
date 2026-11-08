From CoqCP Require Import Options Imperative Execution.
From UniformEvalFixture Require Import UniformEvalProgram.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.

(* A general execution theorem for the actual generated push procedure.
   This fixture says nothing about the surrounding evaluator worklist. *)
Definition Machine := @Execution.Machine arrayIndex1 (arrayType _ environment1).
Definition maximum : Z := 18446744073709551615.
Definition word x := 0 <= x <= maximum.
Lemma coerce_word x : word x -> coerceInt x 64 = x.
Proof. intros H. unfold coerceInt. apply Z.mod_small. unfold word, maximum in H. lia. Qed.
Lemma update_count (ns : varsfuncdef_0__uniformEvalPush -> Z) (x : Z) : update ns vardef_0__uniformEvalPush_count x vardef_0__uniformEvalPush_count = x.
Proof. unfold update. case_decide; congruence. Qed.
Lemma update_node (ns : varsfuncdef_0__uniformEvalPush -> Z) (x : Z) : update ns vardef_0__uniformEvalPush_count x vardef_0__uniformEvalPush_node = ns vardef_0__uniformEvalPush_node.
Proof. unfold update. case_decide; congruence. Qed.
Lemma update_depth (ns : varsfuncdef_0__uniformEvalPush -> Z) (x : Z) : update ns vardef_0__uniformEvalPush_count x vardef_0__uniformEvalPush_depth = ns vardef_0__uniformEvalPush_depth.
Proof. unfold update. case_decide; congruence. Qed.
Definition pushed (s : Machine) top node depth :=
  let grown := withMemory s (growArrays (memory s) arraydef_0__uniformEvalStack (S top) (0,0,0)) in
  let written := withMemory grown (modifyArray (memory grown) arraydef_0__uniformEvalStack top (node,depth,0)) in
  withMemory written (modifyArray (memory written) arraydef_0__uniformEvalState 0 (Z.of_nat (S top))).
Lemma modify_stack_state (values : forall name, list (arrayType _ environment1 name)) slot value :
  modifyArray values arraydef_0__uniformEvalStack slot value arraydef_0__uniformEvalState = values arraydef_0__uniformEvalState.
Proof. reflexivity. Qed.
Theorem generated_push s bs ns top :
  (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  List.nth 0 (memory s arraydef_0__uniformEvalState) 0 = Z.of_nat top ->
  Z.of_nat top < maximum ->
  exec (funcdef_0__uniformEvalPush bs ns) s =
    Some (tt, pushed s top (ns vardef_0__uniformEvalPush_node) (ns vardef_0__uniformEvalPush_depth)).
Proof.
  intros Hmeta Htop Hlimit.
  change (@List.nth Z 0 (memory s arraydef_0__uniformEvalState) 0 = Z.of_nat top) in Htop.
  change (0 < @List.length Z (memory s arraydef_0__uniformEvalState))%nat in Hmeta.
  cbv beta iota zeta delta [memory] in Hmeta, Htop.
  unfold funcdef_0__uniformEvalPush. rewrite exec_eliminate. unfold funcdef_0__uniformEvalPush_body.
  unfold maximum in Hlimit.
  cbv beta iota zeta delta [numberLocalGet numberLocalSet retrieve store grow addInt bind
    execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory].
  replace (Z.to_nat 0) with 0%nat by reflexivity.
  let guard := constr:(Nat.lt 0 (length (memory s arraydef_0__uniformEvalState))) in
  let guard := eval cbv beta iota zeta delta [memory] in guard in
  lazymatch goal with |- context [@decide guard ?decision] =>
    destruct (@decide guard decision) as [Hbound |Hbound];
      [|exfalso; apply Hbound; exact Hmeta]
  end.
  rewrite nth_lt_default with (default := 0%Z), Htop.
  try rewrite bool_decide_false by lia.
  repeat first [
    match goal with |- context [bool_decide ?P] =>
      first [rewrite (bool_decide_true P) by lia |rewrite (bool_decide_false P) by lia]
    end
    | rewrite nth_lt_default with (default := 0%Z)
    | rewrite Htop | rewrite Nat2Z.id | rewrite update_count | rewrite update_node | rewrite update_depth
    | progress replace (Z.to_nat 0) with 0%nat by reflexivity
    | progress replace (Z.of_nat top + 1) with (Z.of_nat (S top)) by lia
    | match goal with |- context [coerceInt ?value 64] =>
        rewrite (coerce_word value) by (unfold word, maximum; lia)
      end
    | progress cbv beta iota zeta delta [shortCircuitAnd numberLocalGet numberLocalSet retrieve store grow addInt bind
        execLocal localStep step optionBind setNum setMachine machine nums bools fst snd withMemory memory]
    | rewrite modify_stack_state
    | rewrite growArrays_other by discriminate | rewrite growArrays_same
    | match goal with |- context [decide (Nat.lt ?slot ?len)] =>
        let Hready := fresh "Hready" in
        assert (Hready : (slot < len)%nat) by
          (repeat rewrite length_insert; try rewrite growList_length;
           first [change (slot < length (memory s arraydef_0__uniformEvalState))%nat; lia |lia]);
        case_decide; [clear Hready |contradiction]
      end
    | case_decide; [|lia]
  ].
  reflexivity.
Qed.
Definition error_state (s : Machine) :=
  withMemory s (modifyArray (memory s) arraydef_0__meta 8 1).
Theorem generated_push_full s bs ns :
  (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 0 (memory s arraydef_0__uniformEvalState) 0 = maximum ->
  exec (funcdef_0__uniformEvalPush bs ns) s = Some (tt, error_state s).
Proof.
  intros Hstate Hmeta Htop.
  change (@List.nth Z (Z.to_nat 0) (memory s arraydef_0__uniformEvalState) 0 = maximum) in Htop.
  unfold funcdef_0__uniformEvalPush. rewrite exec_eliminate. unfold funcdef_0__uniformEvalPush_body.
  cbv beta iota zeta delta [numberLocalGet numberLocalSet retrieve store bind execLocal localStep step
    optionBind setNum setMachine machine nums bools fst snd].
  case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z), Htop.
  cbv beta iota zeta delta [numberLocalGet bind execLocal localStep step optionBind nums bools].
  rewrite update_count. rewrite bool_decide_true by reflexivity.
  cbv beta iota zeta delta [store bind execLocal localStep step optionBind
    setMachine machine nums bools fst snd].
  case_decide; [reflexivity |lia].
Qed.

Corollary generated_push_full_preserves_stack s bs ns :
  (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  (8 < length (memory s arraydef_0__meta))%nat ->
  List.nth 0 (memory s arraydef_0__uniformEvalState) 0 = maximum ->
  exists result, exec (funcdef_0__uniformEvalPush bs ns) s = Some (tt, result) /\
    memory result arraydef_0__uniformEvalStack = memory s arraydef_0__uniformEvalStack /\
    memory result arraydef_0__uniformEvalState = memory s arraydef_0__uniformEvalState /\
    stdin result = stdin s /\ stdout result = stdout s.
Proof.
  intros Hstate Hmeta Htop. exists (error_state s).
  split; [now apply generated_push_full|].
  repeat split; reflexivity.
Qed.

Lemma nth_insert_same {A} (xs : list A) n value default :
  (n < length xs)%nat -> List.nth n (<[n := value]> xs) default = value.
Proof.
  induction xs as [|x xs IH] in n |- *; [cbn; lia|].
  destruct n as [|n]; cbn; [reflexivity|]. intro H. apply IH. lia.
Qed.

Lemma nth_insert_other {A} (xs : list A) i j value default :
  i <> j -> List.nth i (<[j := value]> xs) default = List.nth i xs default.
Proof.
  induction xs as [|x xs IH] in i, j |- *; [destruct i, j; reflexivity|].
  destruct i as [|i], j as [|j]; cbn; try reflexivity; [congruence|].
  intro H. apply IH. congruence.
Qed.

(* The push writes one new work item and leaves all earlier stack slots
   unchanged. This is the prefix invariant needed by a worklist proof. *)
Theorem pushed_stack_entry s top node depth :
  List.nth top (memory (pushed s top node depth) arraydef_0__uniformEvalStack)
    (0,0,0) = (node,depth,0).
Proof.
  unfold pushed. cbn [withMemory memory].
  change (List.nth top (<[top := (node,depth,0)]>
    (growArrays (memory s) arraydef_0__uniformEvalStack (S top) (0,0,0)
      arraydef_0__uniformEvalStack)) (0,0,0) = (node,depth,0)).
  rewrite growArrays_same. apply nth_insert_same. rewrite growList_length. lia.
Qed.

Theorem pushed_stack_prefix s top node depth i :
  (i < top)%nat -> (i < length (memory s arraydef_0__uniformEvalStack))%nat ->
  List.nth i (memory (pushed s top node depth) arraydef_0__uniformEvalStack) (0,0,0) =
  List.nth i (memory s arraydef_0__uniformEvalStack) (0,0,0).
Proof.
  intros Hi Hlength. unfold pushed. cbn [withMemory memory].
  change (List.nth i (<[top := (node,depth,0)]>
    (growArrays (memory s) arraydef_0__uniformEvalStack (S top) (0,0,0)
      arraydef_0__uniformEvalStack)) (0,0,0) =
    List.nth i (memory s arraydef_0__uniformEvalStack) (0,0,0)).
  rewrite nth_insert_other by lia. rewrite growArrays_same.
  unfold growList. apply app_nth1. exact Hlength.
Qed.

Theorem pushed_count s top node depth :
  (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  List.nth 0 (memory (pushed s top node depth) arraydef_0__uniformEvalState) 0 =
  Z.of_nat (S top).
Proof.
  intro H. unfold pushed. cbn [withMemory memory].
  change (List.nth 0 (<[0%nat := Z.of_nat (S top)]>
    (memory s arraydef_0__uniformEvalState)) 0 = Z.of_nat (S top)).
  apply nth_insert_same. exact H.
Qed.

Theorem pushed_preserves_io s top node depth :
  stdin (pushed s top node depth) = stdin s /\
  stdout (pushed s top node depth) = stdout s.
Proof. split; reflexivity. Qed.

Theorem pushed_preserves_other_array s top node depth name :
  name <> arraydef_0__uniformEvalStack ->
  name <> arraydef_0__uniformEvalState ->
  memory (pushed s top node depth) name = memory s name.
Proof.
  intros Hstack Hstate. unfold pushed. cbn [withMemory memory].
  unfold modifyArray. repeat case_decide; subst; try contradiction.
  now apply growArrays_other.
Qed.

Theorem generated_push_stack_frame s bs ns top :
  (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  List.nth 0 (memory s arraydef_0__uniformEvalState) 0 = Z.of_nat top ->
  Z.of_nat top < maximum ->
  exists result,
    exec (funcdef_0__uniformEvalPush bs ns) s = Some (tt, result) /\
    List.nth top (memory result arraydef_0__uniformEvalStack) (0,0,0) =
      (ns vardef_0__uniformEvalPush_node, ns vardef_0__uniformEvalPush_depth, 0) /\
    List.nth 0 (memory result arraydef_0__uniformEvalState) 0 = Z.of_nat (S top) /\
    (forall i, (i < top)%nat ->
      (i < length (memory s arraydef_0__uniformEvalStack))%nat ->
      List.nth i (memory result arraydef_0__uniformEvalStack) (0,0,0) =
      List.nth i (memory s arraydef_0__uniformEvalStack) (0,0,0)) /\
    (forall name, name <> arraydef_0__uniformEvalStack ->
      name <> arraydef_0__uniformEvalState -> memory result name = memory s name) /\
    stdin result = stdin s /\ stdout result = stdout s.
Proof.
  intros Hstate Htop Hmax.
  exists (pushed s top (ns vardef_0__uniformEvalPush_node)
    (ns vardef_0__uniformEvalPush_depth)).
  split; [now apply generated_push|].
  split; [apply pushed_stack_entry|].
  split; [now apply pushed_count|].
  split; [intros; now apply pushed_stack_prefix|].
  split; [intros; now apply pushed_preserves_other_array|apply pushed_preserves_io].
Qed.

(* For a valid worklist, every live slot lies in the old allocation, so the
   preceding frame theorem preserves the complete live prefix. *)
Corollary generated_push_live_prefix s bs ns top :
  (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  List.nth 0 (memory s arraydef_0__uniformEvalState) 0 = Z.of_nat top ->
  (top <= length (memory s arraydef_0__uniformEvalStack))%nat ->
  Z.of_nat top < maximum ->
  exists result,
    exec (funcdef_0__uniformEvalPush bs ns) s = Some (tt, result) /\
    (forall i, (i < top)%nat ->
      List.nth i (memory result arraydef_0__uniformEvalStack) (0,0,0) =
      List.nth i (memory s arraydef_0__uniformEvalStack) (0,0,0)) /\
    List.nth top (memory result arraydef_0__uniformEvalStack) (0,0,0) =
      (ns vardef_0__uniformEvalPush_node, ns vardef_0__uniformEvalPush_depth, 0) /\
    List.nth 0 (memory result arraydef_0__uniformEvalState) 0 = Z.of_nat (S top).
Proof.
  intros Hstate Htop Hvalid Hmax.
  destruct (generated_push_stack_frame s bs ns top Hstate Htop Hmax)
    as (result & Hexec & Hnew & Hcount & Hprefix & Hrest).
  exists result. repeat split; try assumption.
  intros i Hi. apply Hprefix; lia.
Qed.

Print Assumptions generated_push.
Print Assumptions generated_push_full.
Print Assumptions pushed_stack_entry.
Print Assumptions pushed_stack_prefix.
Print Assumptions generated_push_stack_frame.
Print Assumptions generated_push_live_prefix.
