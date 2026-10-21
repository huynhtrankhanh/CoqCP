From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal CommandQuit CommandStructure.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.

Module CommandChain.
Import IndexExecution SipHashExecution ObservedLocal CommandQuitExecution.
Definition tags : list Z := [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26].
Definition handler_for reader opcode : LocalAction unit := match opcode with
| 1 => CommandStructure.handler_1 reader
| 2 => CommandStructure.handler_2 reader
| 3 => CommandStructure.handler_3 reader
| 4 => CommandStructure.handler_4 reader
| 5 => CommandStructure.handler_5 reader
| 6 => CommandStructure.handler_6 reader
| 7 => CommandStructure.handler_7 reader
| 8 => CommandStructure.handler_8 reader
| 9 => CommandStructure.handler_9 reader
| 10 => CommandStructure.handler_10 reader
| 11 => CommandStructure.handler_11 reader
| 12 => CommandStructure.handler_12 reader
| 13 => CommandStructure.handler_13 reader
| 14 => CommandStructure.handler_14 reader
| 15 => CommandStructure.handler_15 reader
| 16 => CommandStructure.handler_16 reader
| 17 => CommandStructure.handler_17 reader
| 18 => CommandStructure.handler_18 reader
| 19 => CommandStructure.handler_19 reader
| 20 => CommandStructure.handler_20 reader
| 21 => CommandStructure.handler_21 reader
| 22 => CommandStructure.handler_22 reader
| 23 => CommandStructure.handler_23 reader
| 24 => CommandStructure.handler_24 reader
| 25 => CommandStructure.handler_25 reader
| 26 => CommandStructure.handler_26 reader
| _ => Done _ _ _ tt end.
Definition guard_rhs : LocalAction bool :=
  ((Done _ _ _ 8 >>= fun index => retrieve _ _ _ arraydef_0__meta index) >>= fun value =>
    Done _ _ _ 0 >>= fun zero => Done _ _ _ (bool_decide (value = zero))).
Fixpoint chain (handlers : Z -> LocalAction unit) codes : LocalAction unit := match codes with
| [] => Done _ _ _ tt
| opcode :: codes => opcode_guard opcode guard_rhs (handlers opcode) >>= fun _ => chain handlers codes
end.
Definition source_chain (reader : reader_function) : LocalAction unit := ltac:(
  let code := eval unfold CommandStructure.compact_body in (CommandStructure.compact_body reader) in
  let code := eval cbv beta iota zeta in code in
  match code with
  | context [bind (bind (shortCircuitAnd (bind (numberLocalGet _ _ _ vardef_0__command_op) ?compare) ?guard) ?branch) ?next] =>
    let comparison := eval cbn beta in (compare 0%Z) in
    lazymatch comparison with bind (Done _ _ _ ?opcode) _ =>
      constr_eq opcode 1%Z;
      exact (bind (bind (shortCircuitAnd (bind (numberLocalGet _ _ _ vardef_0__command_op) compare) guard) branch) next)
    end
  end).
Lemma actual_chain reader : source_chain reader = chain (handler_for reader) tags.
Proof. reflexivity. Qed.
Lemma guard_skip opcode current right body (f : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations :
  nums f vardef_0__command_op = current -> current <> opcode ->
  execLocalObserved (opcode_guard opcode right body) (f,observations) = Some (tt,(f,observations)).
Proof.
  intros Hvalue Hneq. unfold opcode_guard, shortCircuitAnd.
  cbn [bind numberLocalGet execLocalObserved localStepObserved optionBind fst snd].
  rewrite Hvalue, bool_decide_false by lia. reflexivity.
Qed.
Lemma guard_take opcode body (f : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations :
  nums f vardef_0__command_op = opcode -> meta_value (machine f) 8 = 0 ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (opcode_guard opcode guard_rhs body) (f,observations) = execLocalObserved body (f,observations).
Proof.
  intros Hvalue Herror Hmeta. destruct f as [s bs ns]. cbn [nums machine] in *.
  unfold opcode_guard, shortCircuitAnd, guard_rhs.
  cbn [bind numberLocalGet execLocalObserved localStepObserved optionBind fst snd nums bools machine setMachine].
  rewrite Hvalue, bool_decide_true by reflexivity.
  cbn [bind retrieve execLocalObserved localStepObserved optionBind fst snd].
  unfold observedStep. cbn [step optionBind fst snd machine]. case_decide; [|lia].
  rewrite nth_lt_default with (default := 0%Z).
  cbn [optionBind fst snd machine setMachine nums bools].
  change (execLocalObserved (if bool_decide (meta_value s 8 = 0) then body else Done _ _ _ tt)
    ({|machine := s; bools := bs; nums := ns|},observations) =
    execLocalObserved body ({|machine := s; bools := bs; nums := ns|},observations)).
  rewrite Herror, bool_decide_true by reflexivity. reflexivity.
Qed.
Lemma chain_skips handlers codes current (f : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations :
  nums f vardef_0__command_op = current -> Forall (fun opcode => current <> opcode) codes ->
  execLocalObserved (chain handlers codes) (f,observations) = Some (tt,(f,observations)).
Proof.
  intros Hcurrent Hcodes. induction Hcodes as [|opcode codes Hneq Hcodes IH]; [reflexivity|].
  cbn [chain]. rewrite local_bind, (guard_skip opcode current _ _ f observations Hcurrent Hneq).
  cbn [optionBind fst snd]. exact IH.
Qed.
Lemma chain_active handlers prefix suffix opcode (f after : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations trace :
  nums f vardef_0__command_op = opcode -> meta_value (machine f) 8 = 0 ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  Forall (fun n => opcode <> n) prefix -> Forall (fun n => opcode <> n) suffix ->
  nums after vardef_0__command_op = opcode ->
  execLocalObserved (handlers opcode) (f,observations) = Some (tt,(after,trace)) ->
  execLocalObserved (chain handlers (prefix ++ opcode :: suffix)) (f,observations) = Some (tt,(after,trace)).
Proof.
  intros Hcurrent Herror Hmeta Hprefix Hsuffix Hafter Hbody.
  induction Hprefix as [|other prefix Hneq Hprefix IH].
  - cbn [app chain]. rewrite local_bind, (guard_take opcode _ f observations Hcurrent Herror Hmeta), Hbody.
    cbn [optionBind fst snd]. now apply (chain_skips handlers suffix opcode).
  - cbn [app chain]. rewrite local_bind, (guard_skip other opcode _ _ f observations Hcurrent Hneq).
    cbn [optionBind fst snd]. exact IH.
Qed.
Lemma tags_nodup : NoDup tags.
Proof. change (NoDup (seqZ 1 26)). apply NoDup_seqZ. Qed.
Lemma supported_member opcode : 1 <= opcode <= 26 -> opcode ∈ tags.
Proof. intro Hrange. change (opcode ∈ seqZ 1 26). rewrite elem_of_seqZ. lia. Qed.
Theorem chain_supported handlers opcode (f after : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations trace :
  1 <= opcode <= 26 -> nums f vardef_0__command_op = opcode -> meta_value (machine f) 8 = 0 ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums after vardef_0__command_op = opcode ->
  execLocalObserved (handlers opcode) (f,observations) = Some (tt,(after,trace)) ->
  execLocalObserved (chain handlers tags) (f,observations) = Some (tt,(after,trace)).
Proof.
  intros Hrange Hcurrent Herror Hmeta Hafter Hbody.
  destruct (list_elem_of_split tags opcode (supported_member opcode Hrange)) as [prefix [suffix Hsplit]].
  pose proof tags_nodup as Hnodup. rewrite Hsplit in Hnodup |- *.
  apply NoDup_app in Hnodup as [Hprefix [Hcross Hsuffix]]. apply NoDup_cons in Hsuffix as [Hnot Hsuffix].
  eapply chain_active; try assumption.
  - apply Forall_forall. intros n Hn Heq. subst n. apply (Hcross opcode Hn). apply elem_of_cons. left. reflexivity.
  - apply Forall_forall. intros n Hn Heq. apply Hnot. now rewrite Heq.
Qed.
Theorem generated_source_chain reader opcode (f after : @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__command) observations trace :
  1 <= opcode <= 26 -> nums f vardef_0__command_op = opcode -> meta_value (machine f) 8 = 0 ->
  (8 < length (memory (machine f) arraydef_0__meta))%nat ->
  nums after vardef_0__command_op = opcode ->
  execLocalObserved (handler_for reader opcode) (f,observations) = Some (tt,(after,trace)) ->
  execLocalObserved (source_chain reader) (f,observations) = Some (tt,(after,trace)).
Proof. intros. rewrite actual_chain. eapply chain_supported; eassumption. Qed.
End CommandChain.
