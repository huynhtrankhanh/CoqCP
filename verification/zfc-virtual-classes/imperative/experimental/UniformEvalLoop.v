From CoqCP Require Import Options Imperative Execution.
From UniformEvalFull Require Import EvalProgram.
From stdpp Require Import numbers list.
From Stdlib Require Import ZArith.ZArith Lia.
Open Scope Z_scope.
(* These lemmas extract the outer loop, the actual memo lookup call, and the
   memo-hit dispatch from the generated experimental evaluator. They do not
   establish lookup correctness, stack reads, or complete traversal. *)
Module UniformEvalLoop.
Definition LocalAction R := Action
  (WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformEvaluate)
  withLocalVariablesReturnValue R.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__uniformEvaluate.
Definition loop_body : nat -> LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  lazymatch code with context [loop _ ?body] =>
    let body := eval cbn zeta in body in exact body
  end).
Theorem empty_break (f : Frame) remaining :
 (0 < length (memory (machine f) arraydef_0__uniformEvalState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformEvalState) 0 = 0 ->
 execLocal (loop_body remaining) f = Some (Stop,f).
Proof.
 destruct f as [s bs ns]. cbn [machine]. intros Hlen Htop.
 change (@List.nth Z 0 (memory s arraydef_0__uniformEvalState) 0 = 0) in Htop.
 unfold loop_body. cbn zeta.
 cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
 shortCircuitOr retrieve numberLocalGet numberLocalSet store break subInt
 execLocal localStep step optionBind fst snd nums bools machine setNum setMachine].
 case_decide; [|lia]. cbn [Z.to_nat]. rewrite nth_lt_default with (default := 0%Z). replace (Z.to_nat 0) with 0%nat by reflexivity. rewrite Htop.
 rewrite bool_decide_true by reflexivity. reflexivity.
Qed.
Theorem fatal_break (f : Frame) remaining :
 (0 < length (memory (machine f) arraydef_0__uniformEvalState))%nat ->
 (8 < length (memory (machine f) arraydef_0__meta))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformEvalState) 0 <> 0 ->
 List.nth 8 (memory (machine f) arraydef_0__meta) 0 <> 0 ->
 execLocal (loop_body remaining) f = Some (Stop,f).
Proof.
 destruct f as [s bs ns]. cbn [machine]. intros Hlen Hmeta Htop Hfatal.
 change (@List.nth Z 0 (memory s arraydef_0__uniformEvalState) 0 <> 0) in Htop.
 change (@List.nth Z 8 (memory s arraydef_0__meta) 0 <> 0) in Hfatal.
 unfold loop_body. cbn zeta.
 cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
 shortCircuitOr retrieve numberLocalGet numberLocalSet store break subInt
 execLocal localStep step optionBind fst snd nums bools machine setNum setMachine].
 case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
 replace (Z.to_nat 0) with 0%nat by reflexivity. rewrite bool_decide_false by exact Htop.
 cbv beta iota zeta delta [execLocal localStep step optionBind fst snd nums bools machine].
 case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
 replace (Z.to_nat 8) with 8%nat by reflexivity. rewrite bool_decide_true by exact Hfatal.
 reflexivity.
Qed.
Definition memo_hit_pop : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  multimatch code with context [liftToWithinLoop ?act] =>
    lazymatch act with context [store _ _ _ arraydef_0__uniformEvalState _ _] => exact act end
  end).
Definition memo_hit_branch : LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  multimatch code with context [bind (liftToWithinLoop ?cond) ?next] =>
    lazymatch cond with context [retrieve _ _ _ arraydef_0__uniformMemoState _] =>
      let after := eval cbn beta in (next true) in exact (dropWithinLoop after)
    end
  end).
Definition memo_hit_dispatch : LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  multimatch code with context [bind (liftToWithinLoop ?cond) ?next] =>
    lazymatch cond with context [retrieve _ _ _ arraydef_0__uniformMemoState _] =>
      exact (dropWithinLoop (bind (liftToWithinLoop cond) next))
    end
  end).
Definition memo_get_call : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  multimatch code with context [bind (liftToWithinLoop ?call) ?next] =>
    lazymatch call with context [funcdef_0__uniformMemoGet _ _] => exact call end
  end).
Definition memo_get_then_dispatch : LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  multimatch code with context [bind (liftToWithinLoop ?call) ?next] =>
    lazymatch call with context [funcdef_0__uniformMemoGet _ _] =>
      exact (dropWithinLoop (bind (liftToWithinLoop call) next))
    end
  end).
Definition after_memo_get : LocalAction LoopOutcome := ltac:(
  let code := eval unfold funcdef_0__uniformEvaluate_body in funcdef_0__uniformEvaluate_body in
  let code := eval cbn zeta in code in
  multimatch code with context [bind (liftToWithinLoop ?call) ?next] =>
    lazymatch call with context [funcdef_0__uniformMemoGet _ _] =>
      let after := eval cbn beta in (next tt) in exact (dropWithinLoop after)
    end
  end).
Lemma exec_drop_lift {R} (code : LocalAction R) next (f : Frame) :
  execLocal (dropWithinLoop (liftToWithinLoop code >>= next)) f =
  optionBind (execLocal code f) (fun r => execLocal (dropWithinLoop (next (fst r))) (snd r)).
Proof.
 induction code as [value|effect cont IH] in f |- *; [reflexivity|].
 cbn [liftToWithinLoop Action_rect bind dropWithinLoop execLocal].
 destruct (localStep effect f) as [[value after]|]; cbn [optionBind fst snd]; [apply IH|reflexivity].
Qed.
Lemma memo_get_then_exec f :
  execLocal memo_get_then_dispatch f =
  optionBind (execLocal memo_get_call f) (fun r => execLocal after_memo_get (snd r)).
Proof.
 unfold memo_get_then_dispatch, memo_get_call, after_memo_get.
 rewrite exec_drop_lift. destruct (execLocal _ f) as [[[] after]|]; reflexivity.
Qed.
Lemma memo_hit_branch_exact : memo_hit_branch = (memo_hit_pop >>= fun _ => Done _ _ _ KeepGoing).
Proof. reflexivity. Qed.
Definition maximum : Z := 18446744073709551615.
Definition popped (s : @Execution.Machine arrayIndex1 (arrayType _ environment1)) (n : nat) :=
  withMemory s (modifyArray (memory s) arraydef_0__uniformEvalState 0 (Z.of_nat n)).
Theorem generated_memo_hit_pop (f : Frame) n :
 (0 < length (memory (machine f) arraydef_0__uniformEvalState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformEvalState) 0 = Z.of_nat (S n) ->
 Z.of_nat (S n) <= maximum ->
 execLocal memo_hit_pop f = Some (tt,setMachine f (popped (machine f) n)).
Proof.
 destruct f as [s bs ns]. cbn [machine]. intros Hlen Htop Hbound.
 change (@List.nth Z 0 (memory s arraydef_0__uniformEvalState) 0 = Z.of_nat (S n)) in Htop.
 unfold memo_hit_pop. cbn zeta.
 cbv beta iota zeta delta [retrieve store subInt bind
 execLocal localStep step optionBind fst snd nums bools machine setNum setMachine].
 case_decide; [|lia]. rewrite nth_lt_default with (default := 0%Z).
 replace (Z.to_nat 0) with 0%nat by reflexivity. rewrite Htop.
 replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
 assert (Hword : coerceInt (Z.of_nat n) 64 = Z.of_nat n).
 { unfold coerceInt. apply Z.mod_small. unfold maximum in Hbound. lia. }
 rewrite Hword. case_decide; [reflexivity|lia].
Qed.
Lemma popped_stack s n : memory (popped s n) arraydef_0__uniformEvalStack = memory s arraydef_0__uniformEvalStack.
Proof. reflexivity. Qed.
Lemma popped_io s n : stdin (popped s n) = stdin s /\ stdout (popped s n) = stdout s.
Proof. split; reflexivity. Qed.
Lemma popped_other s n name : name <> arraydef_0__uniformEvalState -> memory (popped s n) name = memory s name.
Proof.
 intro H. unfold popped. cbn [withMemory memory]. unfold modifyArray.
 case_decide; [contradiction|reflexivity].
Qed.
Lemma popped_count s n : (0 < length (memory s arraydef_0__uniformEvalState))%nat ->
  List.nth 0 (memory (popped s n) arraydef_0__uniformEvalState) 0 = Z.of_nat n.
Proof.
 intro H. unfold popped. cbn [withMemory memory].
 change (List.nth 0 (<[0%nat := Z.of_nat n]> (memory s arraydef_0__uniformEvalState)) 0 = Z.of_nat n).
 destruct (memory s arraydef_0__uniformEvalState) as [|x xs] eqn:E; cbn in *; [lia|reflexivity].
Qed.
Corollary generated_memo_hit_worklist (f : Frame) n :
 (0 < length (memory (machine f) arraydef_0__uniformEvalState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformEvalState) 0 = Z.of_nat (S n) ->
 Z.of_nat (S n) <= maximum ->
 exists final,
  execLocal memo_hit_pop f = Some (tt,final) /\
  List.nth 0 (memory (machine final) arraydef_0__uniformEvalState) 0 = Z.of_nat n /\
  memory (machine final) arraydef_0__uniformEvalStack = memory (machine f) arraydef_0__uniformEvalStack /\
  (forall name, name <> arraydef_0__uniformEvalState -> memory (machine final) name = memory (machine f) name) /\
  stdin (machine final) = stdin (machine f) /\ stdout (machine final) = stdout (machine f) /\
  nums final = nums f /\ bools final = bools f.
Proof.
 intros Hlen Htop Hbound. exists (setMachine f (popped (machine f) n)).
 split; [now apply generated_memo_hit_pop|].
 cbn [setMachine machine nums bools]. split; [now apply popped_count|].
 split; [apply popped_stack|]. split; [intros; now apply popped_other|].
 destruct (popped_io (machine f) n). repeat split; assumption || reflexivity.
Qed.
Theorem memo_dispatch_selects_hit (f : Frame) count size flag value :
 (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,flag,value) ->
 flag <> 0 -> execLocal memo_hit_dispatch f = execLocal memo_hit_branch f.
Proof.
 destruct f as [s bs ns]. cbn [machine]. intros Hlen Hentry Hflag.
 change (@List.nth (Z*Z*Z*Z)%type 0 (memory s arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,flag,value)) in Hentry.
 unfold memo_hit_dispatch, memo_hit_branch. cbn zeta.
 cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
 retrieve numberLocalGet execLocal localStep step optionBind fst snd nums bools machine].
 case_decide; [|lia]. rewrite nth_lt_default with (default := (0,0,0,0)).
 replace (Z.to_nat 0) with 0%nat by reflexivity. rewrite Hentry.
 rewrite bool_decide_true by exact Hflag. reflexivity.
Qed.
Print Assumptions memo_dispatch_selects_hit.
Theorem after_get_selects_hit (f : Frame) count size flag value :
 (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,flag,value) ->
 flag <> 0 -> execLocal after_memo_get f = execLocal memo_hit_branch f.
Proof.
 destruct f as [s bs ns]. cbn [machine]. intros Hlen Hentry Hflag.
 change (@List.nth (Z*Z*Z*Z)%type 0 (memory s arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,flag,value)) in Hentry.
 unfold after_memo_get, memo_hit_branch. cbn zeta.
 cbv beta iota zeta delta [dropWithinLoop liftToWithinLoop Action_rect bind
 retrieve numberLocalGet execLocal localStep step optionBind fst snd nums bools machine].
 case_decide; [|lia]. rewrite nth_lt_default with (default := (0,0,0,0)).
 replace (Z.to_nat 0) with 0%nat by reflexivity. rewrite Hentry.
 rewrite bool_decide_true by exact Hflag. reflexivity.
Qed.
Theorem generated_memo_hit_branch (f : Frame) n :
 (0 < length (memory (machine f) arraydef_0__uniformEvalState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformEvalState) 0 = Z.of_nat (S n) ->
 Z.of_nat (S n) <= maximum ->
 execLocal memo_hit_branch f = Some (KeepGoing,setMachine f (popped (machine f) n)).
Proof.
 intros Hlen Htop Hbound. rewrite memo_hit_branch_exact, execLocal_bind.
 rewrite (generated_memo_hit_pop f n Hlen Htop Hbound). reflexivity.
Qed.
Print Assumptions generated_memo_hit_branch.
Theorem generated_memo_dispatch_hit (f : Frame) n count size flag value :
 (0 < length (memory (machine f) arraydef_0__uniformMemoState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,flag,value) -> flag <> 0 ->
 (0 < length (memory (machine f) arraydef_0__uniformEvalState))%nat ->
 List.nth 0 (memory (machine f) arraydef_0__uniformEvalState) 0 = Z.of_nat (S n) ->
 Z.of_nat (S n) <= maximum ->
 execLocal memo_hit_dispatch f = Some (KeepGoing,setMachine f (popped (machine f) n)).
Proof.
 intros Hmemo Hentry Hflag Hstack Hcount Hword.
 rewrite (memo_dispatch_selects_hit f count size flag value Hmemo Hentry Hflag).
 now apply generated_memo_hit_branch.
Qed.
Print Assumptions generated_memo_dispatch_hit.
Theorem generated_get_hit (f g : Frame) n count size flag value :
 execLocal memo_get_call f = Some (tt,g) ->
 (0 < length (memory (machine g) arraydef_0__uniformMemoState))%nat ->
 List.nth 0 (memory (machine g) arraydef_0__uniformMemoState) (0,0,0,0) = (count,size,flag,value) -> flag <> 0 ->
 (0 < length (memory (machine g) arraydef_0__uniformEvalState))%nat ->
 List.nth 0 (memory (machine g) arraydef_0__uniformEvalState) 0 = Z.of_nat (S n) ->
 Z.of_nat (S n) <= maximum ->
 execLocal memo_get_then_dispatch f = Some (KeepGoing,setMachine g (popped (machine g) n)).
Proof.
 intros Hget Hmemo Hentry Hflag Hstack Hcount Hword. rewrite memo_get_then_exec, Hget.
 cbn [optionBind fst snd]. rewrite (after_get_selects_hit g count size flag value Hmemo Hentry Hflag).
 now apply generated_memo_hit_branch.
Qed.
Print Assumptions generated_get_hit.
Print Assumptions generated_memo_hit_pop.
Print Assumptions generated_memo_hit_worklist.

Print Assumptions empty_break.
Print Assumptions fatal_break.
End UniformEvalLoop.
