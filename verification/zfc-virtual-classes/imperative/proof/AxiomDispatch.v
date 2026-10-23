From CoqCP Require Import Options Imperative Execution InteractiveExecution.
From ImperativeZFC Require Import ProofChecker.
From NativeProof Require Import Index SipHash ObservedLocal NativePrimitives RenameMemoControl AxiomStructure.
From Stdlib Require Import Lists.List ZArith.ZArith Lia.
From stdpp Require Import numbers list.
Open Scope Z_scope.
Module AxiomDispatch.
Import IndexExecution SipHashExecution ObservedLocal AxiomStructure.
Definition Frame := @Execution.Frame arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom.
Definition tags : list Z := [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17].
Definition handler_for selector : LocalAction unit := match selector with
| 0 => handler_0
| 1 => handler_1
| 2 => handler_2
| 3 => handler_3
| 4 => handler_4
| 5 => handler_5
| 6 => handler_6
| 7 => handler_7
| 8 => handler_8
| 9 => handler_9
| 10 => handler_10
| 11 => handler_11
| 12 => handler_12
| 13 => handler_13
| 14 => handler_14
| 15 => handler_15
| 16 => handler_16
| 17 => handler_17
| _ => Done _ _ _ tt end.
Definition reference_names selector : list varsfuncdef_0__axiom := match selector with
| 0 | 4 => [vardef_0__axiom_p;vardef_0__axiom_q]
| 1 => [vardef_0__axiom_p;vardef_0__axiom_q;vardef_0__axiom_r]
| 2 | 3 | 15 | 16 => [vardef_0__axiom_p]
| _ => [] end.
Definition tag_test selector : LocalAction bool :=
  numberLocalGet _ _ _ vardef_0__axiom_tag >>= fun value =>
    Done _ _ _ selector >>= fun expected => Done _ _ _ (bool_decide (value=expected)).
Definition reference_test name : LocalAction bool :=
  numberLocalGet _ _ _ name >>= fun index =>
    (Done _ _ _ 1 >>= fun slot => retrieve _ _ _ arraydef_0__meta slot) >>= fun count =>
      Done _ _ _ (bool_decide (index<count)).
Fixpoint checked (condition : LocalAction bool) names : LocalAction bool := match names with
| [] => condition
| name::names => checked (shortCircuitAnd condition (reference_test name)) names end.
Definition selector_guard selector : LocalAction bool := match reference_names selector with
| [] => shortCircuitAnd (tag_test selector) (Done _ _ _ true)
| names => checked (tag_test selector) names end.
Definition clause (handlers : Z->LocalAction unit) selector : LocalAction unit :=
  selector_guard selector >>= fun accepted => if accepted then handlers selector else Done _ _ _ tt.
Fixpoint chain (handlers : Z->LocalAction unit) codes : LocalAction unit := match codes with
| [] => Done _ _ _ tt
| selector::codes => clause handlers selector >>= fun _ => chain handlers codes end.
Definition clear_flag : LocalAction unit := ltac:(
  let code := eval unfold funcdef_0__axiom_body in funcdef_0__axiom_body in
  lazymatch code with bind ?initial _ => exact initial end).
Theorem actual_body : funcdef_0__axiom_body=(clear_flag >>= fun _ => chain handler_for tags).
Proof. reflexivity. Qed.


Definition cleared_frame (f:Frame) := setMachine f (store_meta (machine f) 13 0).
Definition references_valid (f:Frame) selector :=
  Forall (fun name=>nums f name<meta_value (machine f) 1) (reference_names selector).
Lemma clear_generated (f:Frame) observations :
  (13<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved clear_flag (f,observations)=Some (tt,(cleared_frame f,observations)).
Proof.
  intro Hmeta. unfold clear_flag,cleared_frame.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>first [exact Hmeta|cbn;exact Hmeta])].
  reflexivity.
Qed.
Lemma tag_evaluates selector (f:Frame) observations :
  execLocalObserved (tag_test selector) (f,observations)=
    Some (bool_decide (nums f vardef_0__axiom_tag=selector),(f,observations)).
Proof. reflexivity. Qed.
Lemma reference_evaluates name (f:Frame) observations :
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (reference_test name) (f,observations)=
    Some (bool_decide (nums f name<meta_value (machine f) 1),(f,observations)).
Proof.
  intro Hmeta. unfold reference_test.
  repeat first [progress cbn [optionBind fst snd]
    |NativePrimitives.primitive ltac:(fun frame name slot=>exact Hmeta)]. reflexivity.
Qed.
Lemma and_false condition right (f:Frame) observations :
  execLocalObserved condition (f,observations)=Some (false,(f,observations)) ->
  execLocalObserved (shortCircuitAnd condition right) (f,observations)=Some (false,(f,observations)).
Proof. intro Hrun. unfold shortCircuitAnd. rewrite local_bind,Hrun. reflexivity. Qed.
Lemma and_true condition right (f:Frame) observations :
  execLocalObserved condition (f,observations)=Some (true,(f,observations)) ->
  execLocalObserved right (f,observations)=Some (true,(f,observations)) ->
  execLocalObserved (shortCircuitAnd condition right) (f,observations)=Some (true,(f,observations)).
Proof. intros Hleft Hright. unfold shortCircuitAnd. rewrite local_bind,Hleft. exact Hright. Qed.
Lemma checked_false condition names (f:Frame) observations :
  execLocalObserved condition (f,observations)=Some (false,(f,observations)) ->
  execLocalObserved (checked condition names) (f,observations)=Some (false,(f,observations)).
Proof.
  intro Hcondition. induction names as [|name names IH] in condition,Hcondition|-*; [exact Hcondition|].
  cbn [checked]. apply IH. now apply and_false.
Qed.
Lemma checked_true condition names (f:Frame) observations :
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  Forall (fun name=>nums f name<meta_value (machine f) 1) names ->
  execLocalObserved condition (f,observations)=Some (true,(f,observations)) ->
  execLocalObserved (checked condition names) (f,observations)=Some (true,(f,observations)).
Proof.
  intros Hmeta Hnames Hcondition. induction Hnames as [|name names Hvalid Hnames IH] in condition,Hcondition|-*;
    [exact Hcondition|]. cbn [checked]. apply IH. apply and_true; [exact Hcondition|].
  rewrite reference_evaluates by exact Hmeta. rewrite bool_decide_true by exact Hvalid. reflexivity.
Qed.
Lemma guard_false selector current (f:Frame) observations :
  nums f vardef_0__axiom_tag=current -> current<>selector ->
  execLocalObserved (selector_guard selector) (f,observations)=Some (false,(f,observations)).
Proof.
  intros Htag Hneq. assert (Htest:execLocalObserved (tag_test selector) (f,observations)=Some (false,(f,observations))).
  { rewrite tag_evaluates,Htag,bool_decide_false by exact Hneq. reflexivity. }
  unfold selector_guard. destruct (reference_names selector) as [|name names];
    [now apply and_false|now apply checked_false].
Qed.
Lemma guard_true selector (f:Frame) observations :
  nums f vardef_0__axiom_tag=selector -> references_valid f selector ->
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (selector_guard selector) (f,observations)=Some (true,(f,observations)).
Proof.
  intros Htag Hrefs Hmeta.
  assert (Htest:execLocalObserved (tag_test selector) (f,observations)=Some (true,(f,observations))).
  { rewrite tag_evaluates,Htag,bool_decide_true by reflexivity. reflexivity. }
  unfold selector_guard. unfold references_valid in Hrefs.
  destruct (reference_names selector) as [|name names]; [apply and_true;[exact Htest|reflexivity]|].
  now apply checked_true.
Qed.
Lemma clause_skip handlers selector current (f:Frame) observations :
  nums f vardef_0__axiom_tag=current -> current<>selector ->
  execLocalObserved (clause handlers selector) (f,observations)=Some (tt,(f,observations)).
Proof.
  intros Htag Hneq. unfold clause. rewrite local_bind,(guard_false selector current f observations Htag Hneq). reflexivity.
Qed.
Lemma clause_take handlers selector (f:Frame) observations :
  nums f vardef_0__axiom_tag=selector -> references_valid f selector ->
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  execLocalObserved (clause handlers selector) (f,observations)=execLocalObserved (handlers selector) (f,observations).
Proof.
  intros Htag Hrefs Hmeta. unfold clause. rewrite local_bind,(guard_true selector f observations Htag Hrefs Hmeta). reflexivity.
Qed.
Lemma chain_skips handlers codes current (f:Frame) observations :
  nums f vardef_0__axiom_tag=current -> Forall (fun selector=>current<>selector) codes ->
  execLocalObserved (chain handlers codes) (f,observations)=Some (tt,(f,observations)).
Proof.
  intros Htag Hcodes. induction Hcodes as [|selector codes Hneq Hcodes IH]; [reflexivity|].
  cbn [chain]. rewrite local_bind,(clause_skip handlers selector current f observations Htag Hneq). exact IH.
Qed.
Lemma chain_active handlers prefix suffix selector (f after:Frame) observations trace :
  nums f vardef_0__axiom_tag=selector -> references_valid f selector ->
  (1<length (memory (machine f) arraydef_0__meta))%nat ->
  Forall (fun other=>selector<>other) prefix -> Forall (fun other=>selector<>other) suffix ->
  nums after vardef_0__axiom_tag=selector ->
  execLocalObserved (handlers selector) (f,observations)=Some (tt,(after,trace)) ->
  execLocalObserved (chain handlers (prefix++selector::suffix)) (f,observations)=Some (tt,(after,trace)).
Proof.
  intros Htag Hrefs Hmeta Hprefix Hsuffix Hafter Hbody.
  induction Hprefix as [|other prefix Hneq Hprefix IH].
  - cbn [app chain]. rewrite local_bind,(clause_take handlers selector f observations Htag Hrefs Hmeta),Hbody.
    cbn [optionBind fst snd]. now apply (chain_skips handlers suffix selector).
  - cbn [app chain]. rewrite local_bind,(clause_skip handlers other selector f observations Htag Hneq).
    exact IH.
Qed.
Lemma tags_nodup : NoDup tags.
Proof. change (NoDup (seqZ 0 18)). apply NoDup_seqZ. Qed.
Lemma supported_member selector : 0<=selector<=17 -> selector ∈ tags.
Proof. intro Hrange. change (selector ∈ seqZ 0 18). rewrite elem_of_seqZ. lia. Qed.
Theorem chain_supported handlers selector (f after:Frame) observations trace :
  0<=selector<=17 -> nums f vardef_0__axiom_tag=selector -> references_valid f selector ->
  (1<length (memory (machine f) arraydef_0__meta))%nat -> nums after vardef_0__axiom_tag=selector ->
  execLocalObserved (handlers selector) (f,observations)=Some (tt,(after,trace)) ->
  execLocalObserved (chain handlers tags) (f,observations)=Some (tt,(after,trace)).
Proof.
  intros Hrange Htag Hrefs Hmeta Hafter Hbody.
  destruct (list_elem_of_split tags selector (supported_member selector Hrange)) as [prefix [suffix Hsplit]].
  pose proof tags_nodup as Hnodup. rewrite Hsplit in Hnodup|-*.
  apply NoDup_app in Hnodup as [Hprefix [Hcross Hsuffix]]. apply NoDup_cons in Hsuffix as [Hnot Hsuffix].
  eapply chain_active; try eassumption.
  - apply Forall_forall. intros other Hother Heq. subst other. apply (Hcross selector Hother). apply elem_of_cons. left. reflexivity.
  - apply Forall_forall. intros other Hother Heq. apply Hnot. now rewrite Heq.
Qed.
Theorem generated_body selector (f after:Frame) observations trace :
  0<=selector<=17 -> nums f vardef_0__axiom_tag=selector -> references_valid f selector ->
  (13<length (memory (machine f) arraydef_0__meta))%nat -> nums after vardef_0__axiom_tag=selector ->
  execLocalObserved (handler_for selector) (cleared_frame f,observations)=Some (tt,(after,trace)) ->
  execLocalObserved funcdef_0__axiom_body (f,observations)=Some (tt,(after,trace)).
Proof.
  intros Hrange Htag Hrefs Hmeta Hafter Hbody.
  rewrite actual_body,local_bind,(clear_generated f observations Hmeta). cbn [optionBind fst snd].
  apply (chain_supported handler_for selector (cleared_frame f) after observations trace Hrange).
  - exact Htag.
  - unfold references_valid,cleared_frame in *. cbn [machine setMachine nums].
    rewrite meta_store_other by lia. exact Hrefs.
  - unfold cleared_frame. cbn [machine setMachine]. rewrite store_meta_length. lia.
  - exact Hafter.
  - exact Hbody.
Qed.
Theorem generated_helper s bs ns selector after observations trace :
  0<=selector<=17 -> ns vardef_0__axiom_tag=selector ->
  references_valid {|machine:=s;bools:=bs;nums:=ns|} selector ->
  (13<length (memory s arraydef_0__meta))%nat -> nums after vardef_0__axiom_tag=selector ->
  execLocalObserved (handler_for selector) (cleared_frame {|machine:=s;bools:=bs;nums:=ns|},observations)=Some (tt,(after,trace)) ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(machine after,trace)).
Proof.
  intros Hrange Htag Hrefs Hmeta Hafter Hbody. unfold IndexExecution.Machine in *. unfold funcdef_0__axiom. rewrite eliminate_correct.
  pose proof (generated_body selector {|machine:=s;bools:=bs;nums:=ns|} after observations trace Hrange Htag Hrefs Hmeta Hafter Hbody) as Hrun.
  exact (f_equal (fun response=>optionBind response (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))) Hrun).
Qed.


Definition tag_safe (effect : WithLocalVariables arrayIndex1 (arrayType _ environment1) varsfuncdef_0__axiom) :=
  match effect with NumberLocalSet _ _ _ name _ => name<>vardef_0__axiom_tag | _ => True end.
Fixpoint tag_ro {R} (code:LocalAction R) : Prop := match code with
| Done _ _ _ _ => True
| Dispatch _ _ _ effect next => tag_safe effect /\ forall response,tag_ro (next response) end.
Lemma tag_ro_bind {A B} (code:LocalAction A) (next:A->LocalAction B) :
  tag_ro code -> (forall response,tag_ro (next response)) -> tag_ro (code>>=next).
Proof.
  induction code as [value|effect cont IH];cbn [tag_ro bind];intros Hcode Hnext;[apply Hnext|].
  destruct Hcode as [Hsafe Hcode]. split;[exact Hsafe|]. intro response. apply IH;[apply Hcode|exact Hnext].
Qed.
Lemma tag_ro_lift {R} (code:Action (WithArrays arrayIndex1 (arrayType _ environment1)) withArraysReturnValue R) :
  tag_ro (liftToWithLocalVariables code).
Proof.
  induction code as [value|effect cont IH];cbn [liftToWithLocalVariables Action_rect tag_ro tag_safe];[exact I|].
  split;[exact I|exact IH].
Qed.
Lemma tag_step_preserves effect (f after:Frame) observations trace response :
  tag_safe effect -> localStepObserved effect (f,observations)=Some (response,(after,trace)) ->
  nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  intros Hsafe Hrun. destruct effect as [effect|name|name value|name|name value];cbn [tag_safe localStepObserved fst snd] in *.
  - destruct (observedStep effect (machine f,observations)) as [[answer [next seen]]|] eqn:Hstep;[|discriminate].
    cbn [optionBind fst snd] in Hrun. injection Hrun as <- <- <-. reflexivity.
  - injection Hrun as <- <- <-. reflexivity.
  - injection Hrun as <- <- <-. reflexivity.
  - injection Hrun as <- <- <-. reflexivity.
  - injection Hrun as <- <- <-. cbn [nums setNum]. unfold Imperative.update. case_decide;[congruence|reflexivity].
Qed.
Theorem tag_preserves {R} (code:LocalAction R) (f after:Frame) observations trace response :
  tag_ro code -> execLocalObserved code (f,observations)=Some (response,(after,trace)) ->
  nums after vardef_0__axiom_tag=nums f vardef_0__axiom_tag.
Proof.
  induction code as [value|effect cont IH] in f,after,observations,trace,response|-*.
  - cbn [execLocalObserved]. intros Hsafe Hrun. injection Hrun as <- <- <-. reflexivity.
  - cbn [tag_ro execLocalObserved]. intros [Hsafe Hnext] Hrun.
    destruct (localStepObserved effect (f,observations)) as [[answer [next seen]]|] eqn:Hstep;[|discriminate].
    cbn [optionBind fst snd] in Hrun. rewrite (IH answer next after seen trace response (Hnext answer) Hrun).
    exact (tag_step_preserves effect f next observations seen answer Hsafe Hstep).
Qed.
Ltac tag_readonly := first
  [lazymatch goal with |- tag_ro (Done _ _ _ _) => exact I end
  |lazymatch goal with |- tag_ro (bind _ _) => apply tag_ro_bind;[tag_readonly|intro;tag_readonly] end
  |lazymatch goal with |- tag_ro (liftToWithLocalVariables _) => apply tag_ro_lift end
  |lazymatch goal with |- tag_ro (if ?condition then _ else _) => destruct condition;tag_readonly end
  |lazymatch goal with |- tag_ro (Dispatch _ _ _ _ _) => split;[cbn [tag_safe];first[exact I|discriminate]|intro;tag_readonly] end
  |progress cbv beta iota zeta delta [numberLocalGet numberLocalSet booleanLocalGet booleanLocalSet
    retrieve store shortCircuitAnd shortCircuitOr];tag_readonly].
Theorem handler_tag_ro selector : tag_ro (handler_for selector).
Proof.
  unfold handler_for. repeat case_match.
  all: unfold handler_0,handler_1,handler_2,handler_3,handler_4,handler_5,handler_6,handler_7,handler_8,
    handler_9,handler_10,handler_11,handler_12,handler_13,handler_14,handler_15,handler_16,handler_17.
  all: tag_readonly.
Qed.
Theorem generated_projected s bs ns selector final observations trace :
  0<=selector<=17 -> ns vardef_0__axiom_tag=selector ->
  references_valid {|machine:=s;bools:=bs;nums:=ns|} selector ->
  (13<length (memory s arraydef_0__meta))%nat ->
  optionBind (execLocalObserved (handler_for selector)
    (cleared_frame {|machine:=s;bools:=bs;nums:=ns|},observations))
    (fun r=>Some (fst r,(machine (fst (snd r)),snd (snd r))))=Some (tt,(final,trace)) ->
  execObserved (funcdef_0__axiom bs ns) (s,observations)=Some (tt,(final,trace)).
Proof.
  intros Hrange Htag Hrefs Hmeta Hhandler.
  destruct (execLocalObserved (handler_for selector)
    (cleared_frame {|machine:=s;bools:=bs;nums:=ns|},observations)) as [[[] [after seen]]|] eqn:Hrun;[|discriminate].
  cbn [optionBind fst snd] in Hhandler. injection Hhandler as <- <-.
  eapply generated_helper;try eassumption.
  rewrite (tag_preserves _ _ _ _ _ _ (handler_tag_ro selector) Hrun). exact Htag.
Qed.
End AxiomDispatch.
